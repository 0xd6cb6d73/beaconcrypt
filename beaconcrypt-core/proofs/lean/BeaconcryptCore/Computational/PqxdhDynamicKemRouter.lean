import BeaconcryptCore.Computational.PqxdhLiveKemSelection
import BeaconcryptCore.Computational.PqxdhLiveKemOwnership

/-!
The executable dynamic KEM router holds a public selected key and locally generated other keys. Creation activates exactly one reserved slot. An uncreated handle rejects before the selected-reveal freshness stop. A successful selected-key reveal stops the whole continuation; it is never answered with a fabricated secret or ordinary rejection. Prechallenge decapsulation forwards the selected slot to the ordinary unblocked CCA oracle. Source comparisons alone reattach the selected secret.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemRouter
open PqxdhKemIndCca PqxdhPrivateKemSource
open PqxdhLiveKemBirth (PoolSpec Query Observation Pool)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

abbrev Slot (KemSK : Type) := MlKem768PublicKey × Option KemSK
abbrev Reservation (KemSK : Type) := Nat → Option (Slot KemSK)

/-- This state requires no selected-secret field or argument. The intended empty initialization records actual returned values; arbitrary supplied histories and byte aliases are not excluded by the type. The two stop reasons remain explicit. -/
structure State (KemSK : Type) where
  created : Nat
  history : List (Observation KemSK)
  forbiddenReveal : Bool
  exhausted : Bool

def empty : State KemSK := ⟨0, [], false, false⟩

def record (query : Query) (reply : (PoolSpec KemSK).Range query) (state : State KemSK) : State KemSK :=
  { state with history := state.history ++ [⟨query, reply⟩] }

/-- A private reservation is not a creation: future slots are inaccessible. -/
def lookup (reservation : Reservation KemSK) (state : State KemSK) (index : Nat) : Option (Slot KemSK) :=
  if index < state.created then reservation index else none

/-- Only the source comparison knows the selected secret. Its redacted reservation retains public-key aliases without confusing their creation indices. -/
def redact (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) : Reservation KemSK :=
  fun index => (pairs[index]?).map fun pair => (pair.1, if index = selected then none else some pair.2)

/-- This local step may stop at the explicit creation cap or a successful selected reveal. Every missing reveal returns `some none`, so it is an ordinary source rejection and the client continues. -/
def router
    (decapsulation : Reservation KemSK → Nat → MlKem768Ciphertext →
      OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret))
    (selected : Nat) (reservation : Reservation KemSK) :
    QueryImpl (PoolSpec KemSK) (OptionT (StateT (State KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)))) :=
  fun query => OptionT.mk fun state => match query with
  | .create => match reservation state.created with
    | none => pure (none, { state with exhausted := true })
    | some pair =>
      let reply := (state.created, pair.1)
      pure (some reply, record .create reply { state with created := state.created + 1 })
  | .decapsulate index ciphertext => do
    let reply ← decapsulation (lookup reservation state) index ciphertext
    pure (some reply, record (.decapsulate index ciphertext) reply state)
  | .reveal index => match lookup reservation state index with
    | none => pure (some none, record (.reveal index) none state)
    | some pair => if index = selected then pure (none, { state with forbiddenReveal := true })
      else pure (some pair.2, record (.reveal index) pair.2 state)

/-- The prechallenge selected oracle is unrestricted. Other keys are evaluated locally with their own exact optional replies. -/
def pre (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK) :=
  router (fun keys index ciphertext => PqxdhLiveKemRouting.pre kem selected keys (default, index) ciphertext)
    selected reservation

/-- A source-internal postchallenge request at the exact selected ciphertext uses the challenger-provided candidate. Every other selected ciphertext is forwarded; other owners retain actual local outputs even under byte aliases. -/
noncomputable def postDecapsulation (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (keys : Reservation KemSK) (index : Nat) (ciphertext : MlKem768Ciphertext) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret) :=
  match keys index with
  | none => pure none
  | some pair => if index = selected then
      if ciphertext = challenge then pure (some candidate)
      else (MlKemCCAOracleSpec baseSpec).query (.inr ciphertext)
    else match pair.2 with
      | none => pure none
      | some secret => ccaAmbient (kem.decaps secret ciphertext)

/-- Creation and reveal freshness use precisely the same dynamic state before and after the challenge. The candidate is internal reduction input returned to this source client on the selected exact-ciphertext request. Its nonexposure through the later network boundary is a separate consuming obligation. -/
noncomputable def post (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :=
  router (postDecapsulation kem selected challenge candidate) selected reservation

/-- Source interpretation has the actual reserved pairs, but stops before the same forbidden disclosure. Its decapsulation uses the exact private indexed key, including ordinary ML-KEM fallback replies. -/
def source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) :
    QueryImpl (PoolSpec KemSK) (OptionT (StateT (State KemSK) ProbComp)) :=
  fun query => OptionT.mk fun state => match query with
  | .create => match pairs[state.created]? with
    | none => pure (none, { state with exhausted := true })
    | some pair =>
      let reply := (state.created, pair.1)
      pure (some reply, record .create reply { state with created := state.created + 1 })
  | .decapsulate index ciphertext => do
    let reply ← match (pairs.take state.created)[index]? with
      | none => pure none
      | some pair => simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.decaps pair.2 ciphertext)
    pure (some reply, record (.decapsulate index ciphertext) reply state)
  | .reveal index => match (pairs.take state.created)[index]? with
    | none => pure (some none, record (.reveal index) none state)
    | some pair => if index = selected then pure (none, { state with forbiddenReveal := true })
      else pure (some (some pair.2), record (.reveal index) (some pair.2) state)

/-- The real created pool is reconstructed only inside the proof, retaining the exact observed history. -/
def sourcePool (pairs : List (MlKem768PublicKey × KemSK)) (state : State KemSK) : Pool KemSK :=
  ⟨pairs.take state.created, state.history⟩

set_option backward.isDefEq.respectTransparency false in
/-- Missing or not-yet-created handles do not stop freshness, including a guess of the future selected index. -/
theorem missing_reveal (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK) (state : State KemSK) (index : Nat)
    (missing : lookup reservation state index = none) :
    ((pre kem selected reservation (.reveal index)).run).run state =
      pure (some none, record (.reveal index) none state) := by
  simp only [pre, router, OptionT.run_mk, StateT.run, missing]

set_option backward.isDefEq.respectTransparency false in
/-- A real selected reveal stops before producing the unavailable secret; the attempted disclosure is retained explicitly as a stop reason. -/
theorem selected_reveal (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : Reservation KemSK) (state : State KemSK) (pair : Slot KemSK)
    (present : lookup reservation state selected = some pair) :
    ((pre kem selected reservation (.reveal selected)).run).run state =
      pure (none, { state with forbiddenReveal := true }) := by
  simp [pre, router, OptionT.run_mk, StateT.run, present]

/-- The dynamic table exposes precisely the already-created redacted prefix, not the reserved future. -/
theorem lookup_redact (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (state : State KemSK) :
    lookup (redact selected pairs) state = PqxdhLiveKemRouting.redact selected (sourcePool pairs state) := by
  funext index
  by_cases earlier : index < state.created
  · simp [lookup, redact, PqxdhLiveKemRouting.redact, sourcePool, earlier]
  · simp [lookup, PqxdhLiveKemRouting.redact, sourcePool, earlier]

set_option backward.isDefEq.respectTransparency false in
/-- Interpreting just the selected decapsulation oracle recovers the exact dynamic source callback, including created count, full reply history and both stop reasons. -/
theorem step_source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (target, secret))
    (query : Query) (state : State KemSK) :
    evalKem baseImpl kem secret (((pre kem selected (redact selected pairs) query).run).run state) =
      (((source baseImpl kem selected pairs query).run).run state) := by
  cases query with
  | create =>
      cases found : pairs[state.created]? <;>
        simp [pre, router, source, redact, found, evalKem, StateT.run]
  | reveal index =>
      by_cases earlier : index < state.created
      · cases found : pairs[index]? with
        | none => simp [pre, router, source, lookup, redact, earlier, found, evalKem, StateT.run]
        | some pair =>
            by_cases chosen : index = selected
            · subst index
              simp [pre, router, source, lookup, redact, earlier, found, evalKem, StateT.run]
            · simp [pre, router, source, lookup, redact, earlier, found, chosen, evalKem, StateT.run]
      · simp [pre, router, source, lookup, earlier, evalKem, StateT.run]
  | decapsulate index ciphertext =>
      simp only [pre, router, source, OptionT.run_mk, StateT.run, bind_pure_comp, evalKem, simulateQ_map]
      by_cases earlier : index < state.created
      · cases found : pairs[index]? with
        | none => simp [PqxdhLiveKemRouting.pre, lookup, redact, earlier, found]
        | some pair =>
          by_cases chosen : index = selected
          · subst index
            have pairEq : pair = (target, secret) := Option.some.inj (found.symm.trans present)
            subst pair
            simp [PqxdhLiveKemRouting.pre, lookup, redact, earlier, present,
              PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl, KEMScheme.IND_CCA_preChallengeImpl]
            rfl
          · simp only [PqxdhLiveKemRouting.pre, lookup, ite_eq_left earlier, redact, found,
              Option.map_some, ite_eq_right chosen]
            rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
              (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl kem secret)
                (ccaAmbient (kem.decaps pair.2 ciphertext))) =
                simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.decaps pair.2 ciphertext)
              from PqxdhPrivateKemSource.evalKem_ambient baseImpl kem secret _]
            simp [earlier, found]
      · simp [PqxdhLiveKemRouting.pre, lookup, earlier]

set_option backward.isDefEq.respectTransparency false in
/-- Every adaptive creation/decapsulation/reveal program has the same complete stopped source result, including its true optional output, history, activated prefix and stop reasons. No selected secret is an argument of the executable program. -/
theorem program_source {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (target, secret))
    (client : OracleComp (PoolSpec KemSK) Result) (state : State KemSK) :
    evalKem baseImpl kem secret (((simulateQ (pre kem selected (redact selected pairs)) client).run).run state) =
      (((simulateQ (source baseImpl kem selected pairs) client).run).run state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
      change evalKem baseImpl kem secret
        (((pre kem selected (redact selected pairs) query).run).run state >>= fun result =>
          (result.1.elim (pure none) (fun value => (simulateQ (pre kem selected (redact selected pairs)) (next value)).run)).run result.2) = _
      unfold evalKem
      simp only [simulateQ_bind]
      rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl kem secret)
          (((pre kem selected (redact selected pairs) query).run).run state)) =
            (((source baseImpl kem selected pairs query).run).run state)
        from step_source baseImpl kem selected pairs target secret present query state]
      apply bind_congr
      rintro ⟨none | reply, after⟩
      · rfl
      · exact ih reply after

/-- The explicit source reservation starts with the real empty private pool and no caller-supplied secret-bearing history. -/
theorem empty_source_pool (pairs : List (MlKem768PublicKey × KemSK)) :
    sourcePool pairs (empty : State KemSK) = PqxdhLiveKemBirth.empty := rfl

/-- All future reservation slots reject before their actual creation, even when the selected ordinal is already known to the client. -/
theorem future_missing (reservation : Reservation KemSK) (state : State KemSK) (index : Nat)
    (future : state.created ≤ index) : lookup reservation state index = none := by
  simp only [lookup, ite_eq_right (Nat.not_lt.mpr future)]

/-- An executable finite reservation needs only the challenger public key and the independently sampled local pairs. -/
def selectedReservation {count : Nat} (target : Fin (count + 1)) (publicKey : MlKem768PublicKey)
    (others : Fin count → MlKem768PublicKey × KemSK) : Reservation KemSK :=
  fun index => (List.ofFn (target.insertNth (publicKey, none)
    (fun index => ((others index).1, some (others index).2))))[index]?

/-- Removing the selected secret from the actual ordered reservation is exactly the executable public-key-only construction. This is equality of the entire indexed table, not of marginal key distributions. -/
theorem selected_reservation {count : Nat} (target : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK) :
    redact target.val (List.ofFn (target.insertNth chosen others)) = selectedReservation target chosen.1 others := by
  funext index
  by_cases valid : index < count + 1
  · obtain equal | ⟨other, equal⟩ := Fin.eq_self_or_eq_succAbove target (⟨index, valid⟩ : Fin (count + 1))
    · have atTarget : index = target.val := congrArg Fin.val equal
      subst index
      simp only [redact, selectedReservation, List.getElem?_ofFn, target.isLt, _root_.dite_true, Fin.eta, Fin.insertNth_apply_same, ite_true, Option.map_some]
    · have atOther : index = (target.succAbove other).val := congrArg Fin.val equal
      subst index
      have different : (target.succAbove other).val ≠ target.val := fun same =>
        Fin.succAbove_ne target other (Fin.ext same)
      simp only [redact, selectedReservation, List.getElem?_ofFn, (target.succAbove other).isLt, _root_.dite_true, Fin.eta, Fin.insertNth_apply_succAbove, ite_eq_right different, Option.map_some]
  · simp [redact, selectedReservation, valid]

end BeaconcryptCore.Computational.PqxdhDynamicKemRouter

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemRouter.missing_reveal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemRouter.missing_reveal
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemRouter.selected_reveal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemRouter.selected_reveal
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemRouter.lookup_redact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemRouter.lookup_redact
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemRouter.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemRouter.step_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemRouter.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemRouter.program_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemRouter.empty_source_pool' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemRouter.empty_source_pool
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemRouter.future_missing' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemRouter.future_missing
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemRouter.selected_reservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemRouter.selected_reservation
