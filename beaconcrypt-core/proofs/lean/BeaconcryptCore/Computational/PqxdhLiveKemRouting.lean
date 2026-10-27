import BeaconcryptCore.Computational.PqxdhLiveKemBirth
import BeaconcryptCore.Computational.PqxdhPhase2PreChallenge
import BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting

/-!
A selected live KEM is routed by its actual creation index. Every other indexed key remains local even when public key or shared-secret bytes coincide. The private table supplied to the ordinary client has no selected secret. The complete prechallenge comparison and postchallenge origin classification keep missing-handle rejection and all actual optional replies. The complete prechallenge equation concerns fixed existing slots. Its earlier history is retained as an explicit input; constructing that history without a prohibited selected-key reveal remains a required source-prefix obligation. Dynamic selected generation, prohibited-reveal stopping and global selection losses remain consuming work.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveKemRouting
open PqxdhKemIndCca PqxdhPrivateKemSource PqxdhStatefulPhase1EufCma
open PqxdhInitializerSecrecy (kemAmbientImpl)
open PqxdhPhase2DecapsulationRouting (Shared ordinaryDecapsulate)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

abbrev Handle := MlKem768PublicKey × Nat
abbrev PrivateKeys (KemSK : Type) := Nat → Option (MlKem768PublicKey × Option KemSK)

/-- The source-to-interpreter relation discards exactly the designated creation slot's secret. -/
def redact (selected : Nat) (pool : PqxdhLiveKemBirth.Pool KemSK) : PrivateKeys KemSK := fun index =>
  (pool.keys[index]?).map fun pair => (pair.1, if index = selected then none else some pair.2)

/-- Public bytes never select the challenge slot. -/
def encode (selected : Nat) (handle : Handle) : Option Handle :=
  if handle.2 = selected then none else some handle

def Known (pool : PqxdhLiveKemBirth.Pool KemSK) (handle : Handle) : Prop :=
  ∃ secret, pool.keys[handle.2]? = some (handle.1, secret)

/-- Only an actually created selected handle forwards to the CCA oracle; all other present keys are locally interpreted. -/
def pre (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (handle : Handle) (ciphertext : MlKem768Ciphertext) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret) :=
  match keys handle.2 with
  | none => pure none
  | some pair =>
    if handle.2 = selected then (MlKemCCAOracleSpec baseSpec).query (.inr ciphertext)
    else match pair.2 with
    | none => pure none
    | some secret => ccaAmbient (kem.decaps secret ciphertext)

/-- Native typed postchallenge use recognizes only the selected owner's challenge ciphertext. Other owners' actual decapsulation outputs stay known values, including byte aliases. -/
noncomputable def post (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (challenge : MlKem768Ciphertext)
    (handle : Handle) (ciphertext : MlKem768Ciphertext) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Option Shared) :=
  match keys handle.2 with
  | none => pure none
  | some pair =>
    if handle.2 = selected then ordinaryDecapsulate challenge ciphertext
    else match pair.2 with
    | none => pure none
    | some secret => Option.map Shared.known <$> ccaAmbient (kem.decaps secret ciphertext)

set_option backward.isDefEq.respectTransparency false in
/-- Interpreting the designated secret only inside the ordinary CCA interpreter gives the exact indexed native optional decapsulation reply. -/
theorem pre_source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat)
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (handle : Handle) (ciphertext : MlKem768Ciphertext) :
    evalKem baseImpl kem secret (pre kem selected (redact selected pool) handle ciphertext) =
      Prod.fst <$> (PqxdhLiveKemBirth.poolImpl baseImpl kem (.decapsulate handle.2 ciphertext)).run pool := by
  by_cases same : handle.2 = selected
  · have lookup : pool.keys[handle.2]? = some (target, secret) := by simpa only [same] using present
    rw [PqxdhLiveKemBirth.decapsulate_present baseImpl kem pool handle.2 (target, secret) lookup]
    simp [pre, redact, same, present, evalKem, localKemPreChallengeImpl, KEMScheme.IND_CCA_preChallengeImpl]
    rfl
  · cases found : pool.keys[handle.2]? with
    | none =>
      rw [PqxdhLiveKemBirth.decapsulate_missing baseImpl kem pool handle.2 found]
      simp only [pre, redact, found, Option.map_none, evalKem, simulateQ_pure, map_pure]
    | some pair =>
      simp only [pre, redact, found, Option.map_some, ite_eq_right same, evalKem_ambient,
        PqxdhLiveKemBirth.decapsulate_present baseImpl kem pool handle.2 pair found ciphertext,
        bind_pure_comp, Functor.map_map]
      simp

/-- Redaction exposes the selected public key and no selected secret. -/
theorem selected_redacted (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat)
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret)) :
    redact selected pool selected = some (target, none) := by
  simp [redact, present]

/-- Every other creation retains its full actual private pair, without testing public bytes or private-key equality. -/
theorem other_redacted (pool : PqxdhLiveKemBirth.Pool KemSK) (selected index : Nat)
    (other : index ≠ selected) :
    redact selected pool index = (pool.keys[index]?).map (fun pair => (pair.1, some pair.2)) := by
  simp only [redact, ite_eq_right other]

/-- A local decapsulation reply cannot acquire the selected-origin tag even if its bytes equal the challenge secret. -/
theorem known_not_challenge (reply : Option MlKemSharedSecret) :
    Option.map Shared.known reply ≠ some Shared.challenge := by
  cases reply <;> simp

/-- Every actual selected-origin reply comes from the designated created slot and its exact challenge ciphertext. This is provenance, not a claim that other owners' output bytes cannot coincide. -/
theorem post_origin (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (challenge : MlKem768Ciphertext)
    (handle : Handle) (ciphertext : MlKem768Ciphertext)
    (actual : some Shared.challenge ∈ support (post kem selected keys challenge handle ciphertext)) :
    handle.2 = selected ∧ ciphertext = challenge ∧ ∃ pair, keys handle.2 = some pair := by
  classical
  cases found : keys handle.2 with
  | none => simp [post, found] at actual
  | some pair =>
    by_cases owner : handle.2 = selected
    · by_cases same : ciphertext = challenge
      · exact ⟨owner, same, pair, rfl⟩
      · have atSelected : keys selected = some pair := by simpa only [owner] using found
        simp [post, owner, atSelected, ordinaryDecapsulate, same] at actual
    · cases secret : pair.2 <;> simp [post, found, owner, secret] at actual

set_option backward.isDefEq.respectTransparency false in
/-- Reattaching the exact attempt history gives the full native decapsulation poststate, including every rejected reply. -/
theorem pre_source_state (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat)
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (handle : Handle) (ciphertext : MlKem768Ciphertext) :
    (fun reply => (reply, PqxdhLiveKemBirth.record (.decapsulate handle.2 ciphertext) reply pool)) <$>
      evalKem baseImpl kem secret (pre kem selected (redact selected pool) handle ciphertext) =
      (PqxdhLiveKemBirth.poolImpl baseImpl kem (.decapsulate handle.2 ciphertext)).run pool := by
  rw [pre_source baseImpl kem pool selected target secret present]
  cases found : pool.keys[handle.2]? with
  | none =>
      rw [PqxdhLiveKemBirth.decapsulate_missing baseImpl kem pool handle.2 found]
      simp
  | some pair =>
      rw [PqxdhLiveKemBirth.decapsulate_present baseImpl kem pool handle.2 pair found]
      simp only [bind_pure_comp, Functor.map_map]

abbrev DecapSpec : OracleSpec (Handle × MlKem768Ciphertext) := fun _ => Option MlKemSharedSecret

/-- The executable source callback retains every decapsulation attempt, including rejected replies, while the selected secret stays outside its state. -/
def preImpl (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) :
    QueryImpl DecapSpec (StateT (List (PqxdhLiveKemBirth.Observation KemSK)) (OracleComp (MlKemCCAOracleSpec baseSpec))) :=
  fun query history => do
    let reply ← pre kem selected keys query.1 query.2
    pure (reply, history ++ [⟨.decapsulate query.1.2 query.2, reply⟩])

/-- The original indexed source service with the exact same ciphertext and retained private pool. -/
def nativeImpl (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) :
    QueryImpl DecapSpec (StateT (PqxdhLiveKemBirth.Pool KemSK) ProbComp) :=
  fun query => PqxdhLiveKemBirth.poolImpl baseImpl kem (.decapsulate query.1.2 query.2)

/-- Reconstruct private interpreter state only for the source comparison, never as an executable reduction reply. -/
def pack (keys : List (MlKem768PublicKey × KemSK)) (history : List (PqxdhLiveKemBirth.Observation KemSK)) :
    PqxdhLiveKemBirth.Pool KemSK := ⟨keys, history⟩

set_option backward.isDefEq.respectTransparency false in
/-- One complete source callback and its recorded reduction have identical private poststate after interpretation. -/
theorem pre_step (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat)
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret)) (query : DecapSpec.Domain) :
    (fun result => (result.1, pack pool.keys result.2)) <$>
      evalKem baseImpl kem secret ((preImpl kem selected (redact selected pool) query).run pool.transcript) =
      (nativeImpl baseImpl kem query).run pool := by
  simpa only [preImpl, StateT.run, bind_pure_comp, evalKem, simulateQ_map, Functor.map_map,
    pack, PqxdhLiveKemBirth.record, nativeImpl, DecapSpec, PqxdhLiveKemBirth.Range] using
    pre_source_state baseImpl kem pool selected target secret present query.1 query.2

/-- Only the ordinary interpreter receives the selected private key; its executable client remains unchanged. -/
def evaluatedPre (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (selected : Nat) (keys : PrivateKeys KemSK) :
    QueryImpl DecapSpec (StateT (List (PqxdhLiveKemBirth.Observation KemSK)) ProbComp) :=
  fun query history => evalKem baseImpl kem secret ((preImpl kem selected keys query).run history)

/-- Every adaptive decapsulation program has the same complete reply/history under the ordinary interpreter. -/
theorem pre_interpreted {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (selected : Nat) (keys : PrivateKeys KemSK) (client : OracleComp DecapSpec Result)
    (history : List (PqxdhLiveKemBirth.Observation KemSK)) :
    evalKem baseImpl kem secret ((simulateQ (preImpl kem selected keys) client).run history) =
      (simulateQ (evaluatedPre baseImpl kem secret selected keys) client).run history := by
  unfold evalKem
  rw [← QueryImpl.simulateQ_compose]
  apply simulateQ_StateT_compose
  intro query before
  rw [QueryImpl.simulateQ_compose]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete adaptive prechallenge service retains every actual optional reply, earlier observation and private key slot. The selected secret occurs only in interpretation and source-state reconstruction. -/
theorem pre_complete {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat)
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (client : OracleComp DecapSpec Result) :
    (fun result => (result.1, pack pool.keys result.2)) <$>
      evalKem baseImpl kem secret ((simulateQ (preImpl kem selected (redact selected pool)) client).run pool.transcript) =
      (simulateQ (nativeImpl baseImpl kem) client).run pool := by
  rw [pre_interpreted]
  have step (query : DecapSpec.Domain) (history : List (PqxdhLiveKemBirth.Observation KemSK)) :
      Prod.map id (pack pool.keys) <$>
        (evaluatedPre baseImpl kem secret selected (redact selected pool) query).run history =
        (nativeImpl baseImpl kem query).run (pack pool.keys history) := by
    have actual := pre_step baseImpl kem (pack pool.keys history) selected target secret present query
    rw [show redact selected (pack pool.keys history) = redact selected pool from rfl] at actual
    simpa only [evaluatedPre, StateT.run, Prod.map_def, id_eq, pack] using actual
  simpa only [Prod.map_def, id_eq, pack] using
    map_run_simulateQ_eq_of_query_map_eq
      (evaluatedPre baseImpl kem secret selected (redact selected pool))
      (nativeImpl baseImpl kem) (pack pool.keys) step client pool.transcript

set_option backward.isDefEq.respectTransparency false in
/-- Local primitive evaluation forwards only its actual uniform/base interface and cannot make a selected-key decapsulation request. -/
theorem ambient_no_decaps {Result : Type} (work : OracleComp (unifSpec + baseSpec) Result) :
    (ccaAmbient work).IsQueryBoundP (IsMlKemLogicalDecapsulationQuery (ι := ι)) 0 := by
  exact PqxdhPrivateRootQueryBounds.ccaAmbient_bound work _ 0
    (by simpa [IsQueryBoundP, IsMlKemLogicalDecapsulationQuery] using isQueryBoundP_false work 0)

/-- Every source attempt makes at most one selected-key decapsulation request. Local other-key work stays explicit and makes zero such requests. -/
theorem pre_decaps (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (handle : Handle) (ciphertext : MlKem768Ciphertext) :
    (pre kem selected keys handle ciphertext).IsQueryBoundP IsMlKemLogicalDecapsulationQuery 1 := by
  unfold pre
  split
  · simp
  · split
    · exact (isQueryBoundP_query_iff (spec := MlKemCCAOracleSpec baseSpec)
        (p := IsMlKemLogicalDecapsulationQuery) (.inr ciphertext) 1).2 (by simp [IsMlKemLogicalDecapsulationQuery])
    · split
      · simp
      · exact (ambient_no_decaps _).mono (Nat.zero_le _)

/-- Other-key primitive work is charged in the actual forwarded uniform/base class. The selected logical interface is accounted separately. -/
theorem pre_ambient_bound (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (handle : Handle) (ciphertext : MlKem768Ciphertext)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ value, ¬ predicate (.inr value)) (qLocal : Nat)
    (localBound : ∀ secret, (kem.decaps secret ciphertext).IsQueryBoundP (fun query => predicate (.inl query)) qLocal) :
    (pre kem selected keys handle ciphertext).IsQueryBoundP predicate qLocal := by
  unfold pre
  split <;> try simp
  split
  · exact (isQueryBoundP_query_iff (spec := MlKemCCAOracleSpec baseSpec)
      (p := predicate) (.inr ciphertext) qLocal).2 (fun positive => False.elim (excluded ciphertext positive))
  · split <;> try simp
    exact PqxdhPrivateRootQueryBounds.ccaAmbient_bound _ predicate qLocal (localBound _)

/-- Postchallenge routing charges local primitive work and at most one selected oracle query; the exact challenge is blocked by the ordinary router. -/
theorem post_bound (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (challenge : MlKem768Ciphertext)
    (handle : Handle) (ciphertext : MlKem768Ciphertext)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qLocal qSelected : Nat)
    (localBound : ∀ secret, (kem.decaps secret ciphertext).IsQueryBoundP (fun query => predicate (.inl query)) qLocal)
    (selectedBound : (if ciphertext = challenge then 0 else if predicate (.inr ciphertext) then 1 else 0) ≤ qSelected) :
    (post kem selected keys challenge handle ciphertext).IsQueryBoundP predicate (qLocal + qSelected) := by
  unfold post
  split <;> try simp
  split
  · exact (PqxdhPhase2DecapsulationRouting.ordinaryDecapsulate_bound challenge ciphertext predicate).mono
      (selectedBound.trans (Nat.le_add_left _ _))
  · split <;> simp only [isQueryBoundP_pure, isQueryBoundP_map_iff]
    exact (PqxdhPrivateRootQueryBounds.ccaAmbient_bound _ predicate qLocal (localBound _)).mono (Nat.le_add_right _ _)

/-- A complete adaptive q-attempt decapsulation schedule retains its complete history and makes at most q selected-oracle requests. -/
theorem pre_schedule_decaps {Result : Type}
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (client : OracleComp DecapSpec Result)
    (q : Nat) (bounded : client.IsTotalQueryBound q)
    (history : List (PqxdhLiveKemBirth.Observation KemSK)) :
    ((simulateQ (preImpl kem selected keys) client).run history).IsQueryBoundP IsMlKemLogicalDecapsulationQuery q := by
  apply ((isQueryBoundP_true_iff client q).2 bounded).simulateQ_run_StateT_of_step
  exact fun query history => by
    simpa only [preImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, ite_true] using
      pre_decaps kem selected keys query.1 query.2

/-- Every local other-key primitive allowance is multiplied by the complete source attempt cap. Both uniform and base classes use this bound. -/
theorem pre_schedule_ambient {Result : Type}
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (client : OracleComp DecapSpec Result)
    (q : Nat) (bounded : client.IsTotalQueryBound q)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ value, ¬ predicate (.inr value)) (qLocal : Nat)
    (localBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP (fun query => predicate (.inl query)) qLocal)
    (history : List (PqxdhLiveKemBirth.Observation KemSK)) :
    ((simulateQ (preImpl kem selected keys) client).run history).IsQueryBoundP predicate (qLocal * q) := by
  have original (kind : Unit) : client.IsQueryBoundP (fun _ => () = kind) q := by
    cases kind
    simpa [IsQueryBoundP, IsTotalQueryBound] using bounded
  have step (query : DecapSpec.Domain) (before : List (PqxdhLiveKemBirth.Observation KemSK)) :
      ((preImpl kem selected keys query).run before).IsQueryBoundP predicate qLocal := by
    simpa only [preImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff] using
      pre_ambient_bound kem selected keys query.1 query.2 predicate excluded qLocal (fun secret => localBound secret query.2)
  simpa only [Finset.univ_unique, Finset.sum_singleton] using
    FinitePartitionQueryBounds.weighted_bound (fun _ => ()) (fun _ => qLocal) (fun _ => q)
      (preImpl kem selected keys) predicate client original step history

end BeaconcryptCore.Computational.PqxdhLiveKemRouting

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.selected_redacted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.selected_redacted

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.other_redacted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.other_redacted

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.known_not_challenge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.known_not_challenge

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.post_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.post_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_source_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_source_state

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_step

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_interpreted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_interpreted

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.ambient_no_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.ambient_no_decaps

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_decaps

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_ambient_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_ambient_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.post_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.post_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_schedule_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_schedule_decaps

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_schedule_ambient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemRouting.pre_schedule_ambient
