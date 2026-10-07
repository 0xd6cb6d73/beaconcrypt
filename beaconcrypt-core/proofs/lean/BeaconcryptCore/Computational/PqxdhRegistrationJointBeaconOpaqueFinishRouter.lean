import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinish

/-!
# The router of the marked branch no longer needs the candidate (item 2, stage S0b completion)

This module completes stage S0b of the item 2 plan. In the marked branch of `PqxdhRegistrationJointBeaconOpaqueFinish`, every Beacon finish keeps only the presence of the router's reply to the decapsulation of the challenge ciphertext under the selected KEM creation index, but the post-challenge router still holds the KEM candidate. The main theorem `opaqueBranch_freeRouter` states that the opaque raw-ordinal branch of theorem T6 equals `freeRouterBranch`, in which the router holds the fixed public value `placeholder` instead. In that branch the candidate is an argument only of the Server's private resumption interpreter (as in T6) and of the private Beacon root interpreter `markedRoot`; no observer, no router state and no Beacon state holds it. It still remains in one place of the program state: both interpreters read the shared Extract table at the 192-byte input `padFF32 ‖ m ‖ candidate` (`PqxdhServerAuthNative.romRootBytes`, and `PqxdhServerAuthNative.sourceRoot` called by `markedRoot`) and store that input as a key of the table cache, which `PqxdhServerAuthNative.eraseObservers` keeps and which the adversary's public `.hmac` and every other root read consult. So the candidate is the 32-byte suffix of these cache keys until stage S1c, which removes this carrier with the random-oracle split `PqxdhExtractRomHiddenSuffix.hidden_suffix_bound`.

Proof. By `router_moves`, the router holding `placeholder`, with its reply to that one request overwritten by the candidate (`markPool`), is the router holding the candidate. The overwriting is then pushed into the program (`markPool_actual`) and shown to change nothing (`markedResume_unmarked`):

- no component other than the Beacon finish sends that request: the Server's raw accept and its prefix compiler (`accept_free`, `prefix_compiler_free`, `prefixImpl_step`), every other native handler (`native_free`, `source_step`, `marked_step`), Beacon creation, bundle and field reads (`creation_free`, `bundle_compiler_free`, `read_free`, `client_free`) and the Server's opaque resumption (`resume_free`), so marking leaves their programs unchanged (`mark_free`, `simulateQ_agree`);
- the marked Beacon finish maps that reply to the challenge marker and never reads its value (`finish_unmarked`).

The query counting uses `IsQueryBoundP` with the request predicates `IsTarget` (private pool) and `onLeft` (its lift to each enclosing interface), and VCVio's `IsQueryBoundP.simulateQ_run_StateT_of_step`. These are program equalities; they charge no advantage.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemObserverFree PqxdhRegistrationJointBeaconOpaqueFinish

/-! ### Requests for the selected decapsulation of the challenge -/

section Target

variable {KemSK : Type}

/-- The request domain of the private-pool interface (it does not depend on the KEM secret-key type). -/
abbrev PoolDomain := (ℕ ⊕ PqxdhDynamicIdentityPool.PoolQuery) ⊕ ℕ ⊕ PqxdhLiveKemBirth.Query

/-- The private-pool decapsulation of `challenge` under KEM creation index `selected`. -/
def IsTarget (selected : Nat) (challenge : MlKem768Ciphertext) : PoolDomain → Prop
  | .inr (.inr (.decapsulate index ciphertext)) => index = selected ∧ ciphertext = challenge
  | _ => False

instance (selected : Nat) (challenge : MlKem768Ciphertext) :
    DecidablePred (IsTarget selected challenge)
  | .inr (.inr (.decapsulate index ciphertext)) =>
      inferInstanceAs (Decidable (index = selected ∧ ciphertext = challenge))
  | .inr (.inr .create) => inferInstanceAs (Decidable False)
  | .inr (.inr (.reveal _)) => inferInstanceAs (Decidable False)
  | .inr (.inl _) => inferInstanceAs (Decidable False)
  | .inl _ => inferInstanceAs (Decidable False)

/-- A predicate on the left summand of a request domain; right-summand requests never satisfy it. -/
def onLeft {X Y : Type} (predicate : X → Prop) : X ⊕ Y → Prop
  | .inl query => predicate query
  | .inr _ => False

instance {X Y : Type} (predicate : X → Prop) [DecidablePred predicate] :
    DecidablePred (onLeft (Y := Y) predicate)
  | .inl query => inferInstanceAs (Decidable (predicate query))
  | .inr _ => inferInstanceAs (Decidable False)

@[simp]
theorem onLeft_inl {X Y : Type} (predicate : X → Prop) (query : X) :
    onLeft (Y := Y) predicate (.inl query) = predicate query := rfl

@[simp]
theorem onLeft_inr {X Y : Type} (predicate : X → Prop) (query : Y) :
    onLeft predicate (.inr query : X ⊕ Y) = False := rfl

/-- The same request on the exposed encapsulation interface. -/
abbrev IsTargetEnc (selected : Nat) (challenge : MlKem768Ciphertext) :
    PoolDomain ⊕ (Pqxdh.Bytes × MlKem768PublicKey) → Prop :=
  onLeft (IsTarget selected challenge)

/-- Marking leaves every other private-pool request unchanged. -/
theorem markPool_other (selected : Nat) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (other : ¬ IsTarget selected challenge query) :
    markPool selected challenge candidate query = (PqxdhLiveKemBirth.Spec KemSK).query query := by
  rcases query with joint | (coin | (_ | ⟨index, ciphertext⟩ | index))
  · rfl
  · rfl
  · rfl
  · have : ¬ (index = selected ∧ ciphertext = challenge) := other
    simp only [markPool, this, ↓reduceIte]
  · rfl

/-- Marking leaves every program without the selected decapsulation of the challenge unchanged. -/
theorem mark_free {α : Type} (selected : Nat) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) α)
    (free : work.IsQueryBoundP (IsTargetEnc selected challenge) 0) :
    simulateQ (markEnc selected challenge candidate) work = work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at free
      have other : ¬ IsTargetEnc selected challenge query := by
        rcases free.1 with miss | positive
        · exact miss
        · omega
      have rest : ∀ answer, (next answer).IsQueryBoundP (IsTargetEnc selected challenge) 0 := by
        intro answer
        simpa [other] using free.2 answer
      simp only [simulateQ_bind, simulateQ_spec_query]
      rcases query with query | request
      · have step : markEnc selected challenge candidate (.inl query) =
            (liftM ((PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query (.inl query)) :
              OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) _) := by
          simp only [markEnc, markPool_other selected challenge candidate query other, simulateQ_spec_query,
            PqxdhRegistrationJointKemEncapsulation.forward]
        rw [step]
        simp only [ih _ (rest _)]
      · simp only [markEnc, ih _ (rest _)]

end Target

/-! ### Generic query-bound tools -/

section Tools

/-- Interpreting a program by a handler whose every step avoids a predicate avoids it. -/
theorem simulateQ_free {ι ι' α : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec (OracleComp spec')) (bad : ι' → Prop) [DecidablePred bad]
    (step : ∀ query, (impl query).IsQueryBoundP bad 0) (work : OracleComp spec α) :
    (simulateQ impl work).IsQueryBoundP bad 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (isQueryBoundP_bind (step query) fun answer _ => ih answer).mono (by omega)

/-- Two handlers that agree off a predicate interpret every program avoiding it in the same way. -/
theorem simulateQ_agree {ι α : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (left right : QueryImpl spec m) (bad : ι → Prop) [DecidablePred bad]
    (agree : ∀ query, ¬ bad query → left query = right query) (work : OracleComp spec α)
    (free : work.IsQueryBoundP bad 0) :
    simulateQ left work = simulateQ right work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at free
      have other : ¬ bad query := by
        rcases free.1 with miss | positive
        · exact miss
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, agree query other]
      refine bind_congr fun answer => ih answer ?_
      simpa [other] using free.2 answer

/-- Interpreting a program that avoids a predicate by a handler that uses one target request exactly for each source request satisfying it avoids the target predicate. -/
theorem simulateQ_transfer {ι ι' α : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec (OracleComp spec')) (bad : ι → Prop) [DecidablePred bad]
    (bad' : ι' → Prop) [DecidablePred bad']
    (step : ∀ query, (impl query).IsQueryBoundP bad' (if bad query then 1 else 0)) (work : OracleComp spec α)
    (free : work.IsQueryBoundP bad 0) :
    (simulateQ impl work).IsQueryBoundP bad' 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at free
      have other : ¬ bad query := by
        rcases free.1 with miss | positive
        · exact miss
        · omega
      have first := step query
      simp only [other, ↓reduceIte] at first
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (isQueryBoundP_bind first fun answer _ => ih answer (by simpa [other] using free.2 answer)).mono
        (by omega)

/-- Uniform coins forwarded to the private-pool interface never request a decapsulation. -/
theorem coins_free {α : Type} {KemSK : Type} (selected : Nat) (challenge : MlKem768Ciphertext) (work : ProbComp α) :
    (PqxdhLiveKemBirth.coins (KemSK := KemSK) work).IsQueryBoundP (IsTarget selected challenge) 0 := by
  unfold PqxdhLiveKemBirth.coins
  refine simulateQ_free _ _ (fun query => ?_) work
  rw [isQueryBoundP_query_iff]
  intro target
  exact absurd target id

end Tools

/-! ### No other native handler requests the selected decapsulation of the challenge -/

section Steps

open PqxdhServerAuthNative (NativeGame NativeState eraseObservers)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

theorem forward_free {α : Type} (selected : Nat) (challenge : MlKem768Ciphertext)
    (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (free : work.IsQueryBoundP (IsTarget selected challenge) 0) :
    (simulateQ (PqxdhRegistrationJointKemEncapsulation.forward (KemSK := KemSK)) work).IsQueryBoundP
      (IsTargetEnc selected challenge) 0 :=
  simulateQ_transfer _ (IsTarget selected challenge) _ (fun query => by
    simp only [PqxdhRegistrationJointKemEncapsulation.forward, isQueryBoundP_query_iff, onLeft_inl]
    intro target
    simp [target]) work free

/-- Lifted native work only draws uniform coins. -/
theorem native_free {α : Type} (selected : Nat) (challenge : MlKem768Ciphertext) (work : NativeGame KemSK α)
    (state : NativeState KemSK) :
    ((PqxdhRegistrationJointKemEncapsulation.lift (KemSK := KemSK)
      (PqxdhRegistrationJointOpenBackend.native (KemSK := KemSK) work)).run state).IsQueryBoundP
      (IsTargetEnc selected challenge) 0 :=
  forward_free selected challenge _ (coins_free selected challenge _)

/-- The Server's prefix compiler requests no private-pool decapsulation. -/
theorem prefix_compiler_free (selected : Nat) (challenge : MlKem768Ciphertext) (identityIndex : Nat)
    (query : (PqxdhRegistrationJointServerPrefix.NativeSpec Reader).Domain) :
    (PqxdhRegistrationJointServerPrefix.compiler (KemSK := KemSK) identityIndex query).IsQueryBoundP
      (onLeft (IsTarget selected challenge)) 0 := by
  cases query <;> simp [PqxdhRegistrationJointServerPrefix.compiler, isQueryBoundP_query_iff, IsTarget]

/-- Each step of the Server's prefix interpreter requests the selected decapsulation of the challenge only when it forwards it. -/
theorem prefixImpl_step (selected : Nat) (challenge : MlKem768Ciphertext) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (raw : Pqxdh.Bytes)
    (query : (PqxdhRegistrationJointServerPrefix.Spec KemSK Reader).Domain) (consumed : List Pqxdh.Bytes) :
    ((PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw query).run consumed).IsQueryBoundP
      (IsTargetEnc selected challenge) (if onLeft (IsTarget selected challenge) query then 1 else 0) := by
  rcases query with query | query
  · simp only [PqxdhRegistrationJointKemEncapsulation.prefixImpl, StateT.run, isQueryBoundP_map_iff,
      PqxdhRegistrationJointKemEncapsulation.forward, isQueryBoundP_query_iff, onLeft_inl]
    intro target
    simp [target]
  · cases query
    case encapsulate key =>
      simp [PqxdhRegistrationJointKemEncapsulation.prefixImpl, StateT.run, isQueryBoundP_query_iff]
    all_goals
      simp only [PqxdhRegistrationJointKemEncapsulation.prefixImpl, onLeft_inr, ↓reduceIte]
      exact forward_free selected challenge _ (coins_free selected challenge _)

/-- The Server's raw accept with its encapsulation exposed requests no selected decapsulation of the challenge. -/
theorem accept_free (selected : Nat) (challenge : MlKem768Ciphertext) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw).run
      state).IsQueryBoundP (IsTargetEnc selected challenge) 0 := by
  have prepared : ∀ start : NativeState KemSK,
      ((PqxdhRegistrationJointKemEncapsulation.prepare setup codec checks identityIndex raw).run start).IsQueryBoundP
        (IsTargetEnc selected challenge) 0 := by
    intro start
    change ((fun result => (result, start)) <$>
      (simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
        (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run start.2.server.consumed).IsQueryBoundP
      (IsTargetEnc selected challenge) 0
    rw [isQueryBoundP_map_iff]
    refine IsQueryBoundP.simulateQ_run_StateT_of_step (p := onLeft (IsTarget selected challenge)) ?_ ?_ _
    · exact simulateQ_free _ _ (prefix_compiler_free selected challenge identityIndex) _
    · exact fun query consumed => prefixImpl_step selected challenge setup codec checks raw query consumed
  unfold PqxdhRegistrationJointKemEncapsulation.accept
  rw [StateT.run_bind]
  refine isQueryBoundP_bind (n := 0) (m := 0) (native_free selected challenge _ state) fun before _ => ?_
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (n := 0) (m := 0) (prepared before.2) fun collected _ => native_free selected challenge _ _

/-- Each step of the erased native source backend requests the selected decapsulation of the challenge only when it forwards it. -/
theorem source_step (selected : Nat) (challenge : MlKem768Ciphertext) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) (state : NativeState KemSK) :
    ((eraseImpl eraseObservers (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex
      publicIdentity) query).run state).IsQueryBoundP (IsTargetEnc selected challenge)
      (if onLeft (onLeft (IsTarget selected challenge)) query then 1 else 0) := by
  show IsQueryBoundP (Prod.map id eraseObservers <$> ((PqxdhRegistrationJointKemEncapsulation.impl setup codec checks
    identityIndex publicIdentity query).run (eraseObservers state))) _ _
  rw [isQueryBoundP_map_iff]
  rcases query with (pool | tail) | shared
  · simp only [PqxdhRegistrationJointKemEncapsulation.impl, PqxdhRegistrationJointOpenBackend.impl,
      PqxdhRegistrationJointOpenBackend.pool, PqxdhRegistrationJointKemEncapsulation.lift, StateT.run,
      simulateQ_map, simulateQ_spec_query, isQueryBoundP_map_iff, PqxdhRegistrationJointKemEncapsulation.forward,
      isQueryBoundP_query_iff, onLeft_inl]
    intro target
    simp [target]
  · simp only [onLeft_inl, onLeft_inr, ↓reduceIte]
    exact native_free selected challenge _ _
  · simp only [onLeft_inr, ↓reduceIte]
    cases shared with
    | accept raw => exact accept_free selected challenge setup codec checks identityIndex publicIdentity raw _
    | build session payload => exact native_free selected challenge _ _
    | hmac key message => exact native_free selected challenge _ _
    | hash bytes => exact native_free selected challenge _ _
    | reveal keyId => exact native_free selected challenge _ _

/-- Each step of the erased marked backend requests the selected decapsulation of the challenge only when it forwards it. -/
theorem marked_step (selected : Nat) (challenge : MlKem768Ciphertext) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (candidate : MlKemSharedSecret) (query : (MarkedSpec KemSK Response).Domain) (state : NativeState KemSK) :
    ((eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate) query).run
      state).IsQueryBoundP (IsTargetEnc selected challenge)
      (if onLeft (onLeft (onLeft (IsTarget selected challenge))) query then 1 else 0) := by
  rcases query with query | secrets
  · exact source_step selected challenge setup codec checks identityIndex publicIdentity query state
  · show IsQueryBoundP (Prod.map id eraseObservers <$> ((markedImpl setup codec checks identityIndex publicIdentity
      candidate (.inr secrets)).run (eraseObservers state))) _ _
    rw [isQueryBoundP_map_iff]
    simp only [onLeft_inr, ↓reduceIte]
    exact native_free selected challenge _ _

end Steps

/-! ### No other client step requests the selected decapsulation of the challenge -/

section Client

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Forwarding private-pool requests to the source client interface keeps them countable. -/
theorem poolLift_free {α : Type} (selected : Nat) (challenge : MlKem768Ciphertext)
    (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (free : work.IsQueryBoundP (IsTarget selected challenge) 0) :
    (simulateQ (PqxdhRegistrationJointServiceSchedule.poolLift (KemSK := KemSK) (Response := Response)) work).IsQueryBoundP
      (onLeft (onLeft (IsTarget selected challenge))) 0 :=
  simulateQ_transfer _ (IsTarget selected challenge) _ (fun query => by
    simp only [PqxdhRegistrationJointServiceSchedule.poolLift, isQueryBoundP_query_iff, onLeft_inl]
    intro target
    simp [target]) work free

theorem creation_free (selected : Nat) (challenge : MlKem768Ciphertext) :
    (PqxdhRegistrationJointCreation.client (KemSK := KemSK)).IsQueryBoundP (IsTarget selected challenge) 0 := by
  unfold PqxdhRegistrationJointCreation.client
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [IsTarget]), fun identity => ?_⟩
  simp only [IsTarget, ↓reduceIte]
  cases identity with
  | none => trivial
  | some identity =>
      refine isQueryBoundP_bind (n := 0) (m := 0) (coins_free selected challenge _) fun prekey _ => ?_
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [IsTarget]), fun pair => trivial⟩

theorem bundle_compiler_free (selected : Nat) (challenge : MlKem768Ciphertext) (codec : Codec Reader Response)
    (query : (PqxdhLivePhase1Bundle.Spec PqxdhJointGapDh.ScalarBytes).Domain) :
    (PqxdhRegistrationJointBundleCompiler.compiler (KemSK := KemSK) codec query).IsQueryBoundP
      (IsTarget selected challenge) 0 := by
  rcases query with generate | (joint | candidate)
  · exact coins_free selected challenge _
  · simp [PqxdhRegistrationJointBundleCompiler.compiler, isQueryBoundP_query_iff, IsTarget]
  · trivial

theorem read_free (selected : Nat) (challenge : MlKem768Ciphertext) (field : PqxdhRegistrationJointLiveRead.Field)
    (entry : PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    (PqxdhRegistrationJointLiveRead.entryClient (KemSK := KemSK) field entry).IsQueryBoundP
      (IsTarget selected challenge) 0 := by
  cases field with
  | identity =>
      exact (isQueryBoundP_map_iff _ _ _).mpr ((isQueryBoundP_query_iff _ _ _).mpr fun target => False.elim target)
  | kem =>
      simp only [PqxdhRegistrationJointLiveRead.entryClient]
      split
      · trivial
      · exact (isQueryBoundP_map_iff _ _ _).mpr ((isQueryBoundP_query_iff _ _ _).mpr fun target => False.elim target)
  | prekey => trivial
  | oneTime => trivial
  | kernel => trivial

/-- Every source client step other than a Beacon finish requests no selected decapsulation of the challenge. -/
theorem client_free (selected : Nat) (challenge : MlKem768Ciphertext) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : ∀ address raw, query ≠ .inl (.inr (.finish address raw)))
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run owners).IsQueryBoundP
      (onLeft (onLeft (IsTarget selected challenge))) 0 := by
  rcases query with (coin | request) | read
  · simp [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
      isQueryBoundP_query_iff, IsTarget]
  · cases request with
    | create pin keyId =>
        simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
          PqxdhRegistrationJointServiceSchedule.create, StateT.run]
        exact isQueryBoundP_bind (n := 0) (m := 0) (poolLift_free selected challenge _ (creation_free selected challenge))
          fun _ _ => trivial
    | bundle address =>
        simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
          PqxdhRegistrationJointServiceSchedule.bundle, StateT.run]
        split
        · trivial
        · rw [isQueryBoundP_map_iff]
          exact poolLift_free selected challenge _
            (simulateQ_free _ _ (bundle_compiler_free selected challenge codec) _)
    | finish address raw => exact absurd rfl (other address raw)
    | _ => simp [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
        isQueryBoundP_query_iff]
  · simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointLiveRead.clientStep, StateT.run]
    split
    · trivial
    · rw [isQueryBoundP_map_iff]
      exact poolLift_free selected challenge _ (read_free selected challenge _ _)

end Client

/-! ### The marked Beacon finish discards the value of the marked reply -/

section Finish

open PqxdhServerAuthNative (NativeState eraseObservers)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The erased marked backend whose every step is marked by `marker`. -/
noncomputable abbrev markedBy (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate marker : MlKemSharedSecret) :=
  markHandler selected challenge marker
    (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))

/-- Marking changes no step of the marked backend other than the forwarded selected decapsulation of the challenge. -/
theorem markedBy_other (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate marker : MlKemSharedSecret) (query : (MarkedSpec KemSK Response).Domain)
    (other : ¬ onLeft (onLeft (onLeft (IsTarget selected challenge))) query) :
    markedBy setup codec checks identityIndex publicIdentity selected challenge candidate marker query =
      eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate) query := by
  apply StateT.ext
  intro state
  change simulateQ (markEnc selected challenge marker) _ = _
  apply mark_free
  simpa [other] using
    marked_step selected challenge setup codec checks identityIndex publicIdentity candidate query state

/-- Forwarding private-pool requests to the marked interface keeps them countable. -/
theorem markedPoolLift_free {α : Type} (selected : Nat) (challenge : MlKem768Ciphertext)
    (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (free : work.IsQueryBoundP (IsTarget selected challenge) 0) :
    (simulateQ (markedPoolLift (KemSK := KemSK) (Response := Response)) work).IsQueryBoundP
      (onLeft (onLeft (onLeft (IsTarget selected challenge)))) 0 :=
  simulateQ_transfer _ (IsTarget selected challenge) _ (fun query => by
    simp only [markedPoolLift, isQueryBoundP_query_iff, onLeft_inl]
    intro target
    simp [target]) work free

/-- The marked Beacon finish has the same interpretation whether or not the backend marks the selected decapsulation of the challenge: the opaque-handle owner keeps only the presence of that reply. -/
theorem finish_unmarked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate marker : MlKemSharedSecret) (address : Nat) (raw : Pqxdh.Bytes)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    simulateQ (markedBy setup codec checks identityIndex publicIdentity selected challenge candidate marker)
        ((markedFinish setup codec selected challenge address raw).run owners) =
      simulateQ (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))
        ((markedFinish setup codec selected challenge address raw).run owners) := by
  simp only [markedFinish, StateT.run]
  cases found : owners[address]? with
  | none => simp
  | some entry =>
      simp only [simulateQ_map]
      congr 1
      rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
      congr 1
      funext query
      rcases query with prepare | (rawQuery | (rootSecrets | initial | application))
      · by_cases decap : ∃ ciphertext key, prepare =
            PqxdhBeaconPhase2Shared.Query.decapsulate ciphertext key ∧
              key.2 = selected ∧ PqxdhPhase2InputBytes.ciphertext ciphertext = challenge
        · obtain ⟨ciphertext, key, rfl, target⟩ := decap
          simp only [QueryImpl.apply_compose, markedCompiler, markedPreparation, simulateQ_map, simulateQ_spec_query,
            markedPoolLift]
          have markedPool : ∀ query : (PqxdhLiveKemBirth.Spec KemSK).Domain,
              markedBy (Response := Response) setup codec checks identityIndex publicIdentity selected challenge
                candidate marker (.inl (.inl (.inl query))) =
              StateT.mk fun state => (fun answer => (answer, eraseObservers state)) <$>
                simulateQ PqxdhRegistrationJointKemEncapsulation.forward (markPool selected challenge marker query) :=
            fun query => sourceMarked_pool setup codec checks identityIndex publicIdentity selected challenge marker query
          rw [markedPool]
          apply StateT.ext
          intro state
          simp only [StateT.run_map, StateT.run_mk, markPool, target, and_self, ↓reduceIte, simulateQ_map,
            simulateQ_spec_query, Functor.map_map]
          simp only [eraseImpl, markedImpl, QueryImpl.add_apply_inl, PqxdhRegistrationJointKemEncapsulation.impl,
            PqxdhRegistrationJointOpenBackend.impl, PqxdhRegistrationJointOpenBackend.pool,
            PqxdhRegistrationJointKemEncapsulation.lift, StateT.run, StateT.mk, Functor.map_map, simulateQ_map,
            simulateQ_spec_query, PqxdhRegistrationJointKemEncapsulation.forward]
          congr 1
          funext reply
          cases reply <;> rfl
        · simp only [QueryImpl.apply_compose, markedCompiler]
          refine simulateQ_agree _ _ (onLeft (onLeft (onLeft (IsTarget selected challenge))))
            (fun query other => markedBy_other setup codec checks identityIndex publicIdentity selected challenge
              candidate marker query other) _ (markedPoolLift_free selected challenge _ ?_)
          cases prepare with
          | decapsulate ciphertext key =>
              have different : ¬ (key.2 = selected ∧ PqxdhPhase2InputBytes.ciphertext ciphertext = challenge) :=
                fun target => decap ⟨ciphertext, key, rfl, target⟩
              exact (isQueryBoundP_map_iff _ _ _).mpr ((isQueryBoundP_query_iff _ _ _).mpr fun target =>
                absurd target different)
          | dhIdentity index point =>
              exact (isQueryBoundP_map_iff _ _ _).mpr ((isQueryBoundP_query_iff _ _ _).mpr fun target =>
                False.elim target)
          | _ => trivial
      all_goals
        simp only [QueryImpl.apply_compose, markedCompiler, simulateQ_spec_query]
        exact markedBy_other setup codec checks identityIndex publicIdentity selected challenge candidate marker _
          (fun target => False.elim target)

end Finish

/-! ### The resumption and the marked client are unchanged by marking -/

section Resume

open PqxdhServerAuthNative (NativeState eraseObservers)
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointAcceptCutTag (Tag)
open PqxdhRegistrationJointAcceptKemCut (tagged hide)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemOpaqueResume (liftImpl clientNative forwardClient)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X R : Type}

/-- A program that never issues any request. -/
theorem free_false {ι' α : Type} {spec : OracleSpec ι'} (work : OracleComp spec α) :
    work.IsQueryBoundP (fun _ => False) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl id, fun answer => by simp [ih answer]⟩

/-- The Server's opaque resumption requests no selected decapsulation of the challenge. -/
theorem resume_free (selected : Nat) (challenge : MlKem768Ciphertext) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (ciphertext : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) :
    ((simulateQ (eraseImpl eraseObservers (liftImpl clientNative setup native.2.sessions candidate forwardClient))
      (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
        (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge native.2 consumed)).run
          (eraseObservers native)).IsQueryBoundP (IsTargetEnc selected challenge) 0 := by
  refine IsQueryBoundP.simulateQ_run_StateT_of_step (p := onLeft (IsTargetEnc selected challenge)) ?_ ?_ _
  · unfold PqxdhRegistrationJointKemOpaqueResume.resume
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun collected _ => ?_
    · refine simulateQ_transfer _ (IsTargetEnc selected challenge) _ (fun query => ?_) _ ?_
      · simp only [PqxdhRegistrationJointKemOpaqueResume.prefixLift, isQueryBoundP_query_iff, onLeft_inl]
        intro target
        simp [target]
      · unfold PqxdhRegistrationJointKemOpaqueSuffix.compiled
        refine IsQueryBoundP.simulateQ_run_StateT_of_step (p := fun _ => False) (free_false _) (fun query state => ?_) _
        simp only [↓reduceIte]
        exact IsQueryBoundP.simulateQ_run_StateT_of_step (p := onLeft (IsTarget selected challenge))
          (prefix_compiler_free selected challenge identityIndex query)
          (fun request current => prefixImpl_step selected challenge setup codec checks raw request current) state
    · refine simulateQ_free _ _ (fun query => ?_) _
      simp only [PqxdhRegistrationJointKemOpaqueResume.tailLift, isQueryBoundP_query_iff, onLeft_inr]
      exact False.elim
  · intro query state
    rcases query with query | tailQuery
    · show IsQueryBoundP (Prod.map id eraseObservers <$> (forwardClient query).run (eraseObservers state)) _ _
      simp only [isQueryBoundP_map_iff, forwardClient, StateT.run, isQueryBoundP_query_iff, onLeft_inl]
      intro target
      simp [target]
    · show IsQueryBoundP (Prod.map id eraseObservers <$> (PqxdhRegistrationJointKemEncapsulation.lift
        (PqxdhRegistrationJointOpenBackend.native _)).run (eraseObservers state)) _ _
      rw [isQueryBoundP_map_iff]
      simp only [onLeft_inr, ↓reduceIte]
      exact native_free selected challenge _ _

/-- Every step of the marked client has the same interpretation whether or not the backend marks the selected decapsulation of the challenge. -/
theorem client_unmarked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate marker : MlKemSharedSecret) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List EncodedEntry) :
    simulateQ (markedBy setup codec checks identityIndex publicIdentity selected challenge candidate marker)
        ((markedClient setup codec selected challenge query).run owners) =
      simulateQ (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))
        ((markedClient setup codec selected challenge query).run owners) := by
  have lifted : ∀ {α : Type} (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α),
      (work.run owners).IsQueryBoundP (onLeft (onLeft (IsTarget selected challenge))) 0 →
      simulateQ (markedBy setup codec checks identityIndex publicIdentity selected challenge candidate marker)
          ((liftClient work).run owners) =
        simulateQ (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))
          ((liftClient work).run owners) := by
    intro _ work free
    change simulateQ _ (simulateQ markedLift (work.run owners)) = simulateQ _ (simulateQ markedLift (work.run owners))
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    refine simulateQ_agree _ _ (onLeft (onLeft (IsTarget selected challenge))) (fun request other => ?_) _ free
    simp only [QueryImpl.apply_compose, markedLift, simulateQ_spec_query]
    exact markedBy_other setup codec checks identityIndex publicIdentity selected challenge candidate marker _ other
  rcases query with (coin | request) | read
  · exact lifted _ (client_free selected challenge setup codec _ (fun _ _ same => by cases same) owners)
  · cases request with
    | finish address raw =>
        exact finish_unmarked setup codec checks identityIndex publicIdentity selected challenge candidate marker
          address raw owners
    | _ => exact lifted _ (client_free selected challenge setup codec _ (fun _ _ same => by cases same) owners)
  · exact lifted _ (client_free selected challenge setup codec _ (fun _ _ same => by cases same) owners)

/-- The marked resumption is unchanged by marking the selected decapsulation of the challenge with any value. -/
theorem markedResume_unmarked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate marker : MlKemSharedSecret) :
    simulateQ (markEnc selected ciphertext marker)
        (markedResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners
          next selected ciphertext candidate) =
      markedResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners
        next selected ciphertext candidate := by
  unfold markedResume
  rw [simulateQ_bind, mark_free selected ciphertext marker _
    (resume_free selected ciphertext setup codec checks identityIndex publicIdentity raw value ephemeral consumed native
      ciphertext candidate)]
  refine bind_congr fun answer => ?_
  rw [markEnc_hide]
  congr 1
  rw [mark_run]
  exact congrArg (fun work => StateT.run work answer.2)
    (layered _ _ _ _ (client_unmarked setup codec checks identityIndex publicIdentity selected ciphertext candidate
      marker) _ owners)

end Resume

/-! ### The router-free branch -/

section Assembly

open PqxdhServerAuthNative (NativeState eraseObservers)
open PqxdhRegistrationJointKemEncapsulation (actual)
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointKemResume (ResultState)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext toContext sourcePreOpaque opaqueBranch)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- A fixed public value held by the router in place of the candidate. -/
def placeholder : MlKemSharedSecret := List.Vector.replicate 32 0

/-- The router-free postchallenge step: the marked postchallenge step with the router holding `placeholder`. The candidate is an argument only of the Server's private resumption interpreter and of the private Beacon root interpreter. -/
noncomputable def freeRouterPost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (ResultState KemSK A Bool count) := do
  match transcript.context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners next)) state _ =>
    if value.keys.pqKey = transcript.publicKey then
      let reached ← (((simulateQ (eraseOptionImpl eraseJoint
          (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey others)
            transcript.ciphertext placeholder))
        (simulateQ (actual setup) (markedResume setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners next selected.val
          transcript.ciphertext candidate))).run).run (eraseJoint state))
      pure (toContext setup codec checks decision transcript.context, some reached)
    else pure (toContext setup codec checks decision transcript.context, none)
  | _ => pure (toContext setup codec checks decision transcript.context, none)

/-- The marked postchallenge step equals the router-free postchallenge step. -/
theorem markedPost_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    markedPost setup codec checks decision count selected transcript candidate =
      freeRouterPost setup codec checks decision count selected transcript candidate := by
  obtain ⟨publicKey, ciphertext, context⟩ := transcript
  cases context with
  | failed state => rfl
  | ready created others cut state runtime =>
    cases cut with
    | none => rfl
    | some cut =>
      cases cut with
      | complete outcome => rfl
      | pending raw value ephemeral consumed native owners next =>
        by_cases active : value.keys.pqKey = publicKey
        · simp only [markedPost, freeRouterPost, active, ↓reduceIte]
          conv_lhs => rw [← router_moves setup.kem setup.joint selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected publicKey others) ciphertext placeholder candidate]
          rw [QueryImpl.simulateQ_compose, markPool_actual, markedResume_unmarked]
        · simp only [markedPost, freeRouterPost, active, ↓reduceIte]

/-- The router-free branch: the marked branch with the router-free postchallenge step. -/
noncomputable def freeRouterBranch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (freeRouterPost setup codec checks decision count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- Stage S0b, completed. The opaque raw-ordinal branch (theorem T6) equals the router-free branch, as programs and for both values of the branch bit: every Beacon finish carries an opaque decapsulation handle and sends its root request privately, the post-challenge router holds the fixed public `placeholder` instead of the candidate, and the candidate is an argument only of the Server's private resumption interpreter and of the private Beacon root interpreter. -/
theorem opaqueBranch_freeRouter (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      freeRouterBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index real := by
  rw [opaqueBranch_marked]
  unfold markedBranch freeRouterBranch
  simp only [markedPost_free]

end Assembly

end BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.onLeft_inl' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.onLeft_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.onLeft_inr' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.onLeft_inr

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.markPool_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.markPool_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.mark_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.mark_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.simulateQ_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.simulateQ_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.simulateQ_agree' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.simulateQ_agree

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.simulateQ_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.simulateQ_transfer

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.coins_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.coins_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.forward_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.forward_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.native_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.native_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.prefix_compiler_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.prefix_compiler_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.prefixImpl_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.prefixImpl_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.accept_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.accept_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.source_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.marked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.marked_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.poolLift_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.poolLift_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.creation_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.creation_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.bundle_compiler_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.bundle_compiler_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.read_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.read_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.client_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.client_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.markedBy_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.markedBy_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.markedPoolLift_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.markedPoolLift_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.finish_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.finish_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.free_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.free_false

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.resume_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.resume_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.client_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.client_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.markedResume_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.markedResume_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.markedPost_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.markedPost_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.opaqueBranch_freeRouter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter.opaqueBranch_freeRouter
