-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedKem
import BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditOpenKey
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal
/-! The genuine real reserved provider audit is bounded on the actual corrected warm source tree, with its original ledger, returned frontend and persistent platform state. Both the source chronology and the actual unused-role receipt are derived internally. This is an explicit reserved-provider game; it is not identified with a candidate-observed on-demand-provider audit. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedAudit
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)


omit primitive in
private theorem reference_coins (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : Secret)
    {A : Type} (work : ProbComp A)
    (before : (PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) × RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ (RegistrationNativeOpenKeyKemEarlyRealSource.reference setup.baseImpl setup.kem pairs publicKey challenge candidate)
      (simulateQ RegistrationNativePlatformG3InitializedKem.coins work)).run before = (fun reply => (reply, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeOpenKeyKemEarlyRealSource.reference setup.baseImpl setup.kem pairs publicKey challenge candidate ∘ₛ RegistrationNativePlatformG3InitializedKem.coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT _ ProbComp) := by
    funext query
    apply StateT.ext
    rintro ⟨external, table⟩
    simp only [QueryImpl.compose, RegistrationNativePlatformG3InitializedKem.coins, RegistrationNativeOpenKey.keyLift,
      RegistrationNativeKeyCompiler.coins, simulateQ_spec_query, RegistrationNativeOpenKeyKemEarlyRealSource.reference,
      QueryImpl.liftTarget_apply, QueryImpl.ofLift, StateT.run, PqxdhRegistrationJointKemSecondEntry.lazyImpl]
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

/-- The genuine real early interpreter forwards the exact warm source prefix and its reached cache without altering its private KEM state. -/
theorem reference_source (budget : PqxdhDeploymentInterface.Budget) (selectedOwner : Nat) (previous : Platform)
    (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : Secret) :
    (simulateQ (RegistrationNativeOpenKeyKemEarlyRealSource.reference setup.baseImpl setup.kem pairs publicKey challenge candidate)
      (RegistrationNativePlatformG3InitializedKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selectedOwner previous)).run' ((PqxdhLiveKemBirth.empty, none), ∅) =
      (do let context ← prior setup source ensureInit identityIndex serverKeyId budget
          (simulateQ (RegistrationNativeOpenKeyKemEarlyRealSource.reference setup.baseImpl setup.kem pairs publicKey challenge candidate)
            (RegistrationNativePlatformG3InitializedKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selectedOwner previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)) := by
  unfold RegistrationNativePlatformG3InitializedKem.program
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  rw [reference_coins setup]
  simp only [bind_map_left]

omit primitive in
private theorem reference_values {A P : Type}
    (provider : RegistrationNativeSecretWordNativePlain.NativeProvider KemSK P)
    (work : OracleComp (RegistrationNativeOpenKey.Spec KemSK) A) (state : P)
    (table : RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ ((PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase
        (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)).flattenStateT) work).run' (state, table) =
      (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work).run' state)).run' table := by
  have actual := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT PqxdhRegistrationJointKemSecondEntry.lazyImpl
    (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work state table
  have observed := congrArg (Functor.map (fun result => result.1.1)) actual
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using observed.symm


noncomputable def audit (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ProbComp Bool := do
  let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) budget.create
  let pair ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let _ ← $ᵗ PqxdhKemIndCca.MlKemSharedSecret
  let context ← prior setup source ensureInit identityIndex serverKeyId budget
  match context.2.2.2.1 with
  | none => pure false
  | some started => do
    let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
    let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
    let result ← RegistrationNativePlatformG3RepeatRun.original setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route seeds wire
      (RegistrationNativeMldsa.owned source started.credential) context.1 context.2.1 pair.2
      (RegistrationNativeOpenKeyKemEarlyRealSource.provider setup.baseImpl setup.kem
        (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 pair.2) checks source selected.val selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩)
      (started.frontend, previous) (RegistrationNativeHiddenInterpreter.initial none, ∅)
      (RegistrationNativeG3LocalMaterialCompletedSource.cache materials) context.2.2.2.2
    pure result.2.2

/-- The real reserved audit is charged to the same whole warm client's actual repeated-role observation, preserving refusals and the entire P state. -/
theorem audit_le_real (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    Pr{let flag ← (audit setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous)}[flag = true] ≤
      Pr{let flag ← (RegistrationNativePlatformG3InitializedKem.real setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous)}[flag = true] := by
  classical
  unfold audit RegistrationNativePlatformG3InitializedKem.real RegistrationNativeOpenKeyKemEarlyObservedReal.source
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun chosen => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun others => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pair => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun unusedDraw => ?_
  rw [reference_source]
  simp only [map_bind]
  apply OracleComp.prEvent_bind_mono_of_support
  intro context reached
  cases success : context.2.2.2.1 with
  | none =>
    simp only [RegistrationNativePlatformG3InitializedKem.after, success, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
      RegistrationNativePlatformG3InitializedKem.repeatObservation, RegistrationNativePlatformSecretWordInitializedSource.Event, decide_false]
    exact le_refl (prEvent (pure (false = true) : ProbComp Prop))
  | some started =>
    have fields := RegistrationNativePlatformPublicRecordOpaqueInitialized.prior_fields setup source ensureInit identityIndex serverKeyId budget context started reached success
    have point := RegistrationNativePlatformG3AuditOpenKey.bound setup wire route (RegistrationNativeMldsa.owned source started.credential)
      context.1 context.2.1 pair.2 view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer checks source
      selected.val selectedAccept serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys context.1, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous)
      budget (bounded _) (RegistrationNativeOpenKeyKemEarlyRealSource.provider setup.baseImpl setup.kem
        (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 pair.2)
      (RegistrationNativeHiddenInterpreter.initial none) context.2.2.2.2 fields.2.2.2.1
    simp only [RegistrationNativePlatformG3InitializedKem.after, success, simulateQ_map, StateT.run'_map', Functor.map_map,
      RegistrationNativePlatformG3InitializedKem.repeatObservation, RegistrationNativePlatformSecretWordInitializedSource.Event,
      decide_eq_true_eq]
    rw [RegistrationNativeOpenKeyKemEarlyRealSource.reference, reference_values]
    simp only [RegistrationNativePlatformG3CheckedUniformSource.openProgram, RegistrationNativeG3MaterializedRetainedLazy.client,
      RegistrationNativeG3MaterializedRetainedSource.ordinary, RegistrationNativeG3NativeUniformAuditBound.ordinary,
      RegistrationNativeHiddenInterpreter.initial,
      RegistrationNativePlatformSecretWordOrdinary.evaluate, Prod.map_def, id_eq,
      RegistrationNativeG3NativeStartupFields.word_eval] at point ⊢
    exact point

/-- The actual warm real reserved audit pays one ordinary CCA loss, unconditional correctness error and twice one whole-prefix recovery loss. -/
theorem bound (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    Pr{let flag ← (audit setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous)}[flag = true] ≤
      RegistrationNativePlatformG3InitializedKem.loss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous :=
  (audit_le_real setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget bounded selected previous).trans
    (RegistrationNativePlatformG3InitializedKem.real_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary functional budget bounded selected previous)

end BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedAudit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedAudit.reference_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedAudit.reference_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedAudit.audit_le_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedAudit.audit_le_real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedAudit.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3InitializedAudit.bound
