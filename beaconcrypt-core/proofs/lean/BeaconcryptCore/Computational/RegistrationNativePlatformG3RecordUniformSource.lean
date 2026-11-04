-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordKem
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal
/-! The record-aware actual warm KEM uniform branch has the exact conditional early-provider source law. The genuine family/challenge, mathematical candidate and actual startup are reordered only by proved independent sampling. Every complete source value, ledger, terminal record observation and persistent platform state remains available to the same final observer. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniformSource
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
private theorem reference_coins (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : Secret)
    {A : Type} (work : ProbComp A)
    (before : (PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) × RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
      (simulateQ RegistrationNativePlatformG3InitializedKem.coins work)).run before = (fun reply => (reply, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate ∘ₛ RegistrationNativePlatformG3InitializedKem.coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT _ ProbComp) := by
    funext query
    apply StateT.ext
    rintro ⟨external, table⟩
    simp only [QueryImpl.compose, RegistrationNativePlatformG3InitializedKem.coins, RegistrationNativeOpenKey.keyLift,
      RegistrationNativeKeyCompiler.coins, simulateQ_spec_query, RegistrationNativeOpenKeyKemEarlySource.reference,
      QueryImpl.liftTarget_apply, QueryImpl.ofLift, StateT.run, PqxdhRegistrationJointKemSecondEntry.lazyImpl]
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

/-- The genuine early interpreter forwards the exact warm source prefix and its reached cache without altering its private KEM state. -/
theorem reference_source (budget : PqxdhDeploymentInterface.Budget) (selectedOwner : Nat) (previous : Platform)
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : Secret) :
    (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
      (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selectedOwner previous)).run' ((PqxdhLiveKemBirth.empty, none), ∅) =
      (do let context ← prior setup source ensureInit identityIndex serverKeyId budget
          (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
            (RegistrationNativePlatformG3RecordKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selectedOwner previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)) := by
  unfold RegistrationNativePlatformG3RecordKem.program
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  rw [reference_coins setup]
  simp only [bind_map_left]


noncomputable def conditional (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (observe : Secret → RegistrationNativePlatformG3RecordKem.Result source (budget.cap 4 + budget.cap 5) Value Platform → Bool) : ProbComp Bool := do
  let context ← prior setup source ensureInit identityIndex serverKeyId budget
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
  let candidate ← $ᵗ Secret
  observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
    profile.pairs profile.publicKey profile.challenge candidate)
    (RegistrationNativePlatformG3RecordKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected.val previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)


private theorem uniform_of_bounds (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform)
    (observe : Secret → RegistrationNativePlatformG3RecordKem.Result source (budget.cap 4 + budget.cap 5) Value Platform → Bool)
    (creates : (simulateQ RegistrationNativeOpenKey.native
      (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected.val previous)).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) budget.create)
    (noReveal : (simulateQ RegistrationNativeOpenKey.native
      (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected.val previous)).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) 0) :
    RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget selected.val previous)) observe budget.create selected false =ᵈ
      conditional setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous observe := by
  have closed := RegistrationNativeOpenKeyKemEarlyObservedUniform.uniform_source setup.baseImpl setup.kem
    (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected.val previous) observe budget.create selected creates noReveal
  refine closed.trans ?_
  have exactPrefix : RegistrationNativeOpenKeyKemEarlyObservedUniform.source setup.baseImpl setup.kem
      (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected.val previous) observe budget.create selected =
      (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
          let candidate ← $ᵗ Secret
          let context ← prior setup source ensureInit identityIndex serverKeyId budget
          observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
            profile.pairs profile.publicKey profile.challenge candidate)
            (RegistrationNativePlatformG3RecordKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selected.val previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)) := by
    unfold RegistrationNativeOpenKeyKemEarlyObservedUniform.source RegistrationNativeG3NativeRepeatUniformBound.prior
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro chosen
    apply bind_congr
    intro others
    apply bind_congr
    intro pair
    apply bind_congr
    intro candidate
    rw [reference_source]
    simp only [map_bind]
  rw [exactPrefix]
  have swapped :
      (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
          let candidate ← $ᵗ Secret
          let context ← prior setup source ensureInit identityIndex serverKeyId budget
          observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
            profile.pairs profile.publicKey profile.challenge candidate)
            (RegistrationNativePlatformG3RecordKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selected.val previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)) =ᵈ
      (do let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
          let context ← prior setup source ensureInit identityIndex serverKeyId budget
          let candidate ← $ᵗ Secret
          observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
            profile.pairs profile.publicKey profile.challenge candidate)
            (RegistrationNativePlatformG3RecordKem.after setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
              erased helper writer bounds mode adversary budget selected.val previous context)).run' ((PqxdhLiveKemBirth.empty, none), ∅)) := by
    apply _root_.EvalDistEq.bind_right
    intro profile
    exact OracleComp.EvalDistEq.bind_bind_swap ($ᵗ Secret) (prior setup source ensureInit identityIndex serverKeyId budget) _
  exact swapped.trans (OracleComp.EvalDistEq.bind_bind_swap
    (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected)
    (prior setup source ensureInit identityIndex serverKeyId budget) _)


/-- The one ordinary uniform KEM branch of the actual warm client has its same conditional native result and challenge observation. -/
theorem uniform_source (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform)
    (observe : Secret → RegistrationNativePlatformG3RecordKem.Result source (budget.cap 4 + budget.cap 5) Value Platform → Bool) :
    RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (RegistrationNativePlatformG3RecordKem.program setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer bounds mode adversary budget selected.val previous)) observe budget.create selected false =ᵈ
      conditional setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget selected previous observe := by
  have bill := RegistrationNativePlatformG3RecordKem.resource_bounds setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget bounded selected.val previous
  exact uniform_of_bounds setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous observe bill.1 bill.2

end BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniformSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniformSource.reference_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniformSource.reference_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniformSource.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniformSource.uniform_source
