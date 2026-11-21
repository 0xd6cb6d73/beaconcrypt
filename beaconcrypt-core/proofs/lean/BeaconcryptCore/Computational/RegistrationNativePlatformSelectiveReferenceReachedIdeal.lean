-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeIdeal
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativeLorStartup
import BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView

/-! The same genuine reference program has its ideal baseline at every reached cursor, control and private interpreter state. This permits an explicit reduction-owned sampling prefix without resetting the cache or assuming a sampling/runtime state identity. Broad LR designation still needs the separate hidden-test attachment. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceReachedIdeal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)
open RegistrationNativePlatformSelectiveEntropyStartup (referenceProgram referenceStage)
open PqxdhRecordLiftIdeal (ctxInterpreter)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)

variable (initialShell : CborRecordWorldClient.Shell) (initialControl : PqxdhRecordLiftProtocol.Control n)
    (initialSecret : PqxdhRecordLiftIdeal.CtxPrivate n)

/-- The literal current source-reference program, with its genuine startup, in the all-random record package. -/
noncomputable def run (route : RawCtxServerRouting.SenderDecoder) :
    ProbComp (RegistrationNativeRecordPackage.View n (State n KemSK ProviderState Platform source) Value) :=
  (fun result => RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) result.2.base.produced) <$>
    CborRawRecordOriginFlatten.interpret (ctxInterpreter (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec (canonicalWire wire)))
      (RegistrationNativeWire.ledgerCodec (canonicalWire wire)) route
      (referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        ensureInit identityIndex serverKeyId previous privateBefore bounds .P adversary)
      initialShell initialControl initialSecret

/-- The original native test bit is fair for the exact native canonical observer with physical hidden tests. -/
theorem lor (route : RawCtxServerRouting.SenderDecoder) (budget : PqxdhDeploymentInterface.Budget)
    (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) :
    𝒟[RegistrationNativeLorEntropy.winningView setup.source.crypto (canonicalWire wire) serverKeyId budget filter guess target <$>
      run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds adversary initialShell initialControl initialSecret route] {true} =
      2⁻¹ * 𝒟[RegistrationNativeLorEntropy.eligibleView setup.source.crypto (canonicalWire wire) serverKeyId budget filter target <$>
        run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds adversary initialShell initialControl initialSecret route] {true} := by
  simp only [run, Functor.map_map,
    ← prEvent_eq_evalDist_singleton _ true, referenceProgram,
    CborRawRecordOriginFlatten.interpret_bind]
  apply RegistrationNativeLorStartup.bind_half
  rintro ⟨⟨⟨initialized, shell⟩, control⟩, secret⟩ _
  cases initialized with
  | none => simp [CborRawRecordOriginFlatten.interpret_pure, RegistrationNativeLorEntropy.winningView,
      RegistrationNativeLorEntropy.eligibleView, RegistrationNativeRecordPackage.nativeView]
  | some born =>
      have fair := RegistrationNativePlatformGatedNativeIdeal.lor setup (canonicalWire wire) route
        (RegistrationNativePlatformSelectiveEntropyQuery.environment setup checks (canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none))
        (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount))
        serverKeyId bounds budget (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩)
        filter guess target born.created ((born.native.frontend,previous),privateBefore) shell control secret
      simpa only [referenceStage, ← prEvent_eq_evalDist_singleton _ true, prEvent_map,
        RegistrationNativePlatformGatedNativeEntropy.run, Functor.map_map,
        RegistrationNativeLorEntropy.winning, RegistrationNativeLorEntropy.eligible] using fair

/-- Native selector-weighted fresh guessing averages the genuine startup and retains one same-run selector probability. -/
theorem fresh_bytes (route : RawCtxServerRouting.SenderDecoder) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : RegistrationNativeCanonicalSelector.Target budget) :
    𝒟[RegistrationNativeWeightedRecordView.winning setup.source.crypto (canonicalWire wire) serverKeyId budget claim target <$>
      run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds adversary initialShell initialControl initialSecret route] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[RegistrationNativeWeightedRecordView.selection setup.source.crypto (canonicalWire wire) serverKeyId budget claim target <$>
          run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds adversary initialShell initialControl initialSecret route] {true} := by
  simp only [run, Functor.map_map,
    ← prEvent_eq_evalDist_singleton _ true, referenceProgram,
    CborRawRecordOriginFlatten.interpret_bind]
  apply RegistrationNativeWeightedStartup.bind_weighted
  rintro ⟨⟨⟨initialized, shell⟩, control⟩, secret⟩ _
  cases initialized with
  | none => simp [CborRawRecordOriginFlatten.interpret_pure, RegistrationNativeWeightedRecordView.winning,
      RegistrationNativeWeightedRecordView.selection, RegistrationNativeSelectedRecordTrace.viewSelected,
      RegistrationNativeSelectedRecordTrace.outcomeSelected, RegistrationNativeRecordPackage.nativeView]
  | some born =>
      have bound := RegistrationNativePlatformGatedNativeIdeal.fresh_bytes setup (canonicalWire wire) route
        (RegistrationNativePlatformSelectiveEntropyQuery.environment setup checks (canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none))
        (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount))
        serverKeyId bounds budget (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩)
        claim target born.created ((born.native.frontend,previous),privateBefore) shell control secret
      simpa only [referenceStage, ← prEvent_eq_evalDist_singleton _ true, prEvent_map,
        RegistrationNativePlatformGatedNativeEntropy.run, Functor.map_map,
        ← RegistrationNativeWeightedRecordView.native_winning,
        ← RegistrationNativeWeightedRecordView.native_selection] using bound

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceReachedIdeal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceReachedIdeal.lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceReachedIdeal.lor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceReachedIdeal.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceReachedIdeal.fresh_bytes
