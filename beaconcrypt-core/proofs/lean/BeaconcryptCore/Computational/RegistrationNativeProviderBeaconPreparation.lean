-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePhase

/-! Selected and ordinary Beacon preparation share the actual provider source. Preparation itself contains no KEM operation, so its exact returned reference and freshly stored root reuse the literal native source equations while retaining the entire provider state. The preceding collection remains provider-dependent. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPreparation
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderCallbacks (NativeState implementation)
open RegistrationNativeOrdinaryFinishSourcePhase (adapt)
open RegistrationNativeProviderBuildCaps (IsLocalKem)
open RegistrationBeaconReferenceNativePreparation (restored)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}

abbrev Frame (n : Nat) (KemSK ProviderState : Type) :=
  RegistrationNativeOrdinaryFinishSourceFrame.Frame n KemSK × ProviderState

def drop (before : NativeState n KemSK ProviderState) : Frame n KemSK ProviderState :=
  (RegistrationNativeOrdinaryFinishSourceFrame.drop before.1, before.2)

theorem client_free (setup : Setup base KemSK) (localScalar : Option ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) :
    (simulateQ (adapt setup localScalar)
      (simulateQ (RegistrationBeaconReferenceCompiler.prepare (n := n) (KemSK := KemSK))
        (RegistrationBeaconReferenceRoot.client authenticated pending))).IsQueryBoundP IsLocalKem 0 := by
  cases localScalar with
  | none =>
      simp only [adapt, RegistrationBeaconReferenceRoot.client,
        bind_pure_comp, simulateQ_map, simulateQ_spec_query, RegistrationBeaconReferenceCompiler.prepare,
        QueryImpl.id'_apply, isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsLocalKem]
      exact False.elim
  | some scalar =>
      simp only [adapt, RegistrationBeaconReferenceRoot.client, bind_pure_comp,
        simulateQ_map, simulateQ_spec_query, RegistrationBeaconReferenceCompiler.prepare,
        RegistrationNativePublicOwners.ordinary]
      cases translated : RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar
          (RegistrationNativeRelatedRoot.pinnedBeaconMessage pending.collected) <;>
        simp only [isQueryBoundP_map_iff, isQueryBoundP_pure, isQueryBoundP_query_iff, IsLocalKem]
      exact False.elim

/-- Reconstructed preparation uses the selected private scalar or the owner's literal ordinary scalar and preserves the full provider frame. -/
theorem client_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (provider : Provider KemSK ProviderState) (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (before : NativeState n KemSK ProviderState) :
    (fun result => (restored result.2.1.extra.1 authenticated result.1, drop result.2)) <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar provider false)
        (simulateQ (adapt setup localScalar)
          (simulateQ RegistrationBeaconReferenceCompiler.prepare
            (RegistrationBeaconReferenceRoot.client authenticated pending)))).run before =
      (fun result => (result, drop before)) <$>
        simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed
          (localScalar.getD selectedScalar))
          (RegistrationNativeBeaconRootSource.client authenticated pending) := by
  rw [RegistrationNativeProviderCallbacks.program_free setup wire route sign seed selectedScalar provider false _
    (client_free setup localScalar authenticated pending) before]
  simp only [Functor.map_map, drop]
  cases localScalar with
  | none =>
      simp only [adapt, simulateQ_id', Option.getD_none]
      have old := RegistrationNativeOrdinaryFinishSourceSelectedPreparation.client_source setup wire route sign seed
        selectedScalar authenticated pending before.1
      have framed := congrArg (fun distribution => (fun result => (result.1, (result.2, before.2))) <$> distribution) old
      simpa only [Functor.map_map, RegistrationNativeOrdinaryFinishSourceFrame.drop] using framed
  | some scalar =>
      have old := RegistrationNativeOrdinaryFinishSourcePreparation.client_source setup wire route sign seed
        selectedScalar scalar authenticated pending before.1
      have framed := congrArg (fun distribution => (fun result => (result.1, (result.2, before.2))) <$> distribution) old
      simpa only [adapt, Option.getD_some, Functor.map_map,
        RegistrationNativeOrdinaryFinishSourceFrame.drop] using framed

/-- A successful prepared capability names its actual newly recorded root, independently of the previous memo or provider state. -/
theorem client_prepared (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (localScalar : Option ScalarBytes)
    (provider : Provider KemSK ProviderState) (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (before after : NativeState n KemSK ProviderState) (ready : RegistrationBeaconReferenceRoot.Ready)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (implementation setup wire route sign seed selectedScalar provider false)
        (simulateQ (adapt setup localScalar)
          (simulateQ RegistrationBeaconReferenceCompiler.prepare
            (RegistrationBeaconReferenceRoot.client authenticated pending)))).run before)) :
    ∃ root, after.1.extra.1 ready.reference = some root := by
  rw [RegistrationNativeProviderCallbacks.program_free setup wire route sign seed selectedScalar provider false _
    (client_free setup localScalar authenticated pending) before, support_map] at supported
  obtain ⟨inner, possible, equal⟩ := supported
  have reached : inner.2 = after.1 := congrArg (fun result => result.2.1) equal
  have output : inner.1 = .ok (some ready) := congrArg Prod.fst equal
  change (inner.1, inner.2) ∈ support _ at possible
  rw [reached, output] at possible
  cases localScalar with
  | none =>
      simp only [adapt, simulateQ_id'] at possible
      exact RegistrationNativeOrdinaryFinishSourceSelectedPreparation.client_prepared setup wire route sign seed
        selectedScalar authenticated pending before.1 after.1 ready possible
  | some scalar =>
      exact RegistrationNativeOrdinaryFinishSourcePreparation.client_prepared setup wire route sign seed
        selectedScalar scalar authenticated pending before.1 after.1 ready possible

end BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPreparation.client_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPreparation.client_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPreparation.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPreparation.client_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPreparation.client_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconPreparation.client_prepared
