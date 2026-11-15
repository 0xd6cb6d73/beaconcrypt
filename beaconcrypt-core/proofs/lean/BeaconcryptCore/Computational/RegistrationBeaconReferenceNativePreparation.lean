-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter

/-! Native selected-Beacon preparation uses the actual reached related-root reply. The private memo reconstructs the source root controller, while the executable ready value contains only cleared public metadata and its reference. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePreparation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationBeaconReferenceNativeInterpreter (State implementation)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def restored (memo : RegistrationNativeReferenceInterpreter.State)
    (authenticated : registration.AuthenticatedResponse) :
    RustM (Option RegistrationBeaconReferenceRoot.Ready) → RustM agreement.AgreementEffect
  | .ok (some ready) => match memo ready.reference with
      | none => .ok (RegistrationBeaconAgreementRoot.rejected authenticated)
      | some root => .ok (.BeaconComplete (RegistrationBeaconReferenceRoot.atRoot ready root))
  | result => RegistrationBeaconReferenceRoot.restored authenticated none result

/-- The single native preparation stores the actual root before exposing its reference; reconstruction therefore uses that reply rather than any preexisting memo entry. -/
theorem client_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (before : State n KemSK mlSource) :
    (fun result => (restored result.2.1 authenticated result.1, result.2.2.2)) <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (simulateQ RegistrationBeaconReferenceCompiler.prepare
          (RegistrationBeaconReferenceRoot.client authenticated pending))).run before =
      (fun result => (result.1, before.2.2)) <$>
        (simulateQ (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh created.seed scalar)
          (RegistrationNativeBeaconRootSource.client authenticated pending)).run before.2.1 := by
  simp only [RegistrationBeaconReferenceRoot.client, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    RegistrationBeaconReferenceCompiler.prepare]
  rw [StateT.run_map, RegistrationBeaconReferenceNativeInterpreter.prepare]
  simp only [bind_pure_comp, Functor.map_map,
    RegistrationNativeBeaconRootSource.client, RegistrationNativeBeaconRootSource.root,
    simulateQ_map, simulateQ_spec_query, StateT.run_map]
  congr 1
  funext result
  rcases result with ⟨root, family⟩
  cases root with
  | none => rfl
  | some root =>
      simp only [Option.map_some, restored, Function.update_self]
      rfl

/-- A successful ready value always names the root just returned by its actual preparation, even if the memo previously contained a different entry. -/
theorem client_prepared (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (before after : State n KemSK mlSource) (ready : RegistrationBeaconReferenceRoot.Ready)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (implementation setup checks wire representation created scalar credential)
        (simulateQ RegistrationBeaconReferenceCompiler.prepare
          (RegistrationBeaconReferenceRoot.client authenticated pending))).run before)) :
    ∃ root, after.1 ready.reference = some root := by
  simp only [RegistrationBeaconReferenceRoot.client, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    RegistrationBeaconReferenceCompiler.prepare] at supported
  rw [StateT.run_map, RegistrationBeaconReferenceNativeInterpreter.prepare] at supported
  simp only [bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨⟨root, family⟩, _reached, equal⟩ := supported
  cases root with
  | none => cases equal
  | some root =>
      cases equal
      exact ⟨root, Function.update_self _ _ _⟩

/-- All ordinary collection effects pass through the actual shared native World and private KEM pool without preparing a root. -/
theorem collect_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : State n KemSK mlSource) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run env)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          ((RegistrationBeaconReferenceCompiler.trustedCollect setup owner oneTime authenticated).run env)).run before.2.2 := by
  rw [← RegistrationBeaconReferenceCallbacks.collect_lift]
  exact RegistrationBeaconReferenceNativeInterpreter.trusted_program setup checks wire representation created scalar credential _ before

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePreparation.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePreparation.client_source
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePreparation.client_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePreparation.client_prepared
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePreparation.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePreparation.collect_source
