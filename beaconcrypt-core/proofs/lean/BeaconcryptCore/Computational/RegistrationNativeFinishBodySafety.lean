-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeFinishFactor
import BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe
import BeaconcryptCore.Refinement.AdapterPublicFinishWorld
/-! The full logged native finish cryptographic body preserves every World owner slot. This follows from the actual lifted authentication, agreement and first-record handlers, with optional outcomes and complete primitive effects retained. The source InitSent material relation then derives post-body readiness; successful terminal installation is not an assumption. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (M Owner)
open RegistrationNativeBeaconPrefixSafe (Work)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

theorem after_agreement (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (result : RustM agreement.AgreementEffect) :
    Work (RegistrationNativeBeaconPhaseCommutation.lift (source := source) (RegistrationNativeFinishFactor.afterAgreement (n := n) (Auxiliary := Auxiliary) setup wire result)) := by
  cases result with
  | fail error | div => simpa only [RegistrationNativeFinishFactor.afterAgreement, RegistrationNativeBeaconPhaseCommutation.lift_pure] using (RegistrationNativeBeaconPrefixSafe.pure_safe (source := source) (Auxiliary := Auxiliary) (n := n) (KemSK := KemSK) _)
  | ok phase => cases phase with
    | BeaconComplete agreed =>
        simp only [RegistrationNativeFinishFactor.afterAgreement, map_eq_bind_pure_comp, RegistrationNativeBeaconPhaseCommutation.lift_bind]
        have leaves := funext (RegistrationNativeBeaconPhaseCommutation.record_lift (n := n) (source := source) (Auxiliary := Auxiliary) setup wire)
        rw [← RegistrationNativeBeaconPhaseCommutation.simulate_lift, ← leaves]
        exact RegistrationNativeBeaconPrefixSafe.bind_safe _ _
          (RegistrationNativeBeaconPrefixSafe.simulate_safe _ (RegistrationNativeBeaconPrefixSafe.record_safe setup wire) _)
          (fun result => by simpa only [Function.comp_apply, RegistrationNativeBeaconPhaseCommutation.lift_pure] using RegistrationNativeBeaconPrefixSafe.pure_safe (RegistrationNativeFinishFactor.collapse result))
    | _ => simpa only [RegistrationNativeFinishFactor.afterAgreement, RegistrationNativeBeaconPhaseCommutation.lift_pure] using (RegistrationNativeBeaconPrefixSafe.pure_safe (source := source) (Auxiliary := Auxiliary) (n := n) (KemSK := KemSK) _)

theorem accepted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    Work (RegistrationNativeBeaconPhaseCommutation.lift (source := source) (RegistrationNativeFinishFactor.accepted (n := n) (Auxiliary := Auxiliary) setup wire owner scalar authenticated)) := by
  unfold RegistrationNativeFinishFactor.accepted
  rw [RegistrationNativeBeaconPhaseCommutation.lift_bind]
  have leaves := funext (RegistrationNativeBeaconPhaseCommutation.agreement_lift (n := n) (Auxiliary := Auxiliary) setup owner scalar)
  rw [← RegistrationNativeBeaconPhaseCommutation.simulate_lift, ← leaves]
  exact RegistrationNativeBeaconPrefixSafe.bind_safe _ _
    (RegistrationNativeBeaconPrefixSafe.simulate_safe _ (RegistrationNativeBeaconPrefixSafe.agreement_safe setup owner scalar) _)
    (after_agreement setup wire)

theorem after_authentication (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Work (RegistrationNativeBeaconPhaseCommutation.lift (source := source) (RegistrationNativeFinishFactor.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire owner scalar reply)) := by
  cases reply with
  | fail error | div => simpa only [RegistrationNativeFinishFactor.afterAuthentication, RegistrationNativeBeaconPhaseCommutation.lift_pure] using (RegistrationNativeBeaconPrefixSafe.pure_safe (source := source) (Auxiliary := Auxiliary) (n := n) (KemSK := KemSK) _)
  | ok result => cases result with
    | Err control => simpa only [RegistrationNativeFinishFactor.afterAuthentication, RegistrationNativeBeaconPhaseCommutation.lift_pure] using (RegistrationNativeBeaconPrefixSafe.pure_safe (source := source) (Auxiliary := Auxiliary) (n := n) (KemSK := KemSK) _)
    | Ok authenticated => exact accepted setup wire owner scalar authenticated

theorem body (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) :
    Work (RegistrationNativeBeaconPhaseCommutation.lift (source := source) (RegistrationNativeFinishFactor.body (n := n) (Auxiliary := Auxiliary) setup wire pending packet owner scalar)) := by
  unfold RegistrationNativeFinishFactor.body
  rw [RegistrationNativeBeaconPhaseCommutation.lift_bind]
  have leaves := funext (RegistrationNativeBeaconPhaseCommutation.authentication_lift (n := n) (source := source) (Auxiliary := Auxiliary) setup)
  rw [← RegistrationNativeBeaconPhaseCommutation.simulate_lift, ← leaves]
  exact RegistrationNativeBeaconPrefixSafe.bind_safe _ _
    (RegistrationNativeBeaconPrefixSafe.simulate_safe _ (RegistrationNativeBeaconPrefixSafe.authentication_safe setup) _)
    (after_authentication setup wire owner scalar)

theorem body_owners (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (Option registration.CompletedBeacon) × RegistrationNativeExperiment.State n KemSK source)
    (reached : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconPhaseCommutation.lift (RegistrationNativeFinishFactor.body setup wire pending packet owner scalar))).run before)) :
    result.2.server.world.world.1.owners = before.server.world.world.1.owners :=
  RegistrationNativeBeaconPrefixSafe.lower_owners setup checks representation created _ (body setup wire pending packet owner scalar) before result reached

theorem raw_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    ((RegistrationNativeFinishFactor.body (n := n) setup wire pending packet owner scalar).run env).AllQueriesSatisfy (RegistrationNativeWorldOwnerFrame.Safe (KemSK := KemSK)) := by
  have allowed := body (n := n) setup wire pending packet owner scalar ([] : List (Owner source)) env
  rw [RegistrationNativeBeaconPhaseCommutation.lift_run] at allowed
  exact (isQueryBound_map_iff _ _ _ _ _).mp allowed

theorem raw_owners (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : (RustM (Option registration.CompletedBeacon) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × RegistrationNativeExperiment.State n KemSK source)
    (reached : result ∈ support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
      ((RegistrationNativeFinishFactor.body setup wire pending packet owner scalar).run env)).run before)) :
    result.2.server.world.world.1.owners = before.server.world.world.1.owners :=
  RegistrationNativeWorldOwnerFrame.program setup checks representation created _ (raw_safe setup wire pending packet owner scalar env) before result reached


variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

theorem body_ready (view : BeaconcryptCore.Refinement.AdapterPublicWrapperState.MaterialView source KemSK)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem) (phase : owner.phase = .initSent pending scalar)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (related : BeaconcryptCore.Refinement.AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (packet : core.option.Option registration.ResponsePacket)
    (result : RustM (Option registration.CompletedBeacon) × RegistrationNativeExperiment.State n KemSK source)
    (reached : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconPhaseCommutation.lift (RegistrationNativeFinishFactor.body setup wire pending packet owner scalar))).run before)) :
    PqxdhRecordLiftWorld.BeaconReady result.2.server.world.world.1 owner.worldOwner := by
  have initial := BeaconcryptCore.Refinement.AdapterPublicFinishWorld.initSent_ready view setup.joint before.pool self owner before.server.world.world.1 related pending prekey oneTime kem scalar stored phase
  change result.2.server.world.world.1.owners[owner.worldOwner]? = some (.inactive .initSent)
  rw [body_owners setup checks representation created wire pending packet owner scalar before result reached]
  exact initial


end BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.after_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.after_agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.after_authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.body_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.body_owners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.raw_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.raw_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.raw_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.raw_owners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.body_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety.body_ready
