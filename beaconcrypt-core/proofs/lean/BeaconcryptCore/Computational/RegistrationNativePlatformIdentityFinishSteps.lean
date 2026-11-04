-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord
import BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityAuthenticationSource

/-! Corrected native response finishing retains opaque Ed authentication/agreement callbacks and consumes InitSent before admission. The literal source byte copy and assigned-ID installation follow actual first-record opening. Every failure and reached owner/Env/cache state is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityFrontend (Owner)
open RegistrationNativeIdentityFinishRecord (abort_value_source abort_value_keeps)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def afterAgreement (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) : RustM agreement.AgreementEffect →
      RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativeIdentityFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeIdentityFrontend.abort owner *> pure .div
  | .ok (.BeaconComplete completed) => do
      let opened ← simulateQ (RegistrationNativeIdentityFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin completed)
      RegistrationNativePlatformIdentityFinishRecord.after index owner opened
  | .ok _ => RegistrationNativeIdentityFrontend.abort owner *> pure (.ok none)

noncomputable def oldAfterAgreement (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) : RustM agreement.AgreementEffect →
      RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
  | .ok (.BeaconComplete completed) => do
      let opened ← simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin completed)
      RegistrationNativePlatformIdentityFinishRecord.original index owner opened
  | .ok _ => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)

theorem agreement_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (seed : IdentitySeed)
    (reply : RustM agreement.AgreementEffect) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (afterAgreement setup wire index owner reply)
      (oldAfterAgreement setup wire index (RegistrationNativeIdentityFrontend.restore seed owner) reply) := by
  cases reply with
  | fail error | div => exact abort_value_source setup checks representation created seeds owner seed _
  | ok effect => cases effect with
    | Rejected previous | ConvertPublic pending | ConvertSecret pending | GenerateEphemeral pending | Encapsulate pending
      | Decapsulate pending | Dh pending | RootKdf pending | ServerComplete completed =>
        exact abort_value_source setup checks representation created seeds owner seed _
    | BeaconComplete completed =>
        exact related_bind setup checks representation created seeds _ _ _ _
          (RegistrationNativeIdentityRecordSource.program_source setup checks representation created seeds wire _)
          (RegistrationNativeIdentityRecordSource.program_keeps setup checks representation created wire _)
          (RegistrationNativePlatformIdentityFinishRecord.after_source setup checks representation created seeds index owner seed)

theorem agreement_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (reply : RustM agreement.AgreementEffect) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (afterAgreement setup wire index owner reply) := by
  cases reply with
  | fail error | div => exact abort_value_keeps setup checks representation created owner _
  | ok effect => cases effect with
    | Rejected previous | ConvertPublic pending | ConvertSecret pending | GenerateEphemeral pending | Encapsulate pending
      | Decapsulate pending | Dh pending | RootKdf pending | ServerComplete completed =>
        exact abort_value_keeps setup checks representation created owner _
    | BeaconComplete completed =>
        exact keeps_bind setup checks representation created _ _
          (RegistrationNativeIdentityRecordSource.program_keeps setup checks representation created wire _)
          (RegistrationNativePlatformIdentityFinishRecord.after_keeps setup checks representation created index owner)

noncomputable def afterAuthentication (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RustM RegistrationResponseExecutor.ResponseResult →
      RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativeIdentityFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeIdentityFrontend.abort owner *> pure .div
  | .ok (.Err _) => RegistrationNativeIdentityFrontend.abort owner *> pure (.ok none)
  | .ok (.Ok accepted) => do
      let agreed ← simulateQ (RegistrationNativeIdentityFrontend.agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon accepted)
      afterAgreement setup wire index owner agreed

noncomputable def oldAfterAuthentication (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RustM RegistrationResponseExecutor.ResponseResult →
      RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
  | .ok (.Err _) => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)
  | .ok (.Ok accepted) => do
      let agreed ← simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon accepted)
      oldAfterAgreement setup wire index owner agreed

theorem authentication_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (seed : IdentitySeed)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (found : seeds[owner.identity.handle]? = some seed)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (afterAuthentication setup wire index owner oneTime reply)
      (oldAfterAuthentication setup wire index (RegistrationNativeIdentityFrontend.restore seed owner) oneTime reply) := by
  cases reply with
  | fail error | div => exact abort_value_source setup checks representation created seeds owner seed _
  | ok result => cases result with
    | Err previous => exact abort_value_source setup checks representation created seeds owner seed _
    | Ok accepted =>
        exact related_bind setup checks representation created seeds _ _ _ _
          (RegistrationNativeIdentityAgreementSource.program_source setup checks representation created seeds owner seed oneTime found _)
          (RegistrationNativeIdentityAgreementSource.program_keeps setup checks representation created owner oneTime _)
          (agreement_source setup checks representation created seeds wire index owner seed)

theorem authentication_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (afterAuthentication setup wire index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact abort_value_keeps setup checks representation created owner _
  | ok result => cases result with
    | Err previous => exact abort_value_keeps setup checks representation created owner _
    | Ok accepted =>
        exact keeps_bind setup checks representation created _ _
          (RegistrationNativeIdentityAgreementSource.program_keeps setup checks representation created owner oneTime _)
          (agreement_keeps setup checks representation created wire index owner)

noncomputable def begin (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) :=
  match pending.aborted_state with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok aborted => do
      RegistrationNativeIdentityFrontend.updatePhase index (.aborted aborted)
      let authenticated ← simulateQ (RegistrationNativeIdentityFrontend.authentication setup source)
        (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))
      afterAuthentication setup wire index owner oneTime authenticated

noncomputable def oldBegin (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket) :
    RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) :=
  match pending.aborted_state with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok aborted => do
      RegistrationNativeBeaconFrontend.updatePhase index (.aborted aborted)
      let authenticated ← simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
        (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))
      oldAfterAuthentication setup wire index owner oneTime authenticated

/-- InitSent is terminally consumed before packet admission, then every actual authentication/agreement/opening/install continuation agrees with the original native source. -/
theorem begin_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (seed : IdentitySeed)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) (found : seeds[owner.identity.handle]? = some seed) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (begin setup wire index owner pending oneTime packet)
      (oldBegin setup wire index (RegistrationNativeIdentityFrontend.restore seed owner) pending oneTime packet) := by
  cases moved : pending.aborted_state with
  | fail error | div => simpa only [begin, oldBegin, moved] using related_pure setup checks representation created seeds _
  | ok aborted =>
      simp only [begin, oldBegin, moved]
      exact related_bind setup checks representation created seeds _ _ _ _
        (RegistrationNativeIdentityBundleSource.phase_source setup checks representation created seeds index (.aborted aborted))
        (RegistrationNativeIdentityBundleSource.phase_keeps setup checks representation created index (.aborted aborted))
        (fun _ => related_bind setup checks representation created seeds _ _ _ _
          (RegistrationNativeIdentityAuthenticationSource.program_source setup checks representation created seeds _)
          (RegistrationNativeIdentityAuthenticationSource.program_keeps setup checks representation created _)
          (authentication_source setup checks representation created seeds wire index owner seed oneTime found))

theorem begin_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (begin setup wire index owner pending oneTime packet) := by
  cases moved : pending.aborted_state with
  | fail error | div => simpa only [begin, moved] using keeps_pure setup checks representation created _
  | ok aborted =>
      simp only [begin, moved]
      exact keeps_bind setup checks representation created _ _
        (RegistrationNativeIdentityBundleSource.phase_keeps setup checks representation created index (.aborted aborted))
        (fun _ => keeps_bind setup checks representation created _ _
          (RegistrationNativeIdentityAuthenticationSource.program_keeps setup checks representation created _)
          (authentication_keeps setup checks representation created wire index owner oneTime))

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.agreement_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.agreement_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.agreement_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.authentication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.authentication_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.authentication_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.authentication_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.begin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.begin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.begin_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps.begin_keeps
