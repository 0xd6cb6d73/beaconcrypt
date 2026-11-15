-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityFinishSteps

/-! Actual native phase dispatch selects the retained InitSent capability and consumes it before optional packet admission. The source correspondence includes inactive phases and all native errors; no pin equality, caller-created binding or reset kernel is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityFrontend (Owner)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def start (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (packet : Option registration.ResponsePacket) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) :=
  match owner.phase with
  | .initSent pending oneTime => RegistrationNativeIdentityFinishSteps.begin setup wire index owner pending oneTime packet
  | _ => pure (.ok none)

noncomputable def original (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (packet : Option registration.ResponsePacket) :
    RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) :=
  match owner.phase with
  | .initSent pending oneTime => RegistrationNativeIdentityFinishSteps.oldBegin setup wire index owner pending oneTime packet
  | _ => pure (.ok none)

theorem start_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (seed : PqxdhJointIdentity.IdentitySeed)
    (packet : Option registration.ResponsePacket) (found : seeds[owner.identity.handle]? = some seed) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (start setup wire index owner packet) (original setup wire index (RegistrationNativeIdentityFrontend.restore seed owner) packet) := by
  cases phase : owner.phase with
  | initSent pending oneTime =>
      simpa only [start, original, RegistrationNativeIdentityFrontend.restore, phase] using
        RegistrationNativeIdentityFinishSteps.begin_source setup checks representation created seeds wire index owner seed pending oneTime packet found
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simpa only [start, original, RegistrationNativeIdentityFrontend.restore, phase] using
        (related_pure (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
          (.ok none : RustM (Option Pqxdh.Bytes)))

theorem start_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (packet : Option registration.ResponsePacket) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (start setup wire index owner packet) := by
  cases phase : owner.phase with
  | initSent pending oneTime =>
      simpa only [start, phase] using
        RegistrationNativeIdentityFinishSteps.begin_keeps setup checks representation created wire index owner pending oneTime packet
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simpa only [start, phase] using
        (keeps_pure (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
          (.ok none : RustM (Option Pqxdh.Bytes)))

theorem new_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : Owner source) (current : RegistrationNativeIdentityFrontend.State source)
    (found : current[index]? = some owner) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (packet : Option registration.ResponsePacket) :
    ((RegistrationNativeIdentityFrontend.finish (n := n) setup source wire index packet).run current).run env =
      ((start setup wire index owner packet).run current).run env := by
  cases phase : owner.phase <;>
    simp only [RegistrationNativeIdentityFrontend.finish, start, RegistrationNativeIdentityFinishSteps.begin,
      RegistrationNativeIdentityFinishSteps.afterAuthentication, RegistrationNativeIdentityFinishSteps.afterAgreement,
      RegistrationNativeIdentityFinishRecord.after, StateT.run_bind, StateT.run_get, pure_bind, found, phase]
  all_goals rfl

theorem old_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (current : RegistrationNativeBeaconFrontend.State source)
    (found : current[index]? = some owner) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (packet : Option registration.ResponsePacket) :
    ((RegistrationNativeBeaconFrontend.finish (n := n) setup source wire index packet).run current).run env =
      ((original setup wire index owner packet).run current).run env := by
  cases phase : owner.phase <;>
    simp only [RegistrationNativeBeaconFrontend.finish, original, RegistrationNativeIdentityFinishSteps.oldBegin,
      RegistrationNativeIdentityFinishSteps.oldAfterAuthentication, RegistrationNativeIdentityFinishSteps.oldAfterAgreement,
      RegistrationNativeIdentityFinishRecord.original, StateT.run_bind, StateT.run_get, pure_bind, found, phase]
  all_goals rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch.start_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch.start_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch.start_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch.start_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch.new_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch.new_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch.old_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch.old_run
