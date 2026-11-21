-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishSteps

/-! The corrected assigned-ID native finish has the same complete opaque-identity execution, including inactive phases, failed authentication/agreement/record opening and reached native installation. All private source rows interpret existing handles and stay absent from the executable client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityFrontend (Owner)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def start (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (packet : Option registration.ResponsePacket) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) :=
  match owner.phase with
  | .initSent pending oneTime => RegistrationNativePlatformIdentityFinishSteps.begin setup wire index owner pending oneTime packet
  | _ => pure (.ok none)

noncomputable def original (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (packet : Option registration.ResponsePacket) :
    RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) :=
  match owner.phase with
  | .initSent pending oneTime => RegistrationNativePlatformIdentityFinishSteps.oldBegin setup wire index owner pending oneTime packet
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
        RegistrationNativePlatformIdentityFinishSteps.begin_source setup checks representation created seeds wire index owner seed pending oneTime packet found
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
        RegistrationNativePlatformIdentityFinishSteps.begin_keeps setup checks representation created wire index owner pending oneTime packet
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simpa only [start, phase] using
        (keeps_pure (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
          (.ok none : RustM (Option Pqxdh.Bytes)))

noncomputable def finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let owners ← get
  match owners[index]? with
  | none => pure (.ok none)
  | some owner => start setup wire index owner packet

private theorem new_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : Owner source) (current : RegistrationNativeIdentityFrontend.State source)
    (found : current[index]? = some owner) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (packet : Option registration.ResponsePacket) :
    ((finish (n := n) setup source wire index packet).run current).run env =
      ((start setup wire index owner packet).run current).run env := by
  simp only [finish, StateT.run_bind, StateT.run_get, pure_bind, found]

private theorem old_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (current : RegistrationNativeBeaconFrontend.State source)
    (found : current[index]? = some owner) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (packet : Option registration.ResponsePacket) :
    ((RegistrationNativePlatformBeaconFinish.finish (n := n) setup source wire index packet).run current).run env =
      ((original setup wire index owner packet).run current).run env := by
  cases phase : owner.phase <;>
    simp only [RegistrationNativePlatformBeaconFinish.finish, RegistrationNativePlatformBeaconFinish.finishWith,
      RegistrationNativePlatformBeaconFinish.afterAuthenticationWith, original, RegistrationNativePlatformIdentityFinishSteps.oldBegin,
      RegistrationNativePlatformIdentityFinishSteps.oldAfterAuthentication, RegistrationNativePlatformIdentityFinishSteps.oldAfterAgreement,
      RegistrationNativePlatformIdentityFinishRecord.original, StateT.run_bind, StateT.run_get, pure_bind, found, phase]
  all_goals rfl

/-- The whole actual finishing operation equals the original native source operation after private credential realization; all authentication/agreement/opening failures keep their reached effects. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (before : NewState n KemSK Auxiliary source) (prior : before.2.identities.seeds = seeds)
    (owned : RegistrationNativeIdentityRealization.Owned setup.joint before.2.identities before.1.1) :
    Prod.map id (view seeds) <$>
      runNew setup checks representation created (finish setup source wire index packet) before =
      runOld setup checks representation created (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet) (view seeds before) := by
  cases selected : before.1.1[index]? with
  | none =>
      simp only [runNew, runOld, finish, RegistrationNativePlatformBeaconFinish.finish, RegistrationNativePlatformBeaconFinish.finishWith,
        StateT.run_bind, StateT.run_get, pure_bind, view, RegistrationNativeIdentityRealization.owners,
        List.getElem?_map, selected, Option.map_none, StateT.run_pure, simulateQ_pure, map_pure,
        Prod.map_def, id_eq]
  | some current =>
      obtain ⟨seed, receipt⟩ := owned current (List.mem_of_getElem? selected)
      have found : seeds[current.identity.handle]? = some seed := by rw [← prior]; exact receipt.1
      have nativeOwner : RegistrationNativeIdentityRealization.owner ⟨seeds, []⟩ current =
          RegistrationNativeIdentityFrontend.restore seed current := by
        simp only [RegistrationNativeIdentityRealization.owner,
          RegistrationNativeIdentityRealization.seed_found ⟨seeds, []⟩ current.identity seed found]
      have nativeFound : (view seeds before).1.1[index]? =
          some (RegistrationNativeIdentityFrontend.restore seed current) := by
        simp only [view, RegistrationNativeIdentityRealization.owners, List.getElem?_map,
          selected, Option.map_some, nativeOwner]
      have actual := RegistrationNativePlatformIdentityFinishRun.start_source setup checks representation created seeds
        wire index current seed packet found before prior
      unfold runNew runOld
      rw [RegistrationNativePlatformIdentityFinishRun.new_run setup wire index current before.1.1 selected before.1.2 packet,
        RegistrationNativePlatformIdentityFinishRun.old_run setup wire index
          (RegistrationNativeIdentityFrontend.restore seed current) (view seeds before).1.1 nativeFound (view seeds before).1.2 packet]
      exact actual

/-- Complete actual finishing execution preserves the existing private identity prefix on every return path. -/
theorem finish_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
      (finish setup source wire index packet) := by
  intro before result supported
  cases selected : before.1.1[index]? with
  | none =>
      simp only [runNew, finish, StateT.run_bind, StateT.run_get,
        pure_bind, selected, StateT.run_pure, simulateQ_pure, map_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some current =>
      have same : runNew setup checks representation created
          (finish setup source wire index packet) before =
          runNew setup checks representation created (start setup wire index current packet) before := by
        unfold runNew
        rw [RegistrationNativePlatformIdentityFinishRun.new_run setup wire index current before.1.1 selected before.1.2 packet]
      rw [same] at supported
      exact RegistrationNativePlatformIdentityFinishRun.start_keeps setup checks representation created wire index current packet before result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun.start_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun.start_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun.start_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun.start_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun.finish_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun.finish_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun.finish_keeps
