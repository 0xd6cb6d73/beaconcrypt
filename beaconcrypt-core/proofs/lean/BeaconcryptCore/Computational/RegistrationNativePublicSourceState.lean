-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicInterpreter
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Computational.RegistrationServerMaterialSourceState
import BeaconcryptCore.Computational.RegistrationServerMaterialRoots
import BeaconcryptCore.Computational.RegistrationNativeSourceRoot

/-! Explicit deterministic source reassembly for the mixed reference frontend. Only the private interpretation restores the selected scalar and prepared roots. The source view names its native/coin/record-log erasure; complete signing histories, protocol state, pool and parsed counter remain present. Live roots and source memo correctness are internal invariants to be derived from initialized execution, not public event restrictions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceState
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeReferenceInterpreter (State)
open PqxdhSecretInputKdf (RootOutput)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}

def owner (scalar : PqxdhJointGapDh.ScalarBytes) (before : RegistrationNativePublicOwners.Owner mlSource) :
    RegistrationNativeBeaconFrontend.Owner mlSource :=
  RegistrationBeaconReferenceCompiler.restoreOwner (before.scalar.getD scalar) before.view

def owners (scalar : PqxdhJointGapDh.ScalarBytes) (before : RegistrationNativePublicOwners.State mlSource) :
    RegistrationNativeBeaconFrontend.State mlSource := before.map (owner scalar)

noncomputable def roots (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) : RegistrationServerReferenceRestore.Roots :=
  fun message => (RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message).getD RegistrationBoundKeySchedule.zero

def restore (privateRoots : RegistrationServerReferenceRestore.Roots) (scalar : PqxdhJointGapDh.ScalarBytes)
    (frontend : RegistrationNativePublicFrontend.State mlSource)
    (before : RegistrationNativePublicInterpreter.State n KemSK) : RegistrationNativeExperiment.State n KemSK mlSource :=
  ⟨RegistrationServerMaterialSourceState.restore privateRoots
      (frontend.server, RegistrationWorldAgreementCompiler.join frontend.environment before.world),
    owners scalar frontend.beacons, before.pool, frontend.parsedAccepts⟩

def nativeView (before : RegistrationNativeExperiment.State n KemSK mlSource) : RegistrationNativeExperiment.State n KemSK mlSource :=
  { before with server := RegistrationServerMaterialSourceState.nativeView before.server }

def project (privateRoots : RegistrationServerReferenceRestore.Roots) (scalar : PqxdhJointGapDh.ScalarBytes)
    (frontend : RegistrationNativePublicFrontend.State mlSource)
    (before : RegistrationNativePublicInterpreter.State n KemSK) : RegistrationNativeExperiment.State n KemSK mlSource :=
  nativeView (restore privateRoots scalar frontend before)

def MemoCorrect (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (memo : State) : Prop :=
  ∀ message root, memo message = some root →
    RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message = some root

def Live (frontend : RegistrationNativePublicFrontend.State mlSource)
    (before : RegistrationNativePublicInterpreter.State n KemSK) : Prop :=
  RegistrationServerMaterialRoots.Live frontend.server before.roots

/-- Ordinary scalars restore literally; only the selected absent scalar uses the private challenger value. -/
theorem owner_fields (scalar : PqxdhJointGapDh.ScalarBytes) (before : RegistrationNativePublicOwners.Owner mlSource) :
    (owner scalar before).prekeyScalar = before.scalar.getD scalar ∧
      RegistrationBeaconReferenceCompiler.eraseOwner (owner scalar before) = before.view := by
  exact ⟨rfl, RegistrationBeaconReferenceCompiler.erase_restore _ _⟩

/-- Full native restoration keeps the private pool, exact owner/public fields and actual parsed-attempt counter. -/
theorem restore_fields (privateRoots : RegistrationServerReferenceRestore.Roots) (scalar : PqxdhJointGapDh.ScalarBytes)
    (frontend : RegistrationNativePublicFrontend.State mlSource)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (restore privateRoots scalar frontend before).pool = before.pool ∧
      (restore privateRoots scalar frontend before).parsedAccepts = frontend.parsedAccepts ∧
      (restore privateRoots scalar frontend before).server.world.world.2 = frontend.environment.receipts := ⟨rfl, rfl, rfl⟩

/-- A moved native token's private root is recovered from actual live-session and memo invariants. -/
theorem live_root (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (frontend : RegistrationNativePublicFrontend.State mlSource)
    (before : RegistrationNativePublicInterpreter.State n KemSK) (live : Live frontend before)
    (correct : MemoCorrect setup seed scalar before.roots) (handle : Nat) (ready : RegistrationServerReferenceRoot.Ready)
    (stored : frontend.server.sessions[handle]? = some (some ready)) :
    ∃ root, before.roots ready.reference = some root ∧ roots setup seed scalar ready.reference = root := by
  obtain ⟨root, prepared⟩ := live ready (List.mem_of_getElem? stored)
  refine ⟨root, prepared, ?_⟩
  simp only [roots, correct ready.reference root prepared, Option.getD_some]

/-- Actual material demand equals the private literal source demand at every live native capability. -/
theorem live_demand (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (frontend : RegistrationNativePublicFrontend.State mlSource)
    (before : RegistrationNativePublicInterpreter.State n KemSK) (live : Live frontend before)
    (correct : MemoCorrect setup seed scalar before.roots) (handle : Nat) (ready : RegistrationServerReferenceRoot.Ready)
    (stored : frontend.server.sessions[handle]? = some (some ready)) :
    (RegistrationNativePublicInterpreter.handler setup wire route sign
      (.inl (.inr (.inl (.inl ready.reference))))).run before =
      pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot setup.source
        (roots setup seed scalar ready.reference))), before) := by
  obtain ⟨root, prepared, literal⟩ := live_root setup seed scalar frontend before live correct handle ready stored
  simp only [RegistrationNativePublicInterpreter.handler, StateT.run_bind, StateT.run_get,
    pure_bind, StateT.run_pure, prepared, Option.map_some, literal]

end BeaconcryptCore.Computational.RegistrationNativePublicSourceState
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceState.owner_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceState.owner_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceState.restore_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceState.restore_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceState.live_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceState.live_root
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceState.live_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceState.live_demand
