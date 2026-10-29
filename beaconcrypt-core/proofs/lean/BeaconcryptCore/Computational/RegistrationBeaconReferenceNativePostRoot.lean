-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial

/-! The complete actual native post-root component factors through the bound source108 opening before its original installation and phase update. Every optional failure keeps its reached effects. The only projection is the explicit record-request analysis ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePostRoot
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner)
open RegistrationBeaconReferenceNativeRecord (Flat environment project)
open RegistrationBeaconReferenceNativeTail (PostSpec program recordLift target)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

noncomputable def factored (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : SelectedOwner mlSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (root : PqxdhSecretInputKdf.RootOutput) :
    RegistrationNativeBeaconFrontend.M n KemSK mlSource Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let result ← StateT.lift (StateT.lift (simulateQ environment
    (simulateQ (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite)
      (RegistrationNativePairedBeaconService.program setup.source descriptor
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root)))))
  RegistrationBeaconReferenceNativeTail.compiled index owner result

private theorem lift_run (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : Flat mlSource Auxiliary) :
    (liftM work : StateT (Flat mlSource Auxiliary)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value).run before =
      (fun reply => (reply, before)) <$> work := by
  change (work >>= fun reply => pure (reply, before)) = _
  exact bind_pure_comp _ _

private theorem program_factored (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (index : Nat) (owner : SelectedOwner mlSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (root : PqxdhSecretInputKdf.RootOutput)
    (before : Flat mlSource Auxiliary) :
    (simulateQ (target (n := n) setup wire index owner)
      (program (RegistrationBeaconBoundSource.atRoot descriptor root))).run before =
      (fun value => (value.1.1, (value.1.2, value.2))) <$>
        ((factored setup wire index owner descriptor root).run before.1).run before.2 := by
  have restriction : target (n := n) (Auxiliary := Auxiliary) setup wire index owner ∘ₛ recordLift =
      RegistrationBeaconReferenceNativeRecord.target setup wire := by
    funext query
    simp only [QueryImpl.apply_compose, recordLift, simulateQ_spec_query, target]
  simp only [program, simulateQ_bind, StateT.run_bind]
  rw [← QueryImpl.simulateQ_compose, restriction, RegistrationBeaconReferenceNativeRecord.target,
    simulateQ_liftTarget]
  simp only [lift_run, QueryImpl.simulateQ_compose,
    RegistrationBeaconRecordSourceProgram.controller_source setup.source wire.frameWrite erased,
    bind_map_left, simulateQ_spec_query, target]
  simp only [factored, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left,
    map_bind]
  rfl

/-- The actual initial64/ongoing76/open/install/terminal-phase component uses exactly the bound source entry, without resetting the consumed sequence-one kernel. -/
theorem post_root (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (root : PqxdhSecretInputKdf.RootOutput)
    (before : Flat mlSource Auxiliary) :
    (fun value => (value.1.1, (value.1.2, RegistrationBeaconReferenceNativeRecord.erase value.2))) <$>
      ((RegistrationBeaconReferenceNativeTail.postRoot (n := n) setup wire index owner
        (RegistrationBeaconBoundSource.atRoot descriptor root)).run before.1).run before.2 =
      (fun value => (value.1.1, (value.1.2, value.2))) <$>
        ((factored setup wire index (eraseOwner owner) descriptor root).run (project before).1).run (project before).2 := by
  have exactSource := RegistrationBeaconReferenceNativeTail.post_root (n := n) setup wire index owner
    (RegistrationBeaconBoundSource.atRoot descriptor root) before
  rw [RegistrationBeaconReferenceNativeTail.program_source,
    program_factored setup wire erased] at exactSource
  simpa only [Functor.map_map, Prod.map_def, id_eq, RegistrationBeaconReferenceNativeRecord.project] using exactSource

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePostRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePostRoot.post_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePostRoot.post_root
