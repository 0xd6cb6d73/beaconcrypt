-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceCompiler
import BeaconcryptCore.Computational.RegistrationNativePairedBeaconService

/-! Selected-owner completion runs the actual response-authentication/public-DH prefix, then prepares its native arbitrary-pin message before material demand. The public owner contains neither the selected scalar nor a root or kernel. Both known side inputs and hidden slot replies use the concrete native sequence-one service; terminal malformed-response consumption occurs before decoding. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish
open RegistrationBeaconReferenceCompiler
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}

def service : QueryImpl (RegistrationNativePairedServerService.PublicSpec n) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inr (.inl query))

abbrev OwnerM (n : Nat) (KemSK Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (SelectedOwner source) (M n KemSK Auxiliary)

def abort {source : RegistrationNativeMldsa.Source} (owner : SelectedOwner source) : OwnerM n KemSK Auxiliary source Unit := do
  let _ ← StateT.lift (StateT.lift (effect (.inr (.advanceOwner owner.worldOwner .aborted))))
  pure ()

/-- The root-free ready reference is demanded only after actual preparation succeeds. -/
noncomputable def complete (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) : OwnerM n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes)) := do
  let completed ← StateT.lift (StateT.lift (simulateQ service
    (RegistrationNativePairedBeaconService.admitted source owner.worldOwner owner.pin.binding.identity_key_id
      ready.descriptor ready.reference)))
  match completed with
  | .fail error => abort owner *> pure (.fail error)
  | .div => abort owner *> pure .div
  | .ok (.Err _) => abort owner *> pure (.ok none)
  | .ok (.Ok completed) => do
      modify fun current => { current with phase := .established completed }
      pure (.ok (some (TranscriptAuthParts.absSlice completed.application)))

/-- The actual move-to-aborted gate precedes the optional decoded packet. Native root preparation precedes the sole material demand. -/
noncomputable def finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) : OwnerM n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let owner ← get
  match owner.phase with
  | .initSent pending _ =>
      match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok _ => do
          let prepared ← finishPreparation setup source packet
          match prepared with
          | .fail error => abort owner *> pure (.fail error)
          | .div => abort owner *> pure .div
          | .ok none => abort owner *> pure (.ok none)
          | .ok (some ready) => complete setup.source owner ready
  | _ => pure (.ok none)

/-- Malformed response bytes consume the pending capability and perform the actual World abort without any root or material call. -/
theorem finish_malformed (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (owner : SelectedOwner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (aborted : pqxdh.BeaconAborted)
    (sent : owner.phase = .initSent pending oneTime) (moved : pending.aborted_state = .ok aborted) :
    (finish (n := n) (Auxiliary := Auxiliary) setup source none).run owner = (do
      let _ ← StateT.lift (effect (.inr (.advanceOwner owner.worldOwner .aborted)))
      pure (.ok none, { owner with phase := .aborted aborted })) := by
  apply StateT.ext
  intro env
  simp only [finish, StateT.run_bind, StateT.run_get, pure_bind, sent, moved,
    finishPreparation, StateT.run_set, RegistrationResponseExecutor.begin_malformed,
    simulateQ_pure, abort, StateT.run_lift, StateT.run_map, map_pure, bind_pure_comp,
    StateT.run_pure, seqRight_eq_bind, bind_map_left, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish.finish_malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish.finish_malformed
