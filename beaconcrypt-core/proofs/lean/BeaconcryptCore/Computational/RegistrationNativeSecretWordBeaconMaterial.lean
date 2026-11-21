-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial

/-! Concrete Beacon material completion changes only the private root-service reference from bytes to its opaque word. Native first-record opening, every abort, actual World effects and terminal success retain the original owner and environment behavior. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
abbrev Spec (n : Nat) := RegistrationNativeSecretWordInterface.WordPairedPublicSpec n
variable {n : Nat} {Auxiliary : Type}

def effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) : OracleComp (Spec n) ((PqxdhRecordLiftInterface.EnvEffects n).Range query) :=
  (Spec n).query (.inr (.inr query))

noncomputable def admitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (message : Message) :
    OracleComp (Spec n) (RustM RegistrationNativePairedBeaconService.Result) := do
  let chosen ← (Spec n).query (.inl message)
  match chosen with
  | none => pure (.ok (.Err ⟨sender⟩))
  | some choice =>
      simulateQ RegistrationNativeSecretWordServerMaterial.commonLift
        (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor choice)

/-- Material callbacks retain their original replies and exact native stages; only the private reference address is evaluated. -/
theorem admitted_source (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (owner : Nat) (sender : U64)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (message : Message) :
    simulateQ (RegistrationNativeSecretWordServerMaterial.realize candidate) (admitted (n := n) source owner sender descriptor message) =
      RegistrationNativePairedBeaconService.admitted source owner sender descriptor
        (RegistrationNativeSecretWordMessage.eval candidate message) := by
  simp only [admitted, RegistrationNativePairedBeaconService.admitted, simulateQ_bind,
    simulateQ_spec_query, RegistrationNativeSecretWordServerMaterial.realize]
  apply bind_congr
  intro chosen
  cases chosen with
  | none => simp only [simulateQ_pure]
  | some choice =>
      rw [← QueryImpl.simulateQ_compose]
      have same : RegistrationNativeSecretWordServerMaterial.realize candidate ∘ₛ
          RegistrationNativeSecretWordServerMaterial.commonLift =
          (RegistrationNativePairedServerService.publicCommon : QueryImpl (RegistrationNativePairedServerService.Common n)
            (OracleComp (RegistrationNativePairedServerService.PublicSpec n))) := by
        funext query
        simp only [QueryImpl.compose, RegistrationNativeSecretWordServerMaterial.commonLift, simulateQ_spec_query,
          RegistrationNativeSecretWordServerMaterial.realize, RegistrationNativePairedServerService.publicCommon]
      rw [same]

abbrev OwnerM (n : Nat) (Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (SelectedOwner source) (StateT (EnvState Auxiliary) (OracleComp (Spec n)))

def abort {source : RegistrationNativeMldsa.Source} (owner : SelectedOwner source) : OwnerM n Auxiliary source Unit := do
  let _ ← StateT.lift (StateT.lift (effect (.inr (.advanceOwner owner.worldOwner .aborted))))
  pure ()

noncomputable def complete (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner : SelectedOwner mlSource) (ready : BeaconReady) :
    OwnerM n Auxiliary mlSource (RustM (Option Pqxdh.Bytes)) := do
  let completed ← StateT.lift (StateT.lift (admitted source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference))
  match completed with
  | .fail error => abort owner *> pure (.fail error)
  | .div => abort owner *> pure .div
  | .ok (.Err _) => abort owner *> pure (.ok none)
  | .ok (.Ok completed) => do
      modify fun current => { current with phase := .established completed }
      pure (.ok (some (TranscriptAuthParts.absSlice completed.application)))

/-- The actual native completion restores exactly, including terminal abort and the complete owner/environment poststate. -/
theorem complete_source {KemSK : Type} (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) {mlSource : RegistrationNativeMldsa.Source}
    (owner before : SelectedOwner mlSource) (ready : BeaconReady) (env : EnvState Auxiliary) :
    simulateQ (RegistrationBeaconReferenceFinish.service (n := n) (KemSK := KemSK) ∘ₛ
      RegistrationNativeSecretWordServerMaterial.realize candidate)
      (((complete source owner ready).run before).run env) =
      (((RegistrationBeaconReferenceFinish.complete source owner (ready.eval candidate)).run before).run env) := by
  simp only [complete, RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left, simulateQ_bind, QueryImpl.simulateQ_compose, admitted_source, BeaconReady.eval]
  apply bind_congr
  intro completed
  cases completed with
  | fail error => rfl
  | div => rfl
  | ok completed => cases completed <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial.admitted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial.admitted_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial.complete_source
