-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld

/-! Uniform, hash, HMAC and ongoing record commands of the actual mixed client have their literal native dispatcher semantics. Owner records use the retained World owner handle, with no owner-index identification premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceOtherQueries
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (restore project nativeView)
open RegistrationNativePublicSourceExecution (execute)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def Ordinary : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inl _ => True
  | .inr (.hmac _ _) | .inr (.hash _) | .inr (.serverSend _ _) | .inr (.serverRaw _)
  | .inr (.beaconSend _ _) | .inr (.beaconRaw _ _) => True
  | _ => False

/-- All actual non-registration commands retain their native full protocol state, returned values and source World under the explicit output view. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (roots : Roots)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (ordinary : Ordinary query) (before : State n KemSK source) :
    Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept publicPrekey query)).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run
          (restore roots scalar before.1 before.2) := by
  cases query with
  | inl coin => exact RegistrationNativePublicSourceWorld.effect_source setup wire route _ created.seed scalar roots (.inl coin) before
  | inr command => cases command with
    | hmac key bytes =>
        change (pure (setup.hmac.eval key bytes, project roots scalar before.1 before.2) : ProbComp _) =
          pure (setup.hmac.eval key bytes, nativeView (restore roots scalar before.1 before.2))
        rfl
    | hash bytes => exact RegistrationNativePublicSourceWorld.effect_source setup wire route _ created.seed scalar roots (.inr (.hash bytes)) before
    | serverSend keyId plaintext => exact RegistrationNativePublicSourceWorld.record_source setup wire route _ created.seed scalar roots (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact RegistrationNativePublicSourceWorld.record_source setup wire route _ created.seed scalar roots (.inl (.inr raw)) before
    | beaconSend owner plaintext => exact RegistrationNativePublicSourceWorld.record_source setup wire route _ created.seed scalar roots (.inr (owner, .inl plaintext)) before
    | beaconRaw owner raw => exact RegistrationNativePublicSourceWorld.record_source setup wire route _ created.seed scalar roots (.inr (owner, .inr raw)) before
    | _ => exact ordinary.elim

end BeaconcryptCore.Computational.RegistrationNativePublicSourceOtherQueries
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceOtherQueries.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceOtherQueries.query_source
