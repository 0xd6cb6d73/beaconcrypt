-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFields
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun
import BeaconcryptCore.Computational.RegistrationServerProviderCache

/-! Source interpretation of the actual Server SDK accept order with its indexed provider explicit. The native core agreement executor runs after mandatory authentication, owned replay and registration reservation; native token retention follows only ServerComplete. The full primitive auxiliary state includes the real World and provider state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderAcceptSdk
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (localImpl)
open RegistrationNativeProviderAcceptFields (Fields)
open RegistrationNativeProviderAcceptRun (Auxiliary)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK ProviderState : Type) := Fields × Auxiliary n KemSK ProviderState

def retain (accepted : agreement.ServerAgreement) : StateT (State n KemSK ProviderState) ProbComp (RustM (Option Nat)) := fun before =>
  match RegistrationNativeProviderAcceptFields.retain accepted before.1 with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (reply, after) => pure (.ok reply, (after, before.2))

noncomputable def agree (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool) (authenticated : registration.AuthenticatedInit) :
    StateT (State n KemSK ProviderState) ProbComp (RustM agreement.AgreementEffect) := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$>
    (simulateQ (RegistrationServerProviderCache.native setup checks wire route sign seed scalar provider selected)
      (RegistrationAgreementExecutor.server before.1.control .Fresh authenticated)).run before.2

noncomputable def afterAuthentication (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool) (authenticated : registration.AuthenticatedInit) :
    StateT (State n KemSK ProviderState) ProbComp (RustM (Option Nat)) := fun before =>
  if before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, before)
  else if checks.reserveRegistration then do
    let completed ← (agree setup checks wire route sign seed scalar provider selected authenticated).run before
    match completed.1 with
    | .fail error => pure (.fail error, completed.2)
    | .div => pure (.div, completed.2)
    | .ok (.ServerComplete accepted) => (retain accepted).run completed.2
    | .ok _ => pure (.ok none, completed.2)
  else pure (.ok none, before)

noncomputable def authenticate (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) : StateT (State n KemSK ProviderState) ProbComp
      (RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$>
    (RegistrationNativeProviderLocal.lower (localImpl setup wire route sign seed scalar provider selected)
      (StateT.lift (simulateQ RegistrationBeaconReferenceCompiler.effect
        (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.1.pin packet)))).run before.2

noncomputable def accept (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) : StateT (State n KemSK ProviderState) ProbComp (RustM (Option Nat)) := do
  let checked ← authenticate setup wire route sign seed scalar provider selected verify packet
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) => afterAuthentication setup checks wire route sign seed scalar provider selected authenticated
  | .ok _ => pure (.ok none)

end BeaconcryptCore.Computational.RegistrationNativeProviderAcceptSdk
