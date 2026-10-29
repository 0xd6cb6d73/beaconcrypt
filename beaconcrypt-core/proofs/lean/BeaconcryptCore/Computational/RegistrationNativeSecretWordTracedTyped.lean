-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedPrivate

/-! The actual monitored Word frontend kernel re-associates to the same private observer interpreter, permitting exact internal owner source cuts while retaining the final original chronology. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def associate (before : RegistrationNativeSecretWordTargetTracedSource.State n KemSK source) :=
  (before.1.1, (before.1.2, before.2))

/-- Exact reassociation retains the same selected owner, native public reply, original private poststate and full trace. -/
theorem typed_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeSecretWordTargetTracedSource.State n KemSK source) :
    Prod.map id associate <$> ((RegistrationNativeSecretWordTargetTracedSource.typed setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey query).run before) =
      ((RegistrationNativeSecretWordGenericTypedFinish.typed setup checks wire sign
        (RegistrationNativeSecretWordTracedPrivate.combined (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer))
        selectedOwner selectedAccept publicPrekey query).run (associate before)) := by
  have actual := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer)
    RegistrationNativeSecretWordFrontendTrace.handler
    ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before.1.1)
    before.1.2 before.2
  have mapped := congrArg (fun program => (fun result => (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))) <$> program) actual
  simpa only [RegistrationNativeSecretWordTargetTracedSource.typed, RegistrationNativeSecretWordGenericTypedFinish.typed,
    RegistrationNativeSecretWordTracedPrivate.combined, StateT.run, associate, Functor.map_map, Prod.map_def, id_eq] using mapped
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedTyped.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedTyped.typed_source
