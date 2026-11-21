-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathMap
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendTrace

/-! The actual chronological Word observer erases pointwise at every typed callback. Its concrete monitored state projects to the original complete source state, allowing a single actual full path to carry both metadata and its original trace. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  (RegistrationNativeSecretWordMessage.State source × RegistrationNativeSecretWordFrontendTrace.State) × RegistrationNativeSecretWordInterpreter.State n KemSK

def project (before : State n KemSK source) : RegistrationNativeSecretWordTargetSource.State n KemSK source := (before.1.1, before.2)

noncomputable def typed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State n KemSK source) ProbComp) := fun query before =>
  (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
    (simulateQ (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer)
      ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
        ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before.1.1)).run before.1.2)).run before.2

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Erasing only the monitor gives the original typed source callback at the literal same original frontend/private input state. -/
theorem typed_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source) :
    Prod.map id project <$> ((typed setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey query).run before) =
      ((RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey query).run (project before)) := by
  have erased := RegistrationNativeSecretWordFrontendTrace.program_erase
    ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before.1.1) before.1.2
  have closed := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) work).run before.2) erased
  rw [simulateQ_map, StateT.run_map] at closed
  rw [RegistrationNativeSecretWordTargetSource.typed_run]
  simpa only [typed, StateT.run, Functor.map_map, Prod.map_def, id_eq, project] using closed

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedSource.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedSource.typed_source
