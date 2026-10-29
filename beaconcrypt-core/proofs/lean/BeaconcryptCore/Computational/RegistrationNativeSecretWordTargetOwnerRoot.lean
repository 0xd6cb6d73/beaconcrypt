-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectedAtom

/-! The actual selected-owner root callback is a successful optional echo of its own ordered collector message. Its Ready therefore carries that exact descriptor and a successful realized input. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerRoot
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider State)
open RegistrationNativeSecretWordTargetServerExecution (localImpl)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)

/-- Actual successful root preparation has precisely the source input and its same symbolic descriptor. -/
theorem prepare (message : Message) (before : State n KemSK) :
    ((localImpl setup wire route sign input inside provider outer false (.inl message)).run before) =
      pure ((input message).map (fun _ => message),
        { before with flags := Function.update before.flags message (input message).isSome }) := by
  simp only [localImpl, QueryImpl.compose, RegistrationNativeSecretWordInterface.liftLocal, simulateQ_spec_query,
    RegistrationNativeSecretWordTargetSource.implementation, QueryImpl.mapStateTBase, StateT.run_mk]
  rw [RegistrationNativeSecretWordInterpreter.prepare_run, simulateQ_pure]

/-- A successful actual selected-owner Ready retains its same source input and ordered collector descriptor. -/
theorem root (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (ready : BeaconReady) (before after : State n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (localImpl setup wire route sign input inside provider outer false)
        (simulateQ RegistrationNativeSecretWordInterface.prepare
          (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run before)) :
    ready.reference = RegistrationNativeSecretWordBeaconRoot.message pending ∧
      ∃ key, input ready.reference = some key := by
  simp only [RegistrationNativeSecretWordBeaconRoot.client, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, RegistrationNativeSecretWordInterface.prepare, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, reached⟩, called, equal⟩ := supported
  rw [prepare, mem_support_pure_iff] at called
  cases formed : input (RegistrationNativeSecretWordBeaconRoot.message pending) with
  | none =>
      simp only [formed, Option.map_none, Prod.mk.injEq] at called
      simp [called.1] at equal
  | some key =>
      simp only [formed, Option.map_some, Prod.mk.injEq] at called
      obtain ⟨rfl, rfl⟩ := called
      simp only [Option.map_some, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      exact ⟨rfl, key, formed⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerRoot
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerRoot.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerRoot.prepare
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerRoot.root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerRoot.root
