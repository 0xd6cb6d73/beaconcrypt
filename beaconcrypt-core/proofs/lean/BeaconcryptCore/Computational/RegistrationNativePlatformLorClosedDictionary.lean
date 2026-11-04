-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem
/-! Closing the source dictionary with any persistent stateful root/World interpretation preserves its explicit preparation and genuine provider-step support laws. The entire external state is retained. These leaf facts are derived from the actual dictionary body; no callback or source-controller correspondence is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
variable {n : Nat} {I KemSK Extra : Type} {base : OracleSpec I}
abbrev State (n : Nat) (KemSK Extra : Type) := RegistrationNativeSecretWordInterpreter.State n KemSK × Extra
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (outer : QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT Extra ProbComp))
noncomputable def handler : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
    (StateT (State n KemSK Extra) ProbComp) :=
  (QueryImpl.mapStateTBase outer (RegistrationNativePlatformLorOpenDictionary.handler setup wire sign input inside provider)).flattenStateT

theorem source_support (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : State n KemSK Extra) (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query × State n KemSK Extra)
    (supported : result ∈ support ((handler setup wire sign input inside provider outer query).run before)) :
    (result.1,result.2.1) ∈ support
      ((RegistrationNativePlatformLorOpenDictionary.handler setup wire sign input inside provider query).run before.1) := by
  rw [handler,QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨reached,called,returned⟩ := supported
  cases returned
  apply OracleComp.support_simulateQ_run'_subset outer _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

theorem prepare (message : Message) (before : State n KemSK Extra)
    (result : Option Message × State n KemSK Extra)
    (supported : result ∈ support ((handler setup wire sign input inside provider outer (.inl (.inl message))).run before)) :
    result.1=(input message).map (fun _ => message) ∧ result.2.1.kem=before.1.kem :=
  RegistrationNativePlatformLorOpenDictionary.prepare_support setup wire sign input inside provider message before.1 (result.1,result.2.1)
    (source_support setup wire sign input inside provider outer (.inl (.inl message)) before result supported)

theorem routed (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain)
    (before : State n KemSK Extra)
    (result : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Range query × State n KemSK Extra)
    (supported : result ∈ support ((handler setup wire sign input inside provider outer (.inl (.inr (.inr query)))).run before)) :
    (result.1,result.2.1.kem) ∈ support ((provider query).run before.1.kem) :=
  RegistrationNativePlatformLorOpenDictionary.kem_support setup wire sign input inside provider query before.1 (result.1,result.2.1)
    (source_support setup wire sign input inside provider outer (.inl (.inr (.inr query))) before result supported)

theorem quiet (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (ordinary : RegistrationNativePlatformLorOpenDictionary.NoRouted query)
    (before : State n KemSK Extra) (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query × State n KemSK Extra)
    (supported : result ∈ support ((handler setup wire sign input inside provider outer query).run before)) :
    result.2.1.kem=before.1.kem :=
  RegistrationNativePlatformLorOpenDictionary.nonrouted_kem setup wire sign input inside provider query ordinary before.1 (result.1,result.2.1)
    (source_support setup wire sign input inside provider outer _ before result supported)
theorem contract : RegistrationNativePlatformLorSourceKem.Contract
    (handler setup wire sign input inside provider outer) (fun current => current.1.kem) input provider := by
  constructor
  · exact fun message before result supported => prepare setup wire sign input inside provider outer message before result supported
  · exact fun query before result supported => routed setup wire sign input inside provider outer query before result supported
  · exact fun query ordinary before result supported => quiet setup wire sign input inside provider outer query ordinary before result supported
end BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary.source_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary.source_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary.prepare

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary.routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary.routed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary.quiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary.contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary.contract
