-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreter
import BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter
/-! The World service remains an explicit oracle in this source-support dictionary. Preparation, genuine routed KEM callbacks, source publication compilation, ordered signing receipts and all their continuations retain their literal bodies. Closing the World branch can therefore carry an arbitrary persistent physical state; it does not assert that ideal record replies occur in the real implementation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordService (Flags)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
abbrev Spec (n : Nat) := RegistrationNativeSecretWordService.Combined + PqxdhRecordLiftInterface.WorldSpec n
abbrev State := RegistrationNativeSecretWordInterpreter.State
abbrev M (n : Nat) (KemSK Value : Type) := StateT (State n KemSK) (OracleComp (Spec n)) Value

def combined : QueryImpl RegistrationNativeSecretWordService.Combined (OracleComp (Spec n)) :=
  fun query => (Spec n).query (.inl query)
def world : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (OracleComp (Spec n)) :=
  fun query => (Spec n).query (.inr query)
def coins : QueryImpl unifSpec (OracleComp (Spec n)) := world ∘ₛ PqxdhRecordLiftInterface.coinLift

def roots (work : StateT Flags (OracleComp RegistrationNativeSecretWordService.Combined) Value) : M n KemSK Value := fun before =>
  (fun result => (result.1,{before with flags := result.2})) <$> simulateQ combined (work.run before.flags)

def effect : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (M n KemSK) :=
  fun query => StateT.lift (world (.inr (.inl query)))

noncomputable def publication (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBoundPublication.Spec (M n KemSK) := fun query before =>
  (fun result => (result.1,{before with ordinary := {before.ordinary with receipts := result.2}})) <$>
    simulateQ (fun effectQuery => world (.inr (.inl effectQuery)))
      ((RegistrationBoundSourceCompiler.compiler setup.source (RegistrationNativeWire.ledgerCodec wire).frameWrite sign query).run before.ordinary.receipts)

noncomputable def common (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePairedServerService.Common n) (M n KemSK)
  | .inl query => publication setup wire sign query
  | .inr query => effect query

def routed (provider : Provider KemSK) (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain) :
    M n KemSK ((RegistrationNativeSecretWordKemInterface.Routed KemSK).Range query) := fun before =>
  (fun result => (result.1,{before with kem := result.2})) <$>
    simulateQ coins ((provider query).run before.kem)

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK) :
    QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (M n KemSK)
  | .inl (.inl message) => roots (RegistrationNativeSecretWordService.handler (n := n) setup.source input inside (.inl message))
  | .inl (.inr (.inl (.inl message))) => roots (RegistrationNativeSecretWordService.handler (n := n) setup.source input inside (.inr message))
  | .inl (.inr (.inl (.inr query))) => common setup wire sign query
  | .inl (.inr (.inr query)) => routed provider query
  | .inr query => StateT.lift (world (.inr (.inr query)))

theorem prepare_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (message : Message) (before : State n KemSK) :
    (handler setup wire sign input inside provider (.inl (.inl message))).run before =
      pure ((input message).map (fun _ => message),
        {before with flags := Function.update before.flags message (input message).isSome}) := by
  simp only [handler,roots,StateT.run,RegistrationNativeSecretWordService.handler,simulateQ_pure,map_pure]

theorem kem_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain) (before : State n KemSK) :
    (handler setup wire sign input inside provider (.inl (.inr (.inr query)))).run before =
      (fun result => (result.1,{before with kem := result.2})) <$>
        simulateQ coins ((provider query).run before.kem) := rfl

theorem record_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK) :
    (handler setup wire sign input inside provider (.inr query)).run before =
      (fun reply => (reply,before)) <$> world (.inr (.inr query)) := by
  simp only [handler,StateT.run_lift,bind_pure_comp]
  rfl

theorem common_frame (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain)
    (before : State n KemSK) (result : (RegistrationNativePairedServerService.Common n).Range query × State n KemSK)
    (supported : result ∈ support ((common setup wire sign query).run before)) :
    result.2.flags=before.flags ∧ result.2.kem=before.kem := by
  rcases query with publicationQuery | effectQuery
  · simp only [common,publication,StateT.run,support_map] at supported
    obtain ⟨answer,_,returned⟩ := supported
    cases returned
    exact ⟨rfl,rfl⟩
  · simp only [common,effect,StateT.run_lift,bind_pure_comp,support_map] at supported
    obtain ⟨answer,_,returned⟩ := supported
    cases returned
    exact ⟨rfl,rfl⟩

section Closing
variable {m : Type → Type} [Monad m] [LawfulMonad m]
def close (keys : QueryImpl RegistrationNativeSecretWordService.Combined m)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) m) : QueryImpl (Spec n) m
  | .inl query => keys query
  | .inr query => physical query

theorem world_source (keys : QueryImpl RegistrationNativeSecretWordService.Combined m)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) m)
    (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) Value) :
    simulateQ (close keys physical) (simulateQ world work) = simulateQ physical work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : close keys physical ∘ₛ world = physical := by
    funext query
    simp only [QueryImpl.compose,world,simulateQ_spec_query,close]
  rw [same]

theorem record_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (keys : QueryImpl RegistrationNativeSecretWordService.Combined m)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) m)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK) :
    simulateQ (close keys physical) ((handler setup wire sign input inside provider (.inr query)).run before) =
      (fun reply => (reply,before)) <$> physical (.inr (.inr query)) := by
  rw [record_run,simulateQ_map]
  simp only [world,simulateQ_spec_query,close]

theorem routed_source (provider : Provider KemSK)
    (keys : QueryImpl RegistrationNativeSecretWordService.Combined m)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) m)
    (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain) (before : State n KemSK) :
    simulateQ (close keys physical) ((routed provider query).run before) =
      (fun result => (result.1,{before with kem := result.2})) <$>
        simulateQ (physical ∘ₛ PqxdhRecordLiftInterface.coinLift) ((provider query).run before.kem) := by
  simp only [routed,StateT.run,simulateQ_map,coins,QueryImpl.simulateQ_compose]
  rw [world_source]

theorem publication_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (keys : QueryImpl RegistrationNativeSecretWordService.Combined m)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) m)
    (query : RegistrationBoundPublication.Spec.Domain) (before : State n KemSK)
    {ProviderState : Type} (nativeBefore : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState)
    (receipts : nativeBefore.receipts = before.ordinary.receipts) :
    simulateQ (close keys physical) ((publication setup wire sign query).run before) =
      (fun result => (result.1,{before with ordinary := {before.ordinary with receipts := result.2.receipts}})) <$>
        simulateQ physical ((RegistrationNativeHiddenInterpreter.publication setup wire sign query).run nativeBefore) := by
  simp only [publication,RegistrationNativeHiddenInterpreter.publication,StateT.run,simulateQ_map,
    ← QueryImpl.simulateQ_compose,Functor.map_map,receipts]
  rfl
end Closing
end BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary



/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.prepare_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.kem_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.kem_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.record_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.record_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.common_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.common_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.world_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.record_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.routed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.routed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.publication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorWorldDictionary.publication_source
