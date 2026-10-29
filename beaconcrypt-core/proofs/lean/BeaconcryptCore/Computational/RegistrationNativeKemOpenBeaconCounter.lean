-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkCounter

/-! Every actual compiled Beacon operation retains the parsed Server-accept counter. The proof covers its open controller and arbitrary native provider replies; it does not replace candidate replies by real KEM outputs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconCounter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeKemOpenProvider (State implementation counter)
open RegistrationNativeKemOpenFrame (NoPut lower)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

private theorem trusted_allowed (chosen : Bool) (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    AllQueriesSatisfy (simulateQ (lower (mlSource := mlSource) chosen)
      (RegistrationNativeKemBeaconCompiler.trusted query)) NoPut := by
  rcases query with query | (query | (query | key))
  all_goals cases chosen <;> exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem trusted_program_allowed (chosen : Bool)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    AllQueriesSatisfy (simulateQ (lower (mlSource := mlSource) chosen)
      (simulateQ RegistrationNativeKemBeaconCompiler.trusted work)) NoPut := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact allQueriesSatisfy_bind (trusted_allowed chosen query) ih

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)

local notation "provider" => implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Actual Beacon creation, publication, finish and every optional failure retain the private parsed selector under the open candidate provider. -/
theorem beacon_counter (chosen : Bool)
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (before after : State n mlSource KemSK) (value : Value)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen)
        (RegistrationNativeKemBeaconCompiler.beacon work))).run).run before)) :
    counter after = counter before := by
  simp only [RegistrationNativeKemBeaconCompiler.beacon, RegistrationNativeKemServerInterface.get,
    RegistrationNativeKemServerInterface.put, simulateQ_bind, simulateQ_spec_query, lower,
    QueryImpl.apply_compose, RegistrationNativeKemFrontendInterface.lift, RegistrationNativeKemRouting.route,
    OptionT.run_bind, Option.elimM, StateT.run_bind] at supported
  rw [RegistrationNativeKemOpenProvider.get_run] at supported
  simp only [pure_bind, Option.elim_some, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, reached⟩, called, tail⟩ := supported
  cases reply with
  | none =>
      simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at tail
  | some reply =>
      have preserved := RegistrationNativeKemOpenFrame.no_put_keeps setup checks wire route representation created credential
        selected pairs publicKey real _
        (trusted_program_allowed chosen
          ((work.run (RegistrationNativeKemServerState.mask before.1.1).beacons).run
            (RegistrationWorldAgreementCompiler.erase (RegistrationNativeKemServerState.mask before.1.1).server.world)))
        (((RegistrationNativeKemServerState.mask before.1.1), before.1.2), before.2) reached reply called
      simp only [Option.elim_some, StateT.run_bind] at tail
      rw [RegistrationNativeKemOpenProvider.get_run] at tail
      simp only [pure_bind, Option.elim_some, StateT.run_bind] at tail
      rw [RegistrationNativeKemOpenProvider.put_run] at tail
      simp only [pure_bind, Option.elim_some] at tail
      have sameState := congrArg Prod.snd tail
      have sameCounter := congrArg counter sameState
      change counter after = counter reached at sameCounter
      exact sameCounter.trans preserved

end BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconCounter.beacon_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconCounter.beacon_counter
