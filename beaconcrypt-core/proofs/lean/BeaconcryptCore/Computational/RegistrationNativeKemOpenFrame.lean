-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider
import BeaconcryptCore.Computational.RegistrationNativeOptionalFrame

/-! Counter preservation for the open typed provider follows its literal native get/put and actual callbacks. Candidate KEM replies may change the protocol outcome while retaining the original attempt counter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenFrame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeKemOpenProvider (State implementation counter nextCounter)
open RegistrationNativeOptionalFrame (Keeps pure_keeps bind_keeps simulate_keeps)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def NoPut : (Spec n mlSource Unit).Domain → Prop
  | .inl (.inl (.inl (.put _))) => False
  | _ => True

def lower (chosen : Bool) : QueryImpl (RegistrationNativeKemServerInterface.Spec n mlSource KemSK)
    (OracleComp (Spec n mlSource KemSK)) :=
  RegistrationNativeKemRouting.route chosen ∘ₛ RegistrationNativeKemFrontendInterface.lift

private theorem next_counter (query : (Spec n mlSource KemSK).Domain) (before : State n mlSource KemSK)
    (allowed : NoPut query) : nextCounter query before = counter before := by
  rcases query with ((request | ordinary) | publicKey) | (pool | key)
  · cases request <;> try rfl
    cases allowed
  · rfl
  · rfl
  · rfl
  · rfl

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)

local notation "provider" => implementation setup checks wire route representation created credential selected pairs publicKey real

private theorem query_keeps (query : (Spec n mlSource KemSK).Domain) (allowed : NoPut query) :
    Keeps counter provider ((Spec n mlSource KemSK).query query : OracleComp (Spec n mlSource KemSK) _) := by
  intro before after value supported
  rw [simulateQ_spec_query] at supported
  exact (RegistrationNativeKemOpenProvider.query_counter setup checks wire route representation created credential
    selected pairs publicKey real query before after (some value) supported).trans (next_counter query before allowed)

/-- Arbitrary actual source work without a local-state put retains the parsed-attempt counter, including all private KEM effects. -/
theorem no_put_keeps (work : OracleComp (Spec n mlSource KemSK) Value) (allowed : work.AllQueriesSatisfy NoPut) :
    Keeps counter provider work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps counter provider value
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      exact bind_keeps counter provider _ _
        (query_keeps setup checks wire route representation created credential selected pairs publicKey real query allowed.1)
        (fun reply => ih reply (allowed.2 reply))

/-- The literal native modifier changes the real parsed counter exactly as its explicit context transformation specifies. -/
theorem modify_counter (chosen : Bool)
    (change : RegistrationNativeKemServerState.State n mlSource → RegistrationNativeKemServerState.State n mlSource)
    (before after : State n mlSource KemSK) (value : Unit)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemServerInterface.modify change))).run).run before)) :
    counter after = (change (RegistrationNativeKemServerState.mask before.1.1)).parsedAccepts := by
  simp only [RegistrationNativeKemServerInterface.modify, RegistrationNativeKemServerInterface.get,
    RegistrationNativeKemServerInterface.put, simulateQ_bind, simulateQ_spec_query, lower,
    QueryImpl.apply_compose, RegistrationNativeKemFrontendInterface.lift, RegistrationNativeKemRouting.route,
    OptionT.run_bind, Option.elimM, StateT.run_bind] at supported
  rw [RegistrationNativeKemOpenProvider.get_run] at supported
  simp only [pure_bind, Option.elim_some] at supported
  rw [RegistrationNativeKemOpenProvider.put_run] at supported
  simp only [mem_support_pure_iff, Prod.mk.injEq] at supported
  rw [supported.2]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeKemOpenFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenFrame.no_put_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenFrame.no_put_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenFrame.modify_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenFrame.modify_counter
