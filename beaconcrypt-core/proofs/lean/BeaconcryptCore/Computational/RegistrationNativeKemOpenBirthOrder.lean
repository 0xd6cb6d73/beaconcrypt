-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthFrame
import BeaconcryptCore.Computational.RegistrationNativeKemOpenRawCounter

/-! Every completed candidate-provider operation preserves or extends the current genuine KEM birth prefix. This derives later-owner availability from the actual constructor and private service, without assuming a public owner index is a World or Ed handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthOrder
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemOpenBirth (borns)
open RegistrationNativeKemParsedRouting (Spec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

private theorem query_mono (query : (Spec n mlSource KemSK).Domain)
    (before after : State n mlSource KemSK) (value : (Spec n mlSource KemSK).Range query)
    (supported : (some value, after) ∈ support (((provider query).run).run before)) : borns before ≤ borns after := by
  have ordinary (noCreate : ¬ RegistrationNativeKemOpenBirthFrame.IsCreate query) : borns before ≤ borns after := by
    exact Nat.le_of_eq (RegistrationNativeKemOpenBirthFrame.query_counter setup checks wire route representation created credential
      selected pairs publicKey real query noCreate before after value supported).symm
  rcases query with other | (pool | key)
  · exact ordinary (by intro impossible; cases impossible)
  · cases pool with
    | create =>
        obtain ⟨pair, _found, _reply, counted, _context, _phase⟩ :=
          RegistrationNativeKemOpenBirth.create_receipt setup checks wire route representation created credential
            selected pairs publicKey real before after value supported
        omega
    | decapsulate index ciphertext => exact ordinary (by intro impossible; cases impossible)
    | reveal index => exact ordinary (by intro impossible; cases impossible)
  · exact ordinary (by intro impossible; cases impossible)

/-- Arbitrary completed actual native candidate-source work never removes an already-created genuine private slot. -/
theorem work_mono (work : OracleComp (Spec n mlSource KemSK) Value) (before after : State n mlSource KemSK)
    (value : Value) (supported : (some value, after) ∈ support (((simulateQ provider work).run).run before)) :
    borns before ≤ borns after := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure original =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
      rw [supported.2]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, reached⟩, called, tail⟩ := supported
      cases reply with
      | none =>
          simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
            reduceCtorEq, false_and] at tail
      | some reply =>
          exact (query_mono setup checks wire route representation created credential selected pairs publicKey real
            query before reached reply called).trans (ih reply reached after tail)

/-- The complete original raw client inherits private-prefix monotonicity through its actual native decoder and dispatcher. -/
theorem raw_work_mono (parsed : Nat) (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before after : State n mlSource KemSK) (value : Value)
    (supported : (some value, after) ∈ support
      (((simulateQ (RegistrationNativeKemOpenRawCounter.native setup checks wire route representation created credential
        selected pairs publicKey real parsed) work).run).run before)) : borns before ≤ borns after := by
  apply work_mono setup checks wire route representation created credential selected pairs publicKey real _ before after value
  simpa only [RegistrationNativeKemOpenRawCounter.native, QueryImpl.simulateQ_compose] using supported

end BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthOrder

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthOrder.work_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthOrder.work_mono
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthOrder.raw_work_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthOrder.raw_work_mono
