-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenProvider

/-! Candidate execution creates an owner key from its exact genuine reserved prefix. The private creation index, complete history and phase survive the callback; reservation alone never exposes an uncreated handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenBirth
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open PqxdhKemIndCca
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

def borns (state : State n mlSource KemSK) : Nat := state.1.2.created

/-- The actual open candidate source creates from the same indexed reservation before and after its private switch. -/
theorem create_run (before : State n mlSource KemSK) :
    (((provider (.inr (.inl .create))).run).run before) =
      (fun result => (result.1, ((before.1.1, result.2), before.2))) <$>
        (((PqxdhDynamicKemRouter.source setup.baseImpl setup.kem selected pairs .create).run).run before.1.2) := by
  cases phase : before.2 <;> simp only [RegistrationNativeKemOpenProvider.implementation,
    RegistrationNativeKemSwitchSource.source, phase, RegistrationNativeKemSwitchSource.post,
    RegistrationNativeKemSwitchSource.carry, RegistrationNativeKemGame.stopped,
    RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine,
    RegistrationNativeKemCandidatePool.source, OptionT.run_mk, StateT.run, Functor.map_map]

/-- Every actual successful birth returns its current indexed genuine public key and advances exactly one private slot, retaining the full native context and phase. -/
theorem create_receipt (before after : State n mlSource KemSK) (reply : Nat × MlKem768PublicKey)
    (supported : (some reply, after) ∈ support (((provider (.inr (.inl .create))).run).run before)) :
    ∃ pair, pairs[borns before]? = some pair ∧ reply = (borns before, pair.1) ∧
      borns after = borns before + 1 ∧ after.1.1 = before.1.1 ∧ after.2 = before.2 := by
  rw [create_run, support_map] at supported
  obtain ⟨⟨value, reached⟩, called, returned⟩ := supported
  cases found : pairs[before.1.2.created]? with
  | none =>
      simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run, found,
        mem_support_pure_iff, Prod.mk.injEq] at called
      obtain ⟨rfl, rfl⟩ := called
      have impossible := congrArg Prod.fst returned
      cases impossible
  | some pair =>
      simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run, found,
        mem_support_pure_iff, Prod.mk.injEq] at called
      obtain ⟨rfl, rfl⟩ := called
      have replyEq := congrArg Prod.fst returned
      change some (before.1.2.created, pair.1) = some reply at replyEq
      have stateEq := congrArg Prod.snd returned
      cases Option.some.inj replyEq
      cases stateEq
      exact ⟨pair, found, rfl, rfl, rfl, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeKemOpenBirth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBirth.create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBirth.create_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBirth.create_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBirth.create_receipt
