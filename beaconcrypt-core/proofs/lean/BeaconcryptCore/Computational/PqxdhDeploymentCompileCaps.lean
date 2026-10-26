-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentQuiet

/-! Explicit transported caps of the compiled program (CE-3 budget transport, closed form). For a complete-interface adversary that respects a budget, in either mode, the compiled program and its tagged form at any raw-accept ordinal make at most: `qCoin + qTest + qFreshBytes` coins, where `qFreshBytes = ℓmax · qFresh` is the fresh-message byte budget; `qCreate`, `qBundle`, `qAccept`, `qBuild`, `qFinish` and `qHmac` registration and HMAC commands; `qHash + S + R + qTest + qFresh` BLAKE2b queries, with `S` the record sends including tests and fresh messages and `R` the raw receives; `qSS + qSR + qTest + qFresh` Server kernel reveals; `qBS + qBR + qTest + qFresh` established-kernel reads; and no identity, KEM, prekey or one-time read. These are the `certified` premise of T4 at the transported budget, whose creation cap meets T4's `room` premise for `count + 1 = qCreate + 1`. The reveal and kernel-read caps are the looser record-command caps recorded as a plan change after the CE-3 trial. The per-class transport through the secrecy layer charges every test and fresh message both as a possible Server send and as a possible Beacon send, so the BLAKE2b cap counts them twice, and it charges one experiment coin per test although only the first admitted test draws the bit; both are sound and looser than the plan's `qHash + S + R` and `+ 1`. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps
open PqxdhServerAuthExperiment
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentCompileBudget (cost unit)
open PqxdhDeploymentCompileSecrecy (wrapCost compileFull)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

/-- The transported caps in the fourteen source14 query kinds. -/
def transported (bounds : FreshBounds) (budget : Budget) : PqxdhRegistrationJointKemCommands.Budget :=
  Sum.elim
    ![budget.coin + budget.test + budget.freshBytes bounds, budget.create, budget.bundle, budget.accept, budget.build,
      budget.finish, budget.hmac, budget.hash + budget.sends + budget.receives + budget.test + budget.fresh,
      budget.serverSend + budget.serverRaw + budget.test + budget.fresh]
    ![0, 0, 0, 0, budget.beaconSend + budget.beaconRaw + budget.test + budget.fresh]

/-- The closed form of the transported bill. -/
theorem transported_eq (bounds : FreshBounds) (budget : Budget) (kind : SourceKind) :
    (∑ core, cost kind core * ∑ full, wrapCost bounds core full * budget.cap full) = transported bounds budget kind := by
  rcases kind with kind | kind <;> fin_cases kind <;>
    simp [Fin.sum_univ_succ, cost, unit, wrapCost, Budget.cap, transported, Budget.freshBytes, Budget.sends,
      Budget.receives] <;> ring

/-- The compiled program meets the transported caps in every source14 query kind. -/
theorem compile_full_certified (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (kind : SourceKind) :
    (compileFull setup codec route bounds mode adversary).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (transported bounds budget kind) := by
  rw [← transported_eq]
  exact PqxdhDeploymentCompileSecrecy.compile_full_bound setup codec route bounds mode adversary budget respects kind

/-- The tagged compiled program at any raw-accept ordinal meets the same caps: the `certified` premise of T4. -/
theorem tag_certified (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (index : Nat) (kind : SourceKind) :
    (PqxdhRegistrationJointAcceptCutTag.tag (compileFull setup codec route bounds mode adversary) index).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (transported bounds budget kind) :=
  PqxdhRegistrationJointAcceptCutTag.tag_bound _ index _ _
    (compile_full_certified setup codec route bounds mode adversary budget respects kind)

/-- The transported creation cap meets T4's `room` premise for `count + 1 = qCreate + 1`. -/
theorem transported_room (bounds : FreshBounds) (budget : Budget) :
    transported bounds budget (.inl 1) ≤ budget.capacity := by
  simp [transported, Budget.capacity]

end BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps.transported_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps.transported_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps.compile_full_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps.compile_full_certified

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps.tag_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps.tag_certified

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps.transported_room' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps.transported_room
