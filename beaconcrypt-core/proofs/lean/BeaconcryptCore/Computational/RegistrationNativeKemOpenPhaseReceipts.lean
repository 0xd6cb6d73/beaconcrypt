-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenReceipts
import BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter

/-! Each original native accept entry has a receipt whose actual prestate satisfies the derived preselected-phase invariant. The invariant is threaded through the literal secrecy ledger below its private draws and public transcript append. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseReceipts
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeWire (Wire)
open RegistrationNativeInterface (Entry Spec)
open RegistrationNativeKemOpenProvider (State counter)
open RegistrationNativeKemOpenPhaseCounter (Safe)
open RegistrationNativeEvents (parsedAcceptCount)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def Receipt (implementation : QueryImpl Spec (OptionT (StateT (State n mlSource KemSK) ProbComp)))
    (wire : Wire) (offset parsed : Nat) (before : List Entry) : Entry → Prop
  | ⟨.inl (.inr (.accept raw)), reply⟩ => ∃ first last,
      Safe parsed first ∧ counter first = offset + parsedAcceptCount wire before ∧
      (some reply, last) ∈ support (((implementation (.inr (.accept raw))).run).run first)
  | _ => True

def Receipts (implementation : QueryImpl Spec (OptionT (StateT (State n mlSource KemSK) ProbComp)))
    (wire : Wire) (offset parsed : Nat) (transcript : List Entry) : Prop :=
  ∀ before entry after, transcript = before ++ entry :: after → Receipt implementation wire offset parsed before entry

private theorem append_split {Item : Type} (old before : List Item) (entry newest : Item) (after : List Item)
    (equal : old ++ [newest] = before ++ entry :: after) :
    (∃ rest, old = before ++ entry :: rest) ∨ (before = old ∧ entry = newest ∧ after = []) := by
  induction old generalizing before with
  | nil =>
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at equal
          exact Or.inr ⟨rfl, equal.1.symm, equal.2.symm⟩
      | cons first rest =>
          have sizes := congrArg List.length equal
          simp only [List.length_append, List.length_cons, List.length_nil] at sizes
          omega
  | cons first rest ih =>
      cases before with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at equal
          exact Or.inl ⟨rest, by rw [equal.1]; rfl⟩
      | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at equal
          obtain ⟨rfl, remaining⟩ := equal
          rcases ih tail remaining with earlier | ⟨rfl, rfl, rfl⟩
          · obtain ⟨suffix, same⟩ := earlier
            exact Or.inl ⟨suffix, by rw [same]; rfl⟩
          · exact Or.inr ⟨rfl, rfl, rfl⟩

private theorem append_receipts
    (implementation : QueryImpl Spec (OptionT (StateT (State n mlSource KemSK) ProbComp)))
    (wire : Wire) (offset parsed : Nat) (old : List Entry) (newest : Entry)
    (prior : Receipts implementation wire offset parsed old)
    (fresh : Receipt implementation wire offset parsed old newest) :
    Receipts implementation wire offset parsed (old ++ [newest]) := by
  intro before entry after equal
  rcases append_split old before entry newest after equal with earlier | ⟨rfl, rfl, rfl⟩
  · obtain ⟨rest, same⟩ := earlier
    exact prior before entry rest same
  · exact fresh

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool) (parsed : Nat)
local notation "native" => RegistrationNativeKemOpenRawCounter.native (n := n) setup checks wire route representation created credential selected pairs publicKey real parsed
local notation "step" => RegistrationNativeKemOpenLedger.step (n := n) setup checks wire route representation created credential selected pairs publicKey real parsed
local notation "run" => RegistrationNativeKemOpenReceipts.run (n := n) setup checks wire route representation created credential selected pairs publicKey real parsed

/-- Appending the original native entry retains an actual callback receipt with the derived private prephase invariant. -/
theorem step_receipts (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain) (offset : Nat)
    (beforeLedger afterLedger : RegistrationNativeLedger.State) (before after : State n mlSource KemSK)
    (safe : Safe parsed before) (counted : counter before = offset + parsedAcceptCount wire beforeLedger.transcript)
    (prior : Receipts native wire offset parsed beforeLedger.transcript) (value : RegistrationNativeInterface.FullSpec.Range query)
    (supported : (some (value, afterLedger), after) ∈ support (((step bounds query beforeLedger).run).run before)) :
    Receipts native wire offset parsed afterLedger.transcript := by
  rw [RegistrationNativeKemOpenLedger.step_trace setup checks wire route representation created credential
    selected pairs publicKey real parsed bounds query beforeLedger afterLedger before after value supported]
  apply append_receipts native wire offset parsed beforeLedger.transcript ⟨query, value⟩ prior
  cases query with
  | inr secrecy => trivial
  | inl query =>
      rw [RegistrationNativeKemOpenLedger.core_run, support_map] at supported
      obtain ⟨⟨reply, reached⟩, called, returned⟩ := supported
      cases query with
      | inl coin => trivial
      | inr command =>
          cases command with
          | accept raw =>
              cases reply with
              | none =>
                  have impossible := congrArg Prod.fst returned
                  simp only [Option.map_none, reduceCtorEq] at impossible
              | some reply =>
                  have sameReply := congrArg (fun result => result.1.map Prod.fst) returned
                  simp only [Option.map_some, Option.some.injEq] at sameReply
                  change reply = value at sameReply
                  subst value
                  exact ⟨before, reached, safe, counted, called⟩
          | _ => trivial

/-- The complete literal ledger execution derives both its native prefix counters and the private phase invariant at every original raw accept. -/
theorem run_receipts (bounds : FreshBounds) (work : OracleComp RegistrationNativeInterface.FullSpec Value)
    (offset : Nat) (beforeLedger afterLedger : RegistrationNativeLedger.State) (before after : State n mlSource KemSK)
    (safe : Safe parsed before) (counted : counter before = offset + parsedAcceptCount wire beforeLedger.transcript)
    (prior : Receipts native wire offset parsed beforeLedger.transcript) (value : Value)
    (supported : (some (value, afterLedger), after) ∈ support (((run bounds work beforeLedger).run).run before)) :
    Safe parsed after ∧ counter after = offset + parsedAcceptCount wire afterLedger.transcript ∧
      Receipts native wire offset parsed afterLedger.transcript := by
  induction work using OracleComp.inductionOn generalizing beforeLedger afterLedger before after with
  | pure original =>
      simp only [RegistrationNativeKemOpenReceipts.run, simulateQ_pure, StateT.run_pure, OptionT.run_pure,
        mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at supported
      obtain ⟨⟨_sameValue, rfl⟩, rfl⟩ := supported
      exact ⟨safe, counted, prior⟩
  | query_bind query next ih =>
      rw [RegistrationNativeKemOpenReceipts.run_query_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, reached⟩, called, tail⟩ := supported
      cases reply with
      | none =>
          simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at tail
      | some result =>
          obtain ⟨reply, reachedLedger⟩ := result
          have nextSafe := RegistrationNativeKemOpenPhaseCounter.raw_work_safe setup checks wire route representation created credential
            selected pairs publicKey real parsed _ before reached safe (reply, reachedLedger) called
          have nextCount := RegistrationNativeKemOpenLedger.step_counter setup checks wire route representation created credential
            selected pairs publicKey real parsed bounds query offset beforeLedger reachedLedger before reached counted reply called
          have nextReceipts := step_receipts setup checks wire route representation created credential
            selected pairs publicKey real parsed bounds query offset beforeLedger reachedLedger before reached safe counted prior reply called
          exact ih reply reachedLedger afterLedger reached after nextSafe nextCount nextReceipts tail

/-- The original full compiler starts these counter and phase receipts at its actual empty secrecy ledger. -/
theorem program_receipts (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before after : State n mlSource KemSK) (safe : Safe parsed before) (value : Value) (ledger : RegistrationNativeLedger.State)
    (supported : (some (value, ledger), after) ∈ support
      (((simulateQ (RegistrationNativeKemOpenProvider.implementation setup checks wire route representation created credential
          selected pairs publicKey real)
        (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)).run).run before)) :
    Safe parsed after ∧ counter after = counter before + parsedAcceptCount wire ledger.transcript ∧
      Receipts native wire (counter before) parsed ledger.transcript := by
  rw [RegistrationNativeKemOpenReceipts.program_run] at supported
  apply run_receipts setup checks wire route representation created credential selected pairs publicKey real parsed bounds
    (RegistrationNativeInterface.asModeO mode work) (counter before) RegistrationNativeLedger.empty ledger before after safe
    (by rfl) _ value supported
  intro pre entry post impossible
  have sizes := congrArg List.length impossible
  simp only [RegistrationNativeLedger.empty, List.length_nil, List.length_append, List.length_cons] at sizes
  omega

end BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseReceipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseReceipts.step_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseReceipts.step_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseReceipts.run_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseReceipts.run_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseReceipts.program_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseReceipts.program_receipts
