-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeParsedCounterLedger

/-! Each original native accept transcript entry retains a receipt of the actual source callback and its private preincrement counter. Receipts are derived during the complete original ledger execution, including failed decoded accepts and hidden secrecy operations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedCounterReceipts
open RegistrationNativeExperiment (State)
open RegistrationNativeInterface (Entry Spec)
open RegistrationNativeEvents (parsedAcceptCount)
open RegistrationNativeWire (Wire)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeParsedCounterLedger (native)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}

def Receipt (implementation : QueryImpl Spec (StateT (State n KemSK mlSource) ProbComp))
    (wire : Wire) (offset : Nat) (before : List Entry) : Entry → Prop
  | ⟨.inl (.inr (.accept raw)), reply⟩ => ∃ first last,
      first.parsedAccepts = offset + parsedAcceptCount wire before ∧
      (reply, last) ∈ support ((implementation (.inr (.accept raw))).run first)
  | _ => True

def Receipts (implementation : QueryImpl Spec (StateT (State n KemSK mlSource) ProbComp))
    (wire : Wire) (offset : Nat) (transcript : List Entry) : Prop :=
  ∀ before entry after, transcript = before ++ entry :: after → Receipt implementation wire offset before entry

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
    (implementation : QueryImpl Spec (StateT (State n KemSK mlSource) ProbComp))
    (wire : Wire) (offset : Nat) (old : List Entry) (newest : Entry)
    (prior : Receipts implementation wire offset old)
    (fresh : Receipt implementation wire offset old newest) :
    Receipts implementation wire offset (old ++ [newest]) := by
  intro before entry after equal
  rcases append_split old before entry newest after equal with earlier | ⟨rfl, rfl, rfl⟩
  · obtain ⟨rest, same⟩ := earlier
    exact prior before entry rest same
  · exact fresh

/-- A complete actual full-interface step records the source preincrement counter for its original raw accept entry. -/
theorem step_receipts (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain) (offset : Nat)
    (before : RegistrationNativeLedger.State × State n KemSK mlSource)
    (counted : before.2.parsedAccepts = offset + parsedAcceptCount wire before.1.transcript)
    (prior : Receipts (native (n := n) setup checks wire route representation created credential) wire offset before.1.transcript)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (reached : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential) query).run before)) :
    Receipts (native (n := n) setup checks wire route representation created credential) wire offset result.2.1.transcript := by
  have trace := RegistrationNativeParsedCounterLedger.step_trace setup checks wire route representation created credential bounds query before result reached
  rw [trace]
  apply append_receipts _ wire offset before.1.transcript ⟨query, result.1⟩ prior
  cases query with
  | inr secrecy => trivial
  | inl query =>
      rw [RegistrationNativeParsedCounterLedger.core_run, support_map] at reached
      obtain ⟨inner, supported, equal⟩ := reached
      cases query with
      | inl coin => trivial
      | inr command =>
          cases command with
          | accept raw =>
              cases equal
              exact ⟨before.2, inner.2, counted, supported⟩
          | _ => trivial

def Holds (implementation : QueryImpl Spec (StateT (State n KemSK mlSource) ProbComp))
    (wire : Wire) (offset : Nat) (current : RegistrationNativeLedger.State × State n KemSK mlSource) : Prop :=
  current.2.parsedAccepts = offset + parsedAcceptCount wire current.1.transcript ∧
    Receipts implementation wire offset current.1.transcript

/-- Every complete original adaptive native execution derives its counter equation and all actual raw accept-call receipts. -/
theorem run_receipts (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK mlSource)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (reached : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created
      mlSource credential bounds mode work before)) :
    Holds (native (n := n) setup checks wire route representation created credential) wire before.parsedAccepts result.2 := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential))
    (Holds (native (n := n) setup checks wire route representation created credential) wire before.parsedAccepts)
    (fun query current valid next supported =>
      ⟨RegistrationNativeParsedCounterLedger.step_counter setup checks wire route representation created credential
          bounds query before.parsedAccepts current valid.1 next supported,
        step_receipts setup checks wire route representation created credential bounds query before.parsedAccepts
          current valid.1 valid.2 next supported⟩) _ (RegistrationNativeLedger.empty, before) _ result reached
  constructor
  · rfl
  · intro pre entry post impossible
    have sizes := congrArg List.length impossible
    simp only [RegistrationNativeLedger.empty, List.length_nil, List.length_append, List.length_cons] at sizes
    omega

end BeaconcryptCore.Computational.RegistrationNativeParsedCounterReceipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedCounterReceipts.step_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedCounterReceipts.step_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedCounterReceipts.run_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedCounterReceipts.run_receipts
