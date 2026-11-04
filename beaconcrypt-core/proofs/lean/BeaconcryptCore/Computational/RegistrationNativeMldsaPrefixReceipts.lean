-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeParsedCounterLedger
import BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant

/-! Every actual public acceptance prefix carries the original native source call and its same-run pre/post cached ML signing receipts. The invariant is derived while the complete adaptive ledger execution continues, including failed accepts and original hidden secrecy draws. Later signing cannot be substituted for this retained prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaPrefixReceipts
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
      RegistrationNativeMldsaInvariant.Valid first ∧ RegistrationNativeMldsaInvariant.Valid last ∧
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

private theorem raw_valid (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : Spec.Domain) (before : State n KemSK mlSource) (valid : RegistrationNativeMldsaInvariant.Valid before)
    (result : Spec.Range query × State n KemSK mlSource)
    (supported : result ∈ support ((native setup checks wire route representation created credential query).run before)) :
    RegistrationNativeMldsaInvariant.Valid result.2 :=
  RegistrationNativeMldsaInvariant.program setup checks wire route representation created credential
    (RegistrationNativeRawAdapter.adapter wire query) before valid result supported

private theorem full_valid (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK mlSource)
    (valid : RegistrationNativeMldsaInvariant.Valid before.2)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential) query).run before)) :
    RegistrationNativeMldsaInvariant.Valid result.2.2 := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (native setup checks wire route representation created credential)
    RegistrationNativeMldsaInvariant.Valid
    (fun command first checked last reached => raw_valid setup checks wire route representation created credential command first checked last reached)
    _ before.2 valid inner possible

/-- A complete actual full-interface step records the source preincrement counter for its original raw accept entry. -/
theorem step_receipts (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain) (offset : Nat)
    (before : RegistrationNativeLedger.State × State n KemSK mlSource)
    (counted : before.2.parsedAccepts = offset + parsedAcceptCount wire before.1.transcript)
    (valid : RegistrationNativeMldsaInvariant.Valid before.2)
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
              exact ⟨before.2, inner.2, counted, valid,
                raw_valid setup checks wire route representation created credential (.inr (.accept raw)) before.2 valid inner supported, supported⟩
          | _ => trivial

def Holds (implementation : QueryImpl Spec (StateT (State n KemSK mlSource) ProbComp))
    (wire : Wire) (offset : Nat) (current : RegistrationNativeLedger.State × State n KemSK mlSource) : Prop :=
  current.2.parsedAccepts = offset + parsedAcceptCount wire current.1.transcript ∧
    RegistrationNativeMldsaInvariant.Valid current.2 ∧ Receipts implementation wire offset current.1.transcript

/-- Every complete actual full-interface callback retains the exact counter, cached histories and all earlier prefix receipts together. -/
theorem step_holds (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain) (offset : Nat)
    (before : RegistrationNativeLedger.State × State n KemSK mlSource)
    (valid : Holds (native (n := n) setup checks wire route representation created credential) wire offset before)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential) query).run before)) :
    Holds (native (n := n) setup checks wire route representation created credential) wire offset result.2 :=
  ⟨RegistrationNativeParsedCounterLedger.step_counter setup checks wire route representation created credential
      bounds query offset before valid.1 result supported,
    full_valid setup checks wire route representation created credential bounds query before valid.2.1 result supported,
    step_receipts setup checks wire route representation created credential bounds query offset before
      valid.1 valid.2.1 valid.2.2 result supported⟩

/-- Every complete original adaptive native execution derives its counter equation and all actual raw accept-call receipts. -/
theorem run_receipts (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK mlSource) (valid : RegistrationNativeMldsaInvariant.Valid before)
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
        full_valid setup checks wire route representation created credential bounds query current valid.2.1 next supported,
        step_receipts setup checks wire route representation created credential bounds query before.parsedAccepts
          current valid.1 valid.2.1 valid.2.2 next supported⟩) _ (RegistrationNativeLedger.empty, before) _ result reached
  refine ⟨rfl, valid, ?_⟩
  intro pre entry post impossible
  have sizes := congrArg List.length impossible
  simp only [RegistrationNativeLedger.empty, List.length_nil, List.length_append, List.length_cons] at sizes
  omega

end BeaconcryptCore.Computational.RegistrationNativeMldsaPrefixReceipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPrefixReceipts.step_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPrefixReceipts.step_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPrefixReceipts.run_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPrefixReceipts.run_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaPrefixReceipts.step_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaPrefixReceipts.step_holds
