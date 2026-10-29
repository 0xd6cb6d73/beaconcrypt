-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger

/-! Local inductive source predicates are retained at the actual original raw accept call states. Historical states and every original private ledger draw remain literal. Concrete applications instantiate the per-query induction certificate with their already proved actual source preservation law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCertifiedReceipts
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeInterface (Entry Spec)
open RegistrationNativeEvents (parsedAcceptCount)
open RegistrationNativeWire (Wire)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeSecretWordTargetLedger (native)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := mlSource)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
variable (valid : State n KemSK mlSource → Prop)

def Receipt (implementation : QueryImpl Spec (StateT (State n KemSK mlSource) ProbComp))
    (valid : State n KemSK mlSource → Prop) (wire : Wire) (offset : Nat) (before : List Entry) : Entry → Prop
  | ⟨.inl (.inr (.accept raw)), reply⟩ => ∃ first last,
      valid first ∧ first.1.parsedAccepts = offset + parsedAcceptCount wire before ∧
      (reply, last) ∈ support ((implementation (.inr (.accept raw))).run first)
  | _ => True

def Receipts (implementation : QueryImpl Spec (StateT (State n KemSK mlSource) ProbComp))
    (valid : State n KemSK mlSource → Prop) (wire : Wire) (offset : Nat) (transcript : List Entry) : Prop :=
  ∀ before entry after, transcript = before ++ entry :: after → Receipt (mlSource := mlSource) implementation valid wire offset before entry

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
    (valid : State n KemSK mlSource → Prop) (wire : Wire) (offset : Nat) (old : List Entry) (newest : Entry)
    (prior : Receipts (mlSource := mlSource) implementation valid wire offset old)
    (fresh : Receipt (mlSource := mlSource) implementation valid wire offset old newest) :
    Receipts (mlSource := mlSource) implementation valid wire offset (old ++ [newest]) := by
  intro before entry after equal
  rcases append_split old before entry newest after equal with earlier | ⟨rfl, rfl, rfl⟩
  · obtain ⟨rest, same⟩ := earlier
    exact prior before entry rest same
  · exact fresh

/-- A complete actual full-interface step records the source preincrement counter for its original raw accept entry. -/
theorem step_receipts (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain) (offset : Nat)
    (before : RegistrationNativeLedger.State × State n KemSK mlSource)
    (validBefore : valid before.2)
    (counted : before.2.1.parsedAccepts = offset + parsedAcceptCount wire before.1.transcript)
    (prior : Receipts (native (n := n) (mlSource := mlSource) setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey) valid wire offset before.1.transcript)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (reached : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      serverKeyId bounds
      (typed) query).run before)) :
    Receipts (native (n := n) (mlSource := mlSource) setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey) valid wire offset result.2.1.transcript := by
  have trace := RegistrationNativeSecretWordTargetLedger.step_trace setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds query before result reached
  rw [trace]
  apply append_receipts _ valid wire offset before.1.transcript ⟨query, result.1⟩ prior
  cases query with
  | inr secrecy => trivial
  | inl query =>
      rw [RegistrationNativeSecretWordTargetLedger.core_run, support_map] at reached
      obtain ⟨inner, supported, equal⟩ := reached
      cases query with
      | inl coin => trivial
      | inr command =>
          cases command with
          | accept raw =>
              cases equal
              exact ⟨before.2, inner.2, validBefore, counted, supported⟩
          | _ => trivial

def Holds (implementation : QueryImpl Spec (StateT (State n KemSK mlSource) ProbComp))
    (valid : State n KemSK mlSource → Prop) (wire : Wire) (offset : Nat) (current : RegistrationNativeLedger.State × State n KemSK mlSource) : Prop :=
  valid current.2 ∧ current.2.1.parsedAccepts = offset + parsedAcceptCount wire current.1.transcript ∧
    Receipts (mlSource := mlSource) implementation valid wire offset current.1.transcript

/-- Every complete original adaptive native execution derives its counter equation and all actual raw accept-call receipts. -/
theorem run_receipts (bounds : FreshBounds)
    (keeps : ∀ query current reached, valid current.2 →
      reached ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run current) →
        valid reached.2.2)
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK mlSource) (initialValid : valid before)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds (native (n := n) (mlSource := mlSource) setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey) valid wire before.1.parsedAccepts result.2 := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
      (typed))
    (Holds (native (n := n) (mlSource := mlSource) setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey) valid wire before.1.parsedAccepts)
    (fun query current good next supported =>
      ⟨keeps query current next good.1 supported,
        RegistrationNativeSecretWordTargetLedger.step_counter setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId
          bounds query before.1.parsedAccepts current good.2.1 next supported,
        step_receipts setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId valid bounds query before.1.parsedAccepts
          current good.1 good.2.1 good.2.2 next supported⟩) _ (RegistrationNativeLedger.empty, before) _ result reached
  refine ⟨initialValid, rfl, ?_⟩
  intro pre entry post impossible
  have sizes := congrArg List.length impossible
  simp only [RegistrationNativeLedger.empty, List.length_nil, List.length_append, List.length_cons] at sizes
  omega

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCertifiedReceipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCertifiedReceipts.step_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCertifiedReceipts.step_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCertifiedReceipts.run_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCertifiedReceipts.run_receipts
