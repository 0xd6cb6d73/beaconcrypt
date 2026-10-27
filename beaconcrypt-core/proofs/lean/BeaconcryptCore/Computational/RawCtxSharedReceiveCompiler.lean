import BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer
import BeaconcryptCore.Computational.RawCtxChainReceiveBounds
import BeaconcryptCore.Computational.RawCtxChainOpeningArguments

/-!
The complete extracted receive driver is compiled to opaque-chain derivations and the existing finite CTX family. Private message keys occur only as labels. The compiler retains cached/future admission, all skipped slots, original optional plaintext, success consumption and rejection rollback. Chain placeholders below are used only for getters already proved independent of both chain fields; the complete source kernel and its real chains remain in the driver.

The source receive costs at most 51 opaque derivations and one selected raw component call. These are independent ledgers: preparation failure still consumes its actual derivations and makes no opening call. No key distribution, nonce uniqueness or global secrecy/authenticity premise is introduced. Every opaque derivation is an explicit oracle call whose implementation must later be charged.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler
open RawCtxInterpretedOpening RawCtxChainReceive

abbrev Label (count : Nat) := Fin (count + 1)
abbrev Spec (Chain : Type) (count : Nat) :=
  (Chain →ₒ (Chain × Label count)) + AdaptiveCtxSharedKeySelection.SourceSpec count
abbrev Source (Send Chain : Type) (count : Nat) :=
  ReceiveSpec Send Chain (Label count) RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted

def unusedChain : RatchetChain := ⟨⟨List.replicate 32 0#u8, by simp⟩⟩

/-- This normalizer reads only the original selected material, sequence and immutable context. -/
noncomputable def arguments {Send Chain : Type} {count : Nat}
    (pending : Opening Send Chain (Label count) RawCtxWholeOwner.OpenContext) :=
  RawCtxInterpretedArguments.openArguments
    (RawCtxChainInterpretation.mapOpeningChains (fun _ => unusedChain) (fun _ => unusedChain) pending)

/-- A missing or mistagged slot rejects without querying a component key. -/
noncomputable def openCall {Send Chain : Type} {count : Nat}
    (pending : Opening Send Chain (Label count) RawCtxWholeOwner.OpenContext) :
    OracleComp (Spec Chain count) (core.option.Option RawCtxWholeOwner.Decrypted) :=
  match arguments pending with
  | none => pure .None
  | some input => do
      let reply ← (Spec Chain count).query (.inr ⟨input.material, .inr input.context.raw⟩)
      pure (RawCtxSharedOpeningConsumer.apiReply input.sequence input.context reply)

/-- Every derivation remains explicit and every opening receives the challenger's original option. -/
noncomputable def compiler {Send Chain : Type} {count : Nat} :
    QueryImpl (Source Send Chain count) (OracleComp (Spec Chain count))
  | .inl request => (Spec Chain count).query (.inl request)
  | .inr pending => openCall pending

noncomputable def receive {Send Chain : Type} {count : Nat}
    (entry : RefinedRatchet Send Chain (Label count)) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :=
  simulateQ compiler (execute (Plaintext := RawCtxWholeOwner.Decrypted) entry target context)

/-- The resource classes distinguish derivations from raw verification calls. -/
def Resource {Chain : Type} {count : Nat} (kdf : Bool) : (Spec Chain count).Domain → Prop
  | .inl _ => kdf = true
  | .inr ⟨_, .inr _⟩ => kdf = false
  | .inr ⟨_, .inl _⟩ => False

instance {Chain : Type} {count : Nat} (kdf : Bool) : DecidablePred (Resource (Chain := Chain) (count := count) kdf) :=
  fun query => by cases query with
    | inl request => exact inferInstanceAs (Decidable (kdf = true))
    | inr request => cases request with | mk index query => cases query <;> simp [Resource] <;> infer_instance

/-- The opening normalizer issues only the selected raw request, even on optional failure. -/
theorem open_bound {Send Chain : Type} {count : Nat}
    (pending : Opening Send Chain (Label count) RawCtxWholeOwner.OpenContext) (kdf : Bool) :
    (openCall pending).IsQueryBoundP (Resource kdf) (if kdf = false then 1 else 0) := by
  unfold openCall
  cases selected : arguments pending with
  | none => trivial
  | some input =>
    rw [isQueryBoundP_query_bind_iff]
    cases kdf <;> simp [Resource]

set_option backward.isDefEq.respectTransparency false in
/-- One source callback conserves its resource class; no unavailable key is used by routing. -/
theorem compiler_step {Send Chain : Type} {count : Nat} (query : (Source Send Chain count).Domain) (kdf : Bool) :
    (compiler query).IsQueryBoundP (Resource kdf) (if query.isLeft = kdf then 1 else 0) := by
  cases query with
  | inl request =>
    simp only [compiler, isQueryBoundP_query_iff, Resource, Sum.isLeft]
    intro hit
    simp [hit]
  | inr pending => simpa only [compiler, Sum.isLeft, eq_comm] using open_bound pending kdf

set_option backward.isDefEq.respectTransparency false in
/-- Every adaptive continuation conserves its separate derivation/opening allowance. -/
theorem compile_bound {Send Chain Result : Type} {count : Nat}
    (client : OracleComp (Source Send Chain count) Result) (kdf : Bool) (bound : Nat)
    (bounded : client.IsQueryBoundP (fun query => query.isLeft = kdf) bound) :
    (simulateQ compiler client).IsQueryBoundP (Resource kdf) bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure value => simp
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
    have rest := fun reply => ih reply _ (bounded.2 reply)
    have total := isQueryBoundP_bind (compiler_step query kdf) (fun reply _ => rest reply)
    apply total.mono
    by_cases hit : query.isLeft = kdf
    · have positive : 0 < bound := bounded.1.resolve_left (not_not_intro hit)
      simp only [ite_eq_left hit]
      omega
    · simp [hit]

/-- The actual source cache/window guard yields 51 derivations, including rejected preparation paths. -/
theorem receive_kdf {Send Chain : Type} {count : Nat}
    (entry : RefinedRatchet Send Chain (Label count)) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    (receive entry target context).IsQueryBoundP (Resource true) 51 := by
  exact compile_bound _ true 51 (RawCtxChainReceiveBounds.receive_bound entry target context)

/-- At most one actual verification is attempted after source preparation, under every possible reply. -/
theorem receive_raw {Send Chain : Type} {count : Nat}
    (entry : RefinedRatchet Send Chain (Label count)) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    (receive entry target context).IsQueryBoundP (Resource false) 1 := by
  apply compile_bound _ false 1
  apply (RawCtxChainReceiveBounds.program_open_bound (normalBegin entry target context)).of_imp
  intro query hit
  cases query <;> simp_all

/-- A selected component label comes from the actual cached/future material getter with the original prepared sequence and context. -/
theorem arguments_source {Send Chain : Type} {count : Nat}
    (pending : Opening Send Chain (Label count) RawCtxWholeOwner.OpenContext)
    (input : RawCtxInterpretedArguments.Input (Label count) RawCtxWholeOwner.OpenContext)
    (selected : arguments pending = some input) :
    material pending = ok (.Some input.material) ∧
      RawCtxInterpretedOpening.sequence pending = ok input.sequence ∧ input.context = pending.context := by
  let mapped := RawCtxChainInterpretation.mapOpeningChains
    (fun _ : Send => unusedChain) (fun _ : Chain => unusedChain) pending
  change RawCtxInterpretedArguments.openArguments mapped = some input at selected
  unfold RawCtxInterpretedArguments.openArguments at selected
  split at selected
  · cases selected
  · rename_i index present
    cases Option.some.inj selected
    have materialExact := (RawCtxInterpretedArguments.material_total mapped).choose_spec
    have sequenceExact := (RawCtxInterpretedArguments.sequence_total mapped).choose_spec
    rw [present] at materialExact
    exact ⟨(RawCtxChainInterpretation.opening_material_chains _ _ pending).symm.trans materialExact,
      (RawCtxChainInterpretation.opening_sequence_chains _ _ pending).symm.trans sequenceExact, rfl⟩

end BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.open_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.open_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.compiler_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.compile_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.receive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.receive_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.receive_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.receive_raw

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.arguments_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedReceiveCompiler.arguments_source
