import BeaconcryptCore.Extraction.Funs
import Examples.CommitmentScheme.Binding
import VCVio.StateSeparating.Hybrid

/-!
# VCVio computational-proof feasibility probe

This module checks two proof seams needed by beaconcrypt's computational-security plan. The first instantiates VCVio's tight and collision-resistance-chain bounded random-oracle commitment theorems with the exact 229-byte transcript width emitted by Aeneas and a 512-bit digest. The second links a public handler to a private consuming-key interface and checks exact one- and two-call observations and final states.

The CTX theorems are a collision-layer pilot, not the complete modified-CTX theorem. A checked embedding of beaconcrypt's payload, explanations, distinctness predicate, and verifier into the generic binding game is still required. Connecting that game to distinct production values of `CtxTranscript` additionally requires the production transcript-injectivity and collision-witness contract. The compiled theorems are unconditional only inside the ideal random-function model; treating deployed BLAKE2b-512 as that oracle is an idealization, not a standard-model collision-resistance reduction.
-/

open OracleSpec OracleComp ENNReal
open beaconcrypt_core

namespace BeaconcryptCore.Computational.VCVioFeasibility

/-! ## Production-shaped generic commitment collision game -/

/-- The exact fixed-width byte type stored by Aeneas's extracted production commitment transcript. -/
abbrev CtxTranscript := Aeneas.Std.Array Aeneas.Std.U8 229#usize

instance : DecidableEq CtxTranscript := fun left right =>
  decidable_of_iff (left.val = right.val) Subtype.ext_iff.symm

local instance : Finite Aeneas.Std.U8 :=
  Finite.of_injective (fun value : Aeneas.Std.U8 => value.bv) (by
    rintro ⟨left⟩ ⟨right⟩ equality
    cases equality
    rfl)

local instance : Finite CtxTranscript := by
  change Finite (List.Vector Aeneas.Std.U8 229)
  infer_instance

/-- The output width of production BLAKE2b-512. -/
abbrev CtxDigest := BitVec 512

/-- VCVio's bounded ROM binding adversary specialized to beaconcrypt's transcript and digest widths. -/
abbrev CtxAdversary (queryBudget : ℕ) :=
  BindingAdversary CtxTranscript Unit CtxDigest queryBudget

/-- The generic bounded ROM game shares one hidden lazy random-function cache between the adversary and the two verifier queries. -/
def ctxBindingGame {queryBudget : ℕ} (adversary : CtxAdversary queryBudget) :=
  bindingGame adversary

/-- The tight generic ROM theorem combines the adversary-cache birthday bound with two fresh verifier queries. -/
theorem ctx_binding_bound_tight {queryBudget : ℕ} (adversary : CtxAdversary queryBudget) :
    Pr[fun result => result.1 = true | ctxBindingGame adversary] ≤
      (((queryBudget * (queryBudget - 1) + 2 : ℕ) : ℝ≥0∞) /
        (2 * Fintype.card CtxDigest)) :=
  binding_bound adversary

/-- The tight bound with the 512-bit random-oracle range cardinality made explicit. -/
theorem ctx_binding_bound_tight_512 {queryBudget : ℕ}
    (adversary : CtxAdversary queryBudget) :
    Pr[fun result => result.1 = true | ctxBindingGame adversary] ≤
      (((queryBudget * (queryBudget - 1) + 2 : ℕ) : ℝ≥0∞) /
        (2 * ((2 ^ 512 : ℕ) : ℝ≥0∞))) := by
  simpa only [CtxDigest, card_bitVec] using ctx_binding_bound_tight adversary

/-- The looser collision-resistance-chain theorem bounds a win via at most `queryBudget + 2` lazy-ROM queries. -/
theorem ctx_binding_bound {queryBudget : ℕ} (adversary : CtxAdversary queryBudget) :
    Pr[fun result => result.1 = true | ctxBindingGame adversary] ≤
      ((((queryBudget + 2) * (queryBudget + 1) : ℕ) : ℝ≥0∞) /
        (2 * Fintype.card CtxDigest)) :=
  binding_bound_via_cr_chain adversary

/-- The looser bound with the 512-bit random-oracle range cardinality made explicit. -/
theorem ctx_binding_bound_512 {queryBudget : ℕ} (adversary : CtxAdversary queryBudget) :
    Pr[fun result => result.1 = true | ctxBindingGame adversary] ≤
      ((((queryBudget + 2) * (queryBudget + 1) : ℕ) : ℝ≥0∞) /
        (2 * ((2 ^ 512 : ℕ) : ℝ≥0∞))) := by
  simpa only [CtxDigest, card_bitVec] using ctx_binding_bound adversary

/-- The game-level byte type is definitionally the byte field of the Aeneas-extracted production type. -/
def extractedTranscriptBytes (transcript : commitment.CommitmentTranscript) : CtxTranscript :=
  transcript.bytes

/-- The Aeneas-extracted production constant and the VCVio pilot agree on the key width in the same Lean kernel. -/
theorem extracted_aead_key_size : commitment.AEAD_KEY_SIZE = 32#usize := by
  simp [commitment.AEAD_KEY_SIZE]

/-! ## Private consuming-key composition -/

/-- Private key-transfer operations hidden by sequential handler linking. -/
inductive CKeyQuery where
  | put (key : Bool)
  | take
deriving DecidableEq

/-- A dependent oracle family gives `put` and `take` their distinct result types. -/
def ckeySpec : OracleSpec CKeyQuery
  | .put _ => Bool
  | .take => Option Bool

/-- The private affine slot rejects overwrite and permanently tombstones a consumed key. -/
inductive CKeySlot where
  | empty
  | full (key : Bool)
  | taken
deriving DecidableEq, Repr

/-- Private stateful provider for the affine key-transfer interface. -/
def ckeyStore : QueryImpl.Stateful unifSpec ckeySpec CKeySlot
  | .put key => fun slot =>
      match slot with
      | .empty => pure (true, .full key)
      | .full oldKey => pure (false, .full oldKey)
      | .taken => pure (false, .taken)
  | .take => fun slot =>
      match slot with
      | .empty => pure (none, .empty)
      | .full key => pure (some key, .taken)
      | .taken => pure (none, .taken)

/-- The only public operation returns an optional key-derived observation. -/
@[reducible]
def publicSpec : OracleSpec Unit := Unit →ₒ Option Bool

/-- Stateless public orchestration that can access the private CKEY interface only before linking. -/
def publicRunCore (key : Bool) : QueryImpl publicSpec (OracleComp ckeySpec)
  | () => do
      let accepted : Bool ← (ckeySpec.query (.put key) : OracleComp ckeySpec Bool)
      if accepted then
        (ckeySpec.query .take : OracleComp ckeySpec (Option Bool))
      else
        pure none

/-- Public orchestration lifted to the state-separating handler API. -/
def publicRun (key : Bool) : QueryImpl.Stateful ckeySpec publicSpec PUnit :=
  QueryImpl.Stateful.ofStateless (publicRunCore key)

/-- Sequential linking hides CKEY and pairs the public and provider states. -/
def linkedRun (key : Bool) :
    QueryImpl.Stateful unifSpec publicSpec (PUnit × CKeySlot) :=
  (publicRun key).link ckeyStore

/-- One call to the linked public interface. -/
def onePublicCall : OracleComp publicSpec (Option Bool) :=
  publicSpec.query ()

/-- Two sequential calls expose that the linked store transfers its value at most once. -/
def twoPublicCalls : OracleComp publicSpec (Option Bool × Option Bool) := do
  let first ← publicSpec.query ()
  let second ← publicSpec.query ()
  pure (first, second)

/-- A successful one-call execution returns the transferred value and tombstones the private slot. -/
theorem linked_run_success_state :
    (linkedRun true).runState (PUnit.unit, .empty) onePublicCall =
      pure (some true, (PUnit.unit, .taken)) := by
  rfl

/-- A call from a tombstoned state is rejected and preserves the tombstone. -/
theorem linked_run_tombstoned_state :
    (linkedRun true).runState (PUnit.unit, .taken) onePublicCall =
      pure (none, (PUnit.unit, .taken)) := by
  rfl

/-- Starting empty, two sequential calls return the value once and retain the tombstone. -/
theorem linked_run_two_calls_consumes_once :
    (linkedRun true).runState (PUnit.unit, .empty) twoPublicCalls =
      pure ((some true, none), (PUnit.unit, .taken)) := by
  rfl

/-- Discarding private state exposes only the successful optional observation. -/
theorem linked_run_success_public :
    (linkedRun true).run (PUnit.unit, .empty) onePublicCall = pure (some true) := by
  rfl

end BeaconcryptCore.Computational.VCVioFeasibility
