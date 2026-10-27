import BeaconcryptCore.Computational.PqxdhErasedParentView
import BeaconcryptCore.Computational.PqxdhInitialSampledParent

/-! The actual later-material sampler admits an exact proof-erased runtime carrier. Erasure retains common decisions, the original start data, saved continuation and complete reached state. It does not condition on reaching the selected address or discard cached branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhErasedParentSample
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhInitialBeaconAmbient PqxdhInitialSourceInitialSecrecy
open RawCtxSelectedParentEntry
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (depth : Nat)

abbrev Start := PqxdhInitialSampledParent.Start extra M P I D K X Response A N S B
abbrev Pending := PqxdhInitialPreparedParent.Pending extra M P I D K Bool Bool A N RootOracle.QueryCache S B
abbrev Packet := Bool ⊕ (Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) ×
  (Bool ⊕ Pending (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (N := N) (S := S) (B := B)))
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

noncomputable def sampleOne (start : Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
    (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) :=
  PqxdhInitialPreparedParent.prepare source writer
    (PqxdhInitialSourcePreparedSecrecy.pre start.1.other) (PqxdhInitialSourcePreparedSecrecy.application start.1.other)
    (PqxdhInitialNativeInitializer.initial source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
    (PqxdhInitialSourcePreparedSecrecy.selector start.1.other) (PqxdhInitialSourcePreparedSecrecy.aux start.1.other)
    (PqxdhInitialSampledParent.marker source start) sender route decode
    (PqxdhInitialSourcePreparedSecrecy.observe source zeroRoot (PqxdhInitialSampledParent.response start)
      start.1.selected start.1.number start.1.ancestors start.1.disclosed)
    (PqxdhInitialSourceExperiment.execution (PqxdhInitialSampledParent.response start) start.1.index start.1.metadata
      { start.1.ready with root := zeroRoot } start.1.post start.1.before) depth
    (PqxdhInitialSourceExperiment.initialState
      (PqxdhInitialSourceExperiment.root source zeroRoot (PqxdhInitialSampledParent.response start) start.1.selected)
      start.1.shared start.1.privateState start.1.cache, [])

/-- The exact original prepared sampler differs only by its proof annotation, including every cached/common branch. -/
theorem one_erase (start : Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
    (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) :
    Sum.map id Subtype.val <$> PqxdhInitialSampledParent.sampleOne source writer sender route decode depth start =
      sampleOne source writer sender route decode depth start :=
  PqxdhInitialPreparedResources.sample_erase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def sample (prior : ProbComp (Context extra M P I D K X Response A N S B)) :
    ProbComp (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) := do
  let context ← prior
  let output ← $ᵗ HmacBlock
  match context with
  | .inl decision => pure (.inl decision)
  | .inr input =>
    let value ← sampleOne source writer sender route decode depth (input, output)
    pure (.inr ((input, output), value))

variable {prior : ProbComp (Context extra M P I D K X Response A N S B)}

def erase (packet : PqxdhInitialSampledParent.Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
    (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) :
    Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) :=
  match packet with
  | .inl decision => .inl decision
  | .inr ⟨start, value⟩ => .inr (start, Sum.map id Subtype.val value.val)

set_option backward.isDefEq.respectTransparency false in
/-- Both actual support annotations erase forwards to the same sampler, without filtering the prior or the native continuation. -/
theorem sample_erase :
    erase source writer sender route decode depth <$>
      PqxdhInitialSampledParent.sample source writer sender route decode depth prior =
      sample source writer sender route decode depth prior := by
  unfold PqxdhInitialSampledParent.sample sample
  conv_rhs => rw [← RawCtxSupportedSample.sum_erase prior]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro context
  apply bind_congr
  intro output
  cases context with
  | inl decision => rfl
  | inr input =>
    simp only [Sum.map_inr, map_bind, map_pure, erase]
    rw [← one_erase source writer sender route decode depth (input.val, output), bind_map_left]
    rfl

def address (packet : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
    (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) : PqxdhJointKdf.JointKdfAddress :=
  match packet with
  | .inl _ => FixedHkdfDomain.ratchet.address []
  | .inr (_, .inl _) => FixedHkdfDomain.ratchet.address []
  | .inr (_, .inr input) => PqxdhInitialBuilderContext.address input.1.original

/-- Removing support evidence keeps the exact selected parent address on common and pending branches. -/
theorem address_erase (packet : PqxdhInitialSampledParent.Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
    (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) :
    address (erase source writer sender route decode depth packet) =
      PqxdhInitialSampledParent.address source writer sender route decode depth packet := by
  rcases packet with common | ⟨start, pending⟩
  · rfl
  · rcases pending with ⟨common | pending, supported⟩ <;> rfl

noncomputable def native (remaining : Nat)
    (context : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) × Entry)
    (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  match context.1 with
  | .inl decision => pure decision
  | .inr (start, pending) =>
    PqxdhInitialCommonSecrecy.native source writer (PqxdhInitialSampledParent.marker source start) sender route decode
      (PqxdhErasedParentView.view source
        (PqxdhInitialSourcePreparedSecrecy.pre start.1.other) (PqxdhInitialSourcePreparedSecrecy.application start.1.other)
        (PqxdhInitialNativeInitializer.initial source start.1.selectedMessage zeroRoot (PqxdhInitialSampledParent.response start))
        (PqxdhInitialSourcePreparedSecrecy.selector start.1.other) (PqxdhInitialSourcePreparedSecrecy.aux start.1.other)
        (PqxdhInitialSourceExperiment.root source zeroRoot (PqxdhInitialSampledParent.response start) start.1.selected)
        start.1.ancestors start.1.disclosed start.1.selected start.1.number remaining)
      (pending, context.2) target output

/-- The whole original native observer, including its exact Gate/Fresh test and all optional replies, factors through the proof-erased runtime carrier. -/
theorem native_erase (remaining : Nat)
    (context : PqxdhInitialSampledParent.Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior × Entry)
    (target : RootOutput) (output : FullOutput) :
    PqxdhInitialSampledParent.native source writer sender route decode depth remaining context target output =
      native source writer sender route decode remaining (erase source writer sender route decode depth context.1, context.2) target output := by
  rcases context with ⟨common | ⟨start, pending⟩, entry⟩
  · rfl
  · apply PqxdhErasedParentView.native_erase

def forgetStart (start : Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
    (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) :=
  ({ start.1 with shared := (start.1.shared.1, ∅) }, start.2)

def normalize (packet : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
    (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) :
    Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) :=
  match packet with
  | .inl decision => .inl decision
  | .inr (start, pending) => .inr (forgetStart start, pending)

/-- The selected address uses the actual saved descriptor; the earlier starting hash cache is not an address-selection input. -/
theorem address_normalize (packet : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
    (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) :
    address (normalize packet) = address packet := by
  rcases packet with common | ⟨start, common | pending⟩ <;> rfl

/-- The original whole pending observer uses its reached cache and saved state; its earlier starting hash-cache field has no runtime use after the prefix. -/
theorem native_normalize (remaining : Nat)
    (context : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) × Entry)
    (target : RootOutput) (output : FullOutput) :
    native source writer sender route decode remaining (normalize context.1, context.2) target output =
      native source writer sender route decode remaining context target output := by
  rcases context with ⟨common | ⟨start, pending⟩, entry⟩ <;> rfl

end BeaconcryptCore.Computational.PqxdhErasedParentSample


/-- info: 'BeaconcryptCore.Computational.PqxdhErasedParentSample.one_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhErasedParentSample.one_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhErasedParentSample.sample_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhErasedParentSample.sample_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhErasedParentSample.address_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhErasedParentSample.address_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhErasedParentSample.native_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhErasedParentSample.native_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhErasedParentSample.address_normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhErasedParentSample.address_normalize

/-- info: 'BeaconcryptCore.Computational.PqxdhErasedParentSample.native_normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhErasedParentSample.native_normalize
