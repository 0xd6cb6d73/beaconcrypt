import BeaconcryptCore.Computational.PqxdhInitialSourceSampled
import BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy

/-!
The later-step reduction samples the original preparation, one shared initializer response and the actual stopped source prefix before its independent parent output. Its dependent carrier retains the exact original message, callbacks, continuation and all reached state. Consequently a context-dependent origin marker is simulated without assuming that two key or transcript marginals determine the full continuation distribution.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSampledParent
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
open PqxdhInitialSourceInitialSecrecy RawCtxSelectedParentEntry
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
abbrev Start (extra : OracleSpec ι) (M P I D K X Response A N : Type) (S B : Nat) :=
  Input extra M P I D K X Response A N S B × HmacBlock
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (depth remaining : Nat)

local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
noncomputable def response (start : Start extra M P I D K X Response A N S B) :=
  RawCtxSelectedInitialConstructor.response64 start.2
noncomputable def marker (start : Start extra M P I D K X Response A N S B) :=
  PqxdhInitialSelectedOrigin.mark source start.1.selectedMessage

noncomputable def sourceRun (start : Start extra M P I D K X Response A N S B) :=
  PqxdhInitialNativeAuditCarried.carried source writer (PqxdhInitialSourcePreparedSecrecy.pre start.1.other)
    (PqxdhInitialSourcePreparedSecrecy.application start.1.other) (PqxdhInitialNativeInitializer.initial source start.1.selectedMessage zeroRoot (response start))
    (PqxdhInitialSourcePreparedSecrecy.selector start.1.other) (PqxdhInitialSourcePreparedSecrecy.aux start.1.other)
    (marker source start) sender route decode (PqxdhInitialSourceExperiment.execution (response start) start.1.index start.1.metadata
      { start.1.ready with root := zeroRoot } start.1.post start.1.before) depth (depth + 1) (PqxdhInitialSourceExperiment.initialState
      (PqxdhInitialSourceExperiment.root source zeroRoot (response start) start.1.selected)
      start.1.shared start.1.privateState start.1.cache, ([] : List RootOutput))

abbrev Carrier (start : Start extra M P I D K X Response A N S B) :=
  Bool ⊕ PqxdhInitialSupportedCertificate.Supported (sourceRun source writer sender route decode depth start)

abbrev Packet (prior : ProbComp (Context extra M P I D K X Response A N S B)) :=
  Bool ⊕ (Σ start : Start extra M P I D K X Response A N S B,
    {_pending : Carrier source writer sender route decode depth start // Sum.inr start.1 ∈ support prior})

noncomputable def sampleOne (start : Start extra M P I D K X Response A N S B) :=
  PqxdhInitialSourcePreparedSecrecy.sample source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth

noncomputable def addressOne (start : Start extra M P I D K X Response A N S B) :=
  PqxdhInitialSourcePreparedSecrecy.address source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.shared start.1.privateState start.1.cache depth

noncomputable def view (start : Start extra M P I D K X Response A N S B) :=
  PqxdhInitialSourcePreparedSecrecy.view source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth remaining

noncomputable def sample (prior : ProbComp (Context extra M P I D K X Response A N S B)) :
    ProbComp (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) := do
  let context ← RawCtxSupportedSample.sum prior
  let output ← $ᵗ HmacBlock
  match context with
  | .inl decision => pure (.inl decision)
  | .inr input =>
    let value ← sampleOne source writer sender route decode depth (input.val, output)
    pure (.inr ⟨(input.val, output), ⟨value, input.property⟩⟩)

variable {prior : ProbComp (Context extra M P I D K X Response A N S B)}

noncomputable def address (packet : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X)
    (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) : JointKdfAddress :=
  match packet with
  | .inl _ => FixedHkdfDomain.ratchet.address []
  | .inr ⟨start, context⟩ => addressOne source writer sender route decode depth start context.val

variable (context : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X)
    (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior × Entry)

noncomputable def native (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  match context.1 with
  | .inl decision => pure decision
  | .inr ⟨start, pending⟩ => PqxdhInitialCommonSecrecy.native source writer (marker source start) sender route decode
      (view source writer sender route decode depth remaining start) (pending.val, context.2) target output

noncomputable def observed (output : FullOutput) : ProbComp (PqxdhInitialCommonSecrecy.Trace M P I D K A N RootOracle.QueryCache S B) :=
  match context.1 with
  | .inl decision => pure (.inl decision)
  | .inr ⟨start, pending⟩ => PqxdhInitialCommonSecrecy.observed source writer (marker source start) sender route decode
      (view source writer sender route decode depth remaining start) (pending.val, context.2) output

noncomputable def observer (output : FullOutput) : ProbComp Bool :=
  match context.1 with
  | .inl decision => pure decision
  | .inr ⟨start, pending⟩ => PqxdhInitialCommonSecrecy.observer source writer (marker source start) sender route decode
      (view source writer sender route decode depth remaining start) (pending.val, context.2) output

noncomputable def bad (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  (fun result => decide (target ∈ PqxdhInitialCommonSecrecy.candidates result)) <$>
    observed source writer sender route decode depth remaining context output

/-- Each branch dispatches the complete source-derived native freshness comparison, including the marker selected by the original sampled transcript. -/
theorem local_bound (target : RootOutput) (output : FullOutput) :
    (native source writer sender route decode depth remaining context target output).boolDistance
      (observer source writer sender route decode depth remaining context output) ≤
    3 * Pr{let x ← bad source writer sender route decode depth remaining context target output}[x = true].toReal := by
  rcases context with ⟨common | ⟨start, pending⟩, entry⟩
  · refine le_of_eq_of_le ?_ (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
    simp [native, observer, ProbComp.boolDistance]
  · exact PqxdhInitialCommonSecrecy.local_bound source writer (marker source start) sender route decode
      (view source writer sender route decode depth remaining start) (pending.val, entry) target output

end BeaconcryptCore.Computational.PqxdhInitialSampledParent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledParent.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledParent.local_bound
