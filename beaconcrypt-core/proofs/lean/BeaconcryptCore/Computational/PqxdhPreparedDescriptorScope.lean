import BeaconcryptCore.Computational.PqxdhInitialDescriptorScope
import BeaconcryptCore.Computational.PqxdhErasedParentMaterial

/-!
The actual audited source cut and missing-parent preparation inherit the raw receive provenance certificate of their literal saved descriptor. All source callbacks, initializer audits, retained private states, caches and common branches remain the original samplers.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope
open PqxdhJointKdfGame PqxdhInitialBeaconAmbient PqxdhInitialNativeAuditCarried
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
  (execution : Execution extra M P I D K Result Origin S B)

/-- The original audited native sampler returns its own descriptor with the actual raw admission facts; its complete private state and chronological audit need no extra invariant. -/
theorem carried_valid (depth stage : Nat) (state reached : PqxdhInitialNativeAudit.State A N C)
    (context : Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (carried source writer pre application initial selector aux mark sender route read execution depth stage state)) :
    PqxdhInitialDescriptorScope.Valid read context :=
  PqxdhInitialDescriptorScope.carried_valid source mark execution.origin sender route read
    execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace
    _ _ _ state reached context supported

/-- The exact missing-parent preparation returns the same certified descriptor; completed and cached branches remain in its original sampler and cannot masquerade as pending outputs. -/
theorem prepared_valid
    (observe : PqxdhInitialPreparedParent.Output M P I D K Result Origin A N C S B → ProbComp Bool)
    (depth : Nat) (state reached : PqxdhInitialNativeAudit.State A N C)
    (context : Context extra M P I D K Result Origin S B)
    (supported : Sum.inr (context, reached) ∈ support
      (PqxdhInitialPreparedParent.prepare source writer pre application initial selector aux mark sender route read observe execution depth state)) :
    PqxdhInitialDescriptorScope.Valid read context :=
  carried_valid source writer pre application initial selector aux mark sender route read execution depth (depth + 1) state reached context
    ((PqxdhInitialPreparedParent.supported_pending source writer pre application initial selector aux mark sender route read observe execution depth state reached context).mp supported).1

/-- The concrete source-shaped preparation used by the later message-key game supplies the raw certificate with its exact initializer, root state, callbacks and saved continuation. -/
theorem sample_one_valid (depth : Nat)
    (start : PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B))
    (pending : PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (A := A) (N := N) (S := S) (B := B))
    (supported : Sum.inr pending ∈ support (PqxdhErasedParentSample.sampleOne source writer sender route read depth start)) :
    PqxdhInitialDescriptorScope.Valid read pending.1 := by
  unfold PqxdhErasedParentSample.sampleOne at supported
  exact prepared_valid source writer _ _ _ _ _ _ sender route read _ _ depth _ pending.2 pending.1 supported

def PacketValid (read : RawCtxReceive.FrameDecoder) : PqxdhErasedParentSample.Packet
    (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
    (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) → Prop
  | .inl _ => True
  | .inr (_, .inl _) => True
  | .inr (_, .inr pending) => PqxdhInitialDescriptorScope.Valid read pending.1

/-- Every supported output of the complete concrete later-message preparation has the required raw provenance on its pending branch. The prior, shared expansion, original source order and all common outcomes are unrestricted and unchanged. -/
theorem sample_valid (depth : Nat)
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (packet : PqxdhErasedParentSample.Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B))
    (supported : packet ∈ support (PqxdhErasedParentSample.sample source writer sender route read depth prior)) :
    PacketValid read packet := by
  unfold PqxdhErasedParentSample.sample at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨context, _, output, _, supported⟩ := supported
  cases context with
  | inl decision =>
      simp only [mem_support_pure_iff] at supported
      rw [supported]
      trivial
  | inr input =>
      simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨value, sampled, rfl⟩ := supported
      cases value with
      | inl decision => trivial
      | inr pending => exact sample_one_valid source writer sender route read depth (input, output) pending sampled

/-- Dropping the unused earlier cache field leaves the actual retained descriptor and its raw certificate unchanged. -/
theorem normalized_valid
    (packet : PqxdhErasedParentSample.Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)) :
    PacketValid read (PqxdhErasedParentSample.normalize packet) ↔ PacketValid read packet := by
  rcases packet with common | ⟨start, common | pending⟩ <;> rfl

/-- The complete existing material preparation supplies a certified saved raw descriptor beside the jointly retained predecessor, nonce and next chain. Every original common/cached outcome remains included. -/
theorem material_valid (depth : Nat)
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (context : PqxdhErasedParentMaterial.MaterialContext (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B))
    (supported : context ∈ support (PqxdhErasedParentMaterial.prepare source writer sender route read depth prior)) :
    PacketValid read context.1.1.1 := by
  unfold PqxdhErasedParentMaterial.prepare at supported
  simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨packet, sampled, parent, _, nonce, _, chain, _, rfl⟩ := supported
  exact (normalized_valid read packet).mpr (sample_valid source writer sender route read depth prior packet sampled)

end BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.carried_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.carried_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.prepared_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.prepared_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.sample_one_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.sample_one_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.sample_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.sample_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.normalized_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.normalized_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.material_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope.material_valid
