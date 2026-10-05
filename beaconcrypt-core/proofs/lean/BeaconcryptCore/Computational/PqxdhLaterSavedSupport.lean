import BeaconcryptCore.Computational.PqxdhLaterSavedContext

/-! The actual complete later-material sampler supplies the exact quiet-continuation and raw-provenance facts used by saved descriptor completion. Common and cached decisions remain in the same distribution. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedSupport
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhCorrelatedExpand
open PqxdhErasedParentSample
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (depth qPost : Nat)
local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (A := A) (N := N) (S := S) (B := B)
local notation "Packet" => PqxdhErasedParentSample.Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)

/-- An actual missing-parent output inherits the original all-reply Post allowance and quiet inner tail. -/
theorem sample_one_fits (start : Start) (pending : Pending)
    (bounded : ∀ reply, (start.1.post reply).IsTotalQueryBound qPost)
    (supported : Sum.inr pending ∈ support (sampleOne source writer sender route read depth start)) :
    PqxdhInitialOriginCertificates.Fits qPost pending.1 := by
  unfold sampleOne at supported
  have carried := (PqxdhInitialPreparedParent.supported_pending source writer _ _ _ _ _ _ sender route read _ _
    depth _ pending.2 pending.1).mp supported
  exact PqxdhInitialNativeAuditCarried.carried_fits source writer _ _ _ _ _ _ sender route read _ depth (depth + 1)
    qPost bounded _ pending.2 pending.1 carried.1

def PacketFits (qPost : Nat) : Packet → Prop
  | .inl _ => True
  | .inr (_, .inl _) => True
  | .inr (_, .inr pending) => PqxdhInitialOriginCertificates.Fits qPost pending.1

/-- The complete source sampler retains every original common decision and supplies its continuation certificate on each pending branch. -/
theorem sample_fits
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (bounded : ∀ input, Sum.inr input ∈ support prior → ∀ reply, (input.post reply).IsTotalQueryBound qPost)
    (packet : Packet) (supported : packet ∈ support (sample source writer sender route read depth prior)) :
    PacketFits qPost packet := by
  unfold sample at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨context, reached, output, _, supported⟩ := supported
  cases context with
  | inl decision =>
      simp only [mem_support_pure_iff] at supported
      subst packet
      trivial
  | inr input =>
      simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨value, sampled, rfl⟩ := supported
      cases value with
      | inl decision => trivial
      | inr pending =>
          exact sample_one_fits source writer sender route read depth qPost (input, output) pending
            (bounded input reached) sampled

/-- Removing the unused earlier cache does not change the saved continuation certificate. -/
theorem normalized_fits (packet : Packet) : PacketFits qPost (normalize packet) ↔ PacketFits qPost packet := by
  rcases packet with common | ⟨start, common | pending⟩ <;> rfl

/-- The complete material sampler supplies both descriptor certificates and the literal retained-parent address; no pending outcome is conditioned into the sampler. -/
theorem material_scope
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (bounded : ∀ input, Sum.inr input ∈ support prior → ∀ reply, (input.post reply).IsTotalQueryBound qPost)
    (context : PqxdhErasedParentMaterial.MaterialContext (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
      (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B))
    (supported : context ∈ support (PqxdhErasedParentMaterial.prepare source writer sender route read depth prior)) :
    PacketFits qPost context.1.1.1 ∧ PqxdhPreparedDescriptorScope.PacketValid read context.1.1.1 ∧
      context.1.1.2.address = address context.1.1.1 := by
  unfold PqxdhErasedParentMaterial.prepare at supported
  simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨packet, sampled, parent, _, nonce, _, chain, _, rfl⟩ := supported
  refine ⟨(normalized_fits qPost packet).mpr
    (sample_fits source writer sender route read depth qPost prior bounded packet sampled), ?_, ?_⟩
  · exact (PqxdhPreparedDescriptorScope.normalized_valid read packet).mpr
      (PqxdhPreparedDescriptorScope.sample_valid source writer sender route read depth prior packet sampled)
  · exact (address_normalize packet).symm

end BeaconcryptCore.Computational.PqxdhLaterSavedSupport

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSupport.sample_one_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSupport.sample_one_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSupport.sample_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSupport.sample_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSupport.normalized_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSupport.normalized_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSupport.material_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSupport.material_scope
