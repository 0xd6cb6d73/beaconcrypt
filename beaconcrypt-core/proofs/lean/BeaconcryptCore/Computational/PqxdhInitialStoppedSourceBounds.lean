import BeaconcryptCore.Computational.PqxdhInitialBuilderCertificates
import BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets
import BeaconcryptCore.Computational.PqxdhInitialOriginContext
import BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler

/-!
The exact saved pending completion is bounded before interpreting any primitive. It keeps every remaining receive derivation, optional opening or sealing, publication and original adaptive post request. The certificate comes from the actual source descriptor and preserves the distinction between protocol callback counts and the cost of interpreting those callbacks.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds
open RawCtxSelectedFamilyContext RawCtxFamilyPrimitiveBudgets RawCtxFamilyCompletionBudgets
open PqxdhInitialPendingPost PqxdhInitialPostContext PqxdhOrderedChainHybrids
variable {ι Chain M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}

private instance : Fintype Class :=
  ⟨{.kdf, .seal, .open, .coin, .hash, .hkdf, .read}, by intro selected; cases selected <;> simp⟩

private theorem partition_total {κ Kind Value : Type} {spec : OracleSpec κ} [Fintype Kind] [DecidableEq Kind]
    (classify : spec.Domain → Kind) (client : OracleComp spec Value) (budget : Kind → Nat)
    (bounded : ∀ kind, client.IsQueryBoundP (fun query => classify query = kind) (budget kind)) :
    client.IsTotalQueryBound (FinitePartitionQueryBounds.bill (fun _ => 1) budget) := by
  refine IsQueryBound.proj (FinitePartitionQueryBounds.bill (fun _ => 1)) ?_ ?_
    (FinitePartitionQueryBounds.structural classify client budget bounded)
  all_goals intro query current positive
  all_goals have exactBill := FinitePartitionQueryBounds.bill_step (fun _ => 1) current (classify query) positive
  all_goals omega

set_option backward.isDefEq.respectTransparency false in
/-- Removing enriched pending fields retains exactly one original callback for every pending callback, under every reply. -/
theorem erase_total {Value : Type} (client : OracleComp (RawCtxPendingOwnerQueries.Spec Chain) Value) (budget : Nat) :
    (simulateQ RawCtxPendingOwnerQueries.erase client).IsTotalQueryBound budget ↔ client.IsTotalQueryBound budget := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [simulateQ_pure]; rfl
  | query_bind query next ih =>
      rcases query with (pending | opening) | ((pending | sealing) | publicQuery)
      all_goals simp only [simulateQ_bind, simulateQ_spec_query, RawCtxPendingOwnerQueries.erase,
        isTotalQueryBound_query_bind_iff, ih]
      all_goals rfl

/-- A carried quiet owner finishes at most254 remaining receive derivations and one opening, or one sealing, without a fresh selected request. -/
theorem owner_total {Metadata Value : Type} (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (context : OwnerContext Metadata Value) (quiet : RawCtxQuietOwnerTails.Quiet context) (material : Material) :
    (ownerStopped sender decode context material).IsTotalQueryBound 255 := by
  apply (erase_total _ 255).mp
  apply (partition_total primitiveClass _ (ownerReserve context)
    (fun kind => owner_stopped sender decode context quiet material kind)).mono
  cases context <;> simp [FinitePartitionQueryBounds.bill, ownerReserve, receiveReserve, sendReserve,
    show (Finset.univ : Finset Class) = {.kdf, .seal, .open, .coin, .hash, .hkdf, .read} from rfl]

/-- Quiet indexed Server or Beacon publication retains the same pending completion budget and all role state. -/
theorem family_total (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : FamilyContext M P I D K Result S B)
    (quiet : RawCtxQuietFamilyTails.Quiet context) (material : Material) :
    (familyStopped sender route decode context material).IsTotalQueryBound 255 := by
  apply (erase_total _ 255).mp
  apply (partition_total primitiveClass _ (familyReserve context)
    (fun kind => family_stopped sender route decode context quiet material kind)).mono
  rcases context with ⟨request, before, index, outside, ⟨request, before, kid, peer, outside, inner⟩⟩ |
    ⟨request, before, index, control, associatedData, outside, inner⟩
  all_goals cases inner
  all_goals simp [FinitePartitionQueryBounds.bill, familyReserve, serverReserve, ownerReserve,
    receiveReserve, sendReserve,
    show (Finset.univ : Finset Class) = {.kdf, .seal, .open, .coin, .hash, .hkdf, .read} from rfl]

private theorem one_query {κ : Type} {spec : OracleSpec κ} (query : spec.Domain) :
    OracleComp.IsTotalQueryBound (spec.query query : OracleComp spec (spec.Range query)) 1 :=
  ⟨by change 0 < 1; decide, fun _ => True.intro⟩

/-- The actual single-record descriptor adds no saved LIVE requests after its bounded pending completion. -/
theorem live_total (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B)
    (quiet : PqxdhInitialPostCertificates.LiveQuiet context) (material : Material) :
    (RawCtxSelectedFamilyContext.stopped sender route decode context material).IsTotalQueryBound 255 := by
  cases context with
  | family request history outside inner =>
      unfold RawCtxSelectedFamilyContext.stopped RawCtxPendingFamilyLiveTails.liftFamily
      apply isTotalQueryBound_bind (n₁ := 255) (n₂ := 0)
      · exact PqxdhBeaconPhase2Bounds.simulate_total _ _ 255
          (family_total sender route decode inner quiet.2 material) (fun _ => one_query _)
      · intro result
        obtain ⟨value, pureOutside⟩ := RawCtxQuietOwnerTails.zero_pure (outside result.1) (quiet.1 result.1)
        simp only [RawCtxPendingFamilyLiveTails.afterFamily, pureOutside]
        trivial

/-- Every actual saved post cut pays its pending completion and the source-certified complete original post continuation. -/
theorem post_total (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : PqxdhInitialPostContext.Context extra M P I D K Result S B)
    (qPost : Nat) (fits : PqxdhInitialPostCertificates.Fits qPost context) (material : Material) :
    (PqxdhInitialPostContext.stopped (X := X) (Response := Response) (Shared := Shared)
      sender route decode context material).IsTotalQueryBound (255 + qPost * 67) := by
  cases context with
  | record request before outside inner =>
      unfold PqxdhInitialPostContext.stopped
      apply isTotalQueryBound_bind (n₁ := 255) (n₂ := qPost * 67)
      · exact PqxdhBeaconPhase2Bounds.simulate_total liveForward _ 255
          (live_total sender route decode inner fits.2 material) (fun _ => one_query _)
      · intro result
        exact PqxdhInitialPendingSourceBounds.program_total sender route decode (outside result.1) qPost (fits.1 result.1) _
  | finish index before control candidate outside inner =>
      unfold PqxdhInitialPostContext.stopped
      apply isTotalQueryBound_bind (n₁ := 255) (n₂ := qPost * 67)
      · exact PqxdhBeaconPhase2Bounds.simulate_total primitiveForward _ 255
          (owner_total candidate.server_binding.identity_key_id decode inner fits.2 material) (fun _ => one_query _)
      · intro result
        exact PqxdhInitialPendingSourceBounds.program_total sender route decode _ qPost (fits.1 _) _

private theorem after_send_total (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (metadata : P) (state : PqxdhInitialGenericPublication.State (KernelOf Chain) M P (List Pqxdh.Bytes))
    (result : KernelOf Chain × Option RawCtxSourceSend.Encrypted) :
    (PqxdhInitialBuilderContext.afterSend
      (auxForward (Chain := Chain) (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B))
      candidate authenticated metadata state result).IsTotalQueryBound 2 := by
  unfold PqxdhInitialBuilderContext.afterSend
  apply isTotalQueryBound_bind (n₁ := 1) (n₂ := 1) (one_query _)
  intro erased
  cases result.2 with
  | none => trivial
  | some encrypted => exact isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (one_query _) (fun serialized => by cases serialized <;> trivial)

/-- The saved first-send completion keeps erasure and serialization before the actual bounded original post continuation. -/
theorem complete_total (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : Front Chain M P I D K S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : PqxdhInitialBuilderContext.BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (result : KernelOf Chain × Option RawCtxSourceSend.Encrypted) :
    (PqxdhInitialBuilderContext.complete (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before candidate authenticated metadata outside result).IsTotalQueryBound (2 + qPost * 67) := by
  apply isTotalQueryBound_bind (n₁ := 2) (n₂ := qPost * 67)
  · exact after_send_total candidate authenticated metadata _ result
  · intro published
    exact PqxdhInitialPendingSourceBounds.program_total sender route decode _ qPost (bounded _) _

/-- A first-builder cut pays one sealing plus its complete publication/post continuation; every later cut pays the source-certified receive-or-send reserve. -/
theorem stopped_total (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : PqxdhInitialBuilderContext.Context extra M P I D K Result S B)
    (qPost : Nat) (fits : PqxdhInitialBuilderCertificates.Fits qPost context) (material : Material) :
    (PqxdhInitialBuilderContext.stopped (X := X) (Response := Response) (Shared := Shared)
      sender route decode context material).IsTotalQueryBound (255 + qPost * 67) := by
  cases context with
  | inl context => exact post_total sender route decode context qPost fits material
  | inr builder =>
      apply (isTotalQueryBound_bind (n₁ := 1) (n₂ := 2 + qPost * 67) (one_query _) ?_).mono (by omega)
      intro sealed
      exact complete_total sender route decode builder.index _ builder.candidate builder.authenticated
        builder.metadata builder.outside qPost fits _

/-- The complete source origin/publication transcript preserves the derived pending completion and outside-source bill. -/
theorem origin_total {Origin : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (qPost : Nat) (fits : PqxdhInitialBuilderCertificates.Fits qPost context.original) (material : Material) :
    (PqxdhInitialOriginContext.stopped (X := X) (Response := Response) mark sender route decode context material).IsTotalQueryBound
      (255 + qPost * 67) := by
  apply (isQueryBoundP_true_iff _ _).mp
  rw [PqxdhInitialOriginContext.stopped_query_bound]
  exact (stopped_total sender route decode context.original qPost fits material).isQueryBoundP

/-- The concrete ordinary observer adapter pays at most two callbacks for each source-bounded pending callback, including initializer audit and full origin metadata. -/
theorem compiled_total {Origin : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (qPost : Nat) (fits : PqxdhInitialBuilderCertificates.Fits qPost context.original) (material : Material) :
    (simulateQ PqxdhInitialParentObserverCompiler.compiler
      (PqxdhInitialOriginContext.stopped (X := X) (Response := Response) mark sender route decode context material)).IsTotalQueryBound
      (2 * (255 + qPost * 67)) :=
  PqxdhInitialParentObserverCompiler.program_bound _ _ (origin_total mark sender route decode context qPost fits material)

end BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.erase_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.erase_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.owner_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.owner_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.family_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.family_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.live_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.live_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.post_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.post_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.complete_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.complete_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.stopped_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.stopped_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.origin_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.origin_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.compiled_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds.compiled_total
