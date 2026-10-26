import BeaconcryptCore.Computational.RawCtxForwardFamily
import BeaconcryptCore.Computational.RawCtxForwardAnnotationLift

/-!
The original LIVE client carries family descriptors together with its saved disclosure history and outside client. The compiler preserves the actual optional read request and reply, appends that reply to the same history, and advances the source timestamp after each complete family operation. The descriptor is constructed before any selected private response and contains the original source continuation, not a value recovered by inverting an arbitrary function.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardLive
open RawCtxSelectedFamilyContext RawCtxForwardAnnotation

abbrev Base (S B : Nat) := LivePrimitiveSpec RatchetChain S B
abbrev Spec (M P I D K Result : Type) (S B : Nat) :=
  RawCtxForwardAnnotation.Spec (Context M P I D K Result S B) (Base S B)
abbrev State (M P I D K : Type) (S B : Nat) := NativeLive M P I D K S B
abbrev SourceSpec := RawCtxProtocolReveals.SourceSpec
variable {M P I D K Result : Type} {S B : Nat}

def familyLift (request : (FamilySpec S B).Domain) (history : RawCtxProtocolReveals.History S B)
    (outside : (FamilySpec S B).Range request → OracleComp (SourceSpec S B) Result) :
    QueryImpl (RawCtxForwardFamily.Spec M P I D K ((FamilySpec S B).Range request) S B)
      (OracleComp (Spec M P I D K Result S B)) :=
  fun query => (Spec M P I D K Result S B).query
    (query.1.map (fun inner => Context.family request history outside inner), .inl query.2)

noncomputable def family
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (FamilySpec S B).Domain) (before : State M P I D K S B)
    (outside : (FamilySpec S B).Range request → OracleComp (SourceSpec S B) Result)
    (after : (FamilySpec S B).Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B)) :
    OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B) := do
  let result ← simulateQ (familyLift request before.2 outside)
    (RawCtxForwardFamily.program sender route decode ((FamilySpec S B).query request) before.1)
  after result.1 (result.2, RawCtxProtocolReveals.tick before.2)

noncomputable def program
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Result) :
    State M P I D K S B → OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B) :=
  OracleComp.recOn client (fun result state => pure (result, state))
    (fun request outside recurse state => match request with
      | .inl query => family sender route decode query state outside recurse
      | .inr query => do
          let reply ← (Spec M P I D K Result S B).query (none,
            .inr (query, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner query) state.1))
          recurse reply (state.1, RawCtxProtocolReveals.note ⟨query, reply⟩ state.2))

/-- A complete original LIVE request either runs its whole family operation or records the actual optional read before resuming the original outside client. -/
theorem program_query
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (SourceSpec S B).Domain)
    (outside : (SourceSpec S B).Range request → OracleComp (SourceSpec S B) Result) (state : State M P I D K S B) :
    program sender route decode (((SourceSpec S B).query request : OracleComp (SourceSpec S B) _) >>= outside) state =
      (match request, outside with
      | .inl query, outside => family sender route decode query state outside
          (fun reply updated => program sender route decode (outside reply) updated)
      | .inr query, outside => do
          let reply ← (Spec M P I D K Result S B).query (none,
            .inr (query, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner query) state.1))
          program sender route decode (outside reply) (state.1, RawCtxProtocolReveals.note ⟨query, reply⟩ state.2)) := by
  cases request <;> rfl

/-- Erasing carried family metadata keeps the full original family operation, original history tick and already compiled LIVE continuation. -/
theorem family_erase
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (FamilySpec S B).Domain) (before : State M P I D K S B)
    (outside : (FamilySpec S B).Range request → OracleComp (SourceSpec S B) Result)
    (after : (FamilySpec S B).Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B))
    (innerErase : simulateQ erase (RawCtxForwardFamily.program sender route decode
      ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _) before.1) =
        RawCtxPendingFamilyTails.program sender route decode ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _) before.1) :
    simulateQ erase (family sender route decode request before outside after) =
      (simulateQ RawCtxPendingFamilyLiveQueries.primitiveForward
        (RawCtxPendingFamilyTails.program sender route decode ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _) before.1) >>=
          fun result => simulateQ erase (after result.1 (result.2, RawCtxProtocolReveals.tick before.2))) := by
  change simulateQ erase (RawCtxForwardAnnotationLift.lift (fun inner => Context.family request before.2 outside inner)
    (RawCtxForwardFamily.program sender route decode ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _) before.1) >>=
      fun result => after result.1 (result.2, RawCtxProtocolReveals.tick before.2)) = _
  simp only [simulateQ_bind, RawCtxForwardAnnotationLift.erase_lift, innerErase]
  rfl

/-- A forward LIVE descriptor keeps the entire saved family callback, the original disclosure history and the complete original outside LIVE program. -/
theorem family_sound
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (FamilySpec S B).Domain) (before : State M P I D K S B)
    (outside : (FamilySpec S B).Range request → OracleComp (SourceSpec S B) Result)
    (after : (FamilySpec S B).Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B))
    (innerSound : Sound (familyFrame sender route decode) (RawCtxForwardFamily.program sender route decode
      ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _) before.1))
    (afterErase : ∀ reply updated, simulateQ erase (after reply updated) =
      RawCtxPendingFamilyLiveTails.program sender route decode (outside reply) updated)
    (afterSound : ∀ reply updated, Sound (frame sender route decode) (after reply updated)) :
    Sound (frame sender route decode) (family sender route decode request before outside after) := by
  change Sound (frame sender route decode)
    (RawCtxForwardAnnotationLift.lift (fun inner => Context.family request before.2 outside inner)
      (RawCtxForwardFamily.program sender route decode ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _) before.1) >>=
        fun result => after result.1 (result.2, RawCtxProtocolReveals.tick before.2))
  apply RawCtxForwardAnnotationLift.sound_lift_bind (familyFrame sender route decode) (frame sender route decode)
    _ _ _ innerSound (fun result => afterSound result.1 (result.2, RawCtxProtocolReveals.tick before.2))
  intro tag
  simp only [frame, RawCtxForwardAnnotationComposition.appendFrame, RawCtxForwardAnnotationLift.liftFrame]
  apply congrArg (fun next : (Base S B).Range (.inl (familyFrame sender route decode tag).1) →
    OracleComp (Base S B) (Result × State M P I D K S B) =>
      (⟨.inl (familyFrame sender route decode tag).1, next⟩ : RawCtxForwardAnnotation.Frame (Base S B) (Result × State M P I D K S B)))
  funext reply
  simp only [RawCtxPendingFamilyLiveTails.liftFamily, afterErase]
  rfl

/-- Forwarding a complete family operation retains a descriptor at every private callback and keeps full coverage after the original history update. -/
theorem family_covered
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (FamilySpec S B).Domain) (before : State M P I D K S B)
    (outside : (FamilySpec S B).Range request → OracleComp (SourceSpec S B) Result)
    (after : (FamilySpec S B).Range request → State M P I D K S B →
      OracleComp (Spec M P I D K Result S B) (Result × State M P I D K S B))
    (innerCovered : RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected
      (RawCtxForwardFamily.program sender route decode
        ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _) before.1))
    (afterCovered : ∀ reply updated, RawCtxForwardCoverage.Covered RawCtxPendingFamilyLiveTails.selected (after reply updated)) :
    RawCtxForwardCoverage.Covered RawCtxPendingFamilyLiveTails.selected
      (family sender route decode request before outside after) := by
  change RawCtxForwardCoverage.Covered RawCtxPendingFamilyLiveTails.selected
    (RawCtxForwardAnnotationLift.lift (fun inner => Context.family request before.2 outside inner)
      (RawCtxForwardFamily.program sender route decode ((FamilySpec S B).query request : OracleComp (FamilySpec S B) _) before.1) >>=
        fun result => after result.1 (result.2, RawCtxProtocolReveals.tick before.2))
  exact RawCtxForwardAnnotationLift.covered_lift_bind RawCtxPendingMixedPrefix.ownerSelected
    RawCtxPendingFamilyLiveTails.selected (fun _ => rfl) _ _ _ innerCovered
    (fun result => afterCovered result.1 (result.2, RawCtxProtocolReveals.tick before.2))

/-- The entire annotated LIVE source erases to its exact original family, optional disclosures, history and adaptive outside program. -/
theorem program_erase
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Result) (state : State M P I D K S B) :
    simulateQ erase (program sender route decode client state) =
      RawCtxPendingFamilyLiveTails.program sender route decode client state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind request outside ih =>
    rw [program_query]
    cases request with
    | inl query =>
      dsimp only
      rw [family_erase sender route decode query state outside _ (RawCtxForwardFamily.program_erase sender route decode _ _),
        RawCtxPendingFamilyLiveTails.program_original]
      simp only [RawCtxPendingFamilyTails.program, simulateQ_spec_query, RawCtxPendingFamilyLiveTails.liftFamily]
      exact bind_congr fun result => ih result.1 (result.2, RawCtxProtocolReveals.tick state.2)
    | inr query =>
      dsimp only
      rw [RawCtxPendingFamilyLiveTails.program_read]
      simp only [simulateQ_bind, simulateQ_spec_query, erase]
      exact bind_congr fun reply => ih reply (state.1, RawCtxProtocolReveals.note ⟨query, reply⟩ state.2)

/-- Every descriptor carried by the actual entire LIVE source names its exact full family continuation and saved original history. -/
theorem program_sound
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Result) (state : State M P I D K S B) :
    Sound (frame sender route decode) (program sender route decode client state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => exact sound_pure _ _
  | query_bind request outside ih =>
    rw [program_query]
    cases request with
    | inl query =>
      dsimp only
      exact family_sound sender route decode query state outside _ (RawCtxForwardFamily.program_sound sender route decode _ _)
        (fun reply updated => program_erase sender route decode (outside reply) updated) ih
    | inr query =>
      dsimp only
      rw [sound_query]
      constructor
      · intro tag impossible
        cases impossible
      · intro reply
        exact ih reply (state.1, RawCtxProtocolReveals.note ⟨query, reply⟩ state.2)

/-- Every private derivation in the entire original LIVE source carries its descriptor under every adaptive reply; public and read callbacks carry none. -/
theorem program_covered
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec S B) Result) (state : State M P I D K S B) :
    RawCtxForwardCoverage.Covered RawCtxPendingFamilyLiveTails.selected (program sender route decode client state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => exact RawCtxForwardCoverage.covered_pure _ _
  | query_bind request outside ih =>
    rw [program_query]
    cases request with
    | inl query =>
      dsimp only
      exact family_covered sender route decode query state outside _ (RawCtxForwardFamily.program_covered sender route decode _ _) ih
    | inr query =>
      dsimp only
      rw [RawCtxForwardCoverage.covered_query]
      exact ⟨rfl, fun reply => ih reply (state.1, RawCtxProtocolReveals.note ⟨query, reply⟩ state.2)⟩

end BeaconcryptCore.Computational.RawCtxForwardLive

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLive.program_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLive.program_query
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLive.family_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLive.family_erase
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLive.family_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLive.family_sound
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLive.family_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLive.family_covered
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLive.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLive.program_erase
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLive.program_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLive.program_sound
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardLive.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardLive.program_covered
