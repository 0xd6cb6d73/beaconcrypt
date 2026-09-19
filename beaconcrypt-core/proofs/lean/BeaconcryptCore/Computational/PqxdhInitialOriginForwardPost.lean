import BeaconcryptCore.Computational.PqxdhInitialOriginContext
import BeaconcryptCore.Computational.PqxdhInitialForwardPost

/-!
The actual post source carries the full current installation/publication trace in every pending descriptor. A Beacon first-receive descriptor additionally carries the marker computed from that same supported preparation before the selected derivation. The original client observes exactly its original replies; actual successful record and finish outcomes update private metadata before its next request. Erasure and complete-continuation soundness are literal program laws, and coverage holds for all oracle replies.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost
open PqxdhInitialPostContext RawCtxForwardAnnotation RawCtxSelectedFamilyContext
variable {ι M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Spec (extra : OracleSpec ι) (M P I D K X Response Shared Result Origin : Type) (S B : Nat) :=
  RawCtxForwardAnnotation.Spec (PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B)

def plain : QueryImpl (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B)
    (OracleComp (Spec extra M P I D K X Response Shared Result Origin S B)) :=
  fun query => (Spec extra M P I D K X Response Shared Result Origin S B).query (none, query)

def selected : (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B).Domain → Bool
  | .inl query => RawCtxPendingFamilyLiveTails.selected query
  | .inr _ => false

noncomputable def record (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range request → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B))) := do
  let result ← RawCtxForwardAnnotationLift.lift (fun inner => (⟨.inl (.record request before outside inner), trace, none⟩ : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B))
    (RawCtxForwardLive.program sender route decode ((RawCtxProtocolReveals.SourceSpec S B).query request) before.roles)
  after result.1 { before with roles := result.2 } (PqxdhInitialOriginPost.record trace request result.1)

noncomputable def ownerLift (origin : Origin) (index : Fin B) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (client : OracleComp (RawCtxForwardOwner.Spec Unit (core.option.Option RawCtxWholeOwner.Decrypted))
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingOwnerTails.Owner RatchetChain Unit)) :
    OracleComp (Spec extra M P I D K X Response Shared Result Origin S B)
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingOwnerTails.Owner RatchetChain Unit) :=
  RawCtxForwardAnnotationLift.lift
    (fun inner => (⟨.inl (.finish index before control candidate outside inner), trace, some origin⟩ : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B))
    (RawCtxForwardAnnotationLift.lift (extra := RawCtxGenericFamilyRead.ReadSpec
      (RawCtxPendingOwnerQueries.Kernel RatchetChain) S B) id client)

noncomputable def finish (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B))) :
    OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :=
  match (before.roles.1.2 index).beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ (plain ∘ₛ PqxdhInitialPendingPost.preForward)
        (PqxdhBeaconPhase2Shared.prepare control (before.roles.1.2 index).beacon.identity prekey oneTime kem raw)
      match prepared with
      | none =>
          let result := PqxdhInitialGenericBeacon.finish control (before.roles.1.2 index) none
          after result.1 (PqxdhInitialPendingPost.install index before result.2) trace
      | some prepared => do
          let kernel ← simulateQ plain (PqxdhInitialPendingPost.initialForward prepared.root)
          match kernel with
          | none =>
              let result := PqxdhInitialGenericBeacon.finish control (before.roles.1.2 index) none
              after result.1 (PqxdhInitialPendingPost.install index before result.2) trace
          | some kernel => do
              let application ← simulateQ plain (PqxdhInitialPendingPost.applicationForward prepared.response)
              match application with
              | none =>
                  let result := PqxdhInitialGenericBeacon.finish control (before.roles.1.2 index) none
                  after result.1 (PqxdhInitialPendingPost.install index before result.2) trace
              | some application => do
                  let candidate := PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata
                  let result ← ownerLift (mark prepared.root) index before trace control candidate outside
                    (RawCtxForwardOwner.program candidate.server_binding.identity_key_id decode
                      (RawCtxSelectedPublicTrace.SourceSpec.query (.inl (.inr application)))
                      (PqxdhInitialGenericBeacon.localOwner candidate kernel))
                  let published := finishResult index before control candidate result
                  after published.1 published.2 (PqxdhInitialOriginContext.finishedTrace trace (some (mark prepared.root)) index published.1)
  | _ => after none (PqxdhInitialPendingPost.install index before (before.roles.1.2 index)) trace

noncomputable def program (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result) :
    NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :=
  OracleComp.recOn client (fun result state trace => pure (result, (state, trace)))
    (fun request outside recurse state trace => match request with
      | .inl (.inl query) => record sender route decode query state trace outside recurse
      | .inl (.inr query) => do
          let reply ← simulateQ plain (PqxdhInitialPendingPost.selectorForward query)
          recurse reply state trace
      | .inr (.finish index raw) => finish mark decode index raw state trace outside recurse)

/-- Untagged callbacks remain literal original source queries after annotation erasure. -/
theorem plain_erase {Value : Type}
    (client : OracleComp (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B) Value) :
    simulateQ erase (simulateQ (plain (M := M) (P := P) (Result := Result) (Origin := Origin)) client) = client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, plain, erase]
      exact bind_congr ih

private theorem ownerLift_erase (origin : Origin) (index : Fin B) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (client : OracleComp (RawCtxForwardOwner.Spec Unit (core.option.Option RawCtxWholeOwner.Decrypted))
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingOwnerTails.Owner RatchetChain Unit)) :
    simulateQ erase (ownerLift (X := X) (Response := Response) (Shared := Shared) origin index before trace control candidate outside client) =
      simulateQ PqxdhInitialPendingPost.primitiveForward (simulateQ erase client) := by
  simp only [ownerLift, RawCtxForwardAnnotationLift.erase_lift]
  have forwards : (RawCtxForwardAnnotationLift.forward : QueryImpl
      (RawCtxPendingFamilyLiveQueries.Spec RatchetChain S B)
      (OracleComp (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B))) ∘ₛ
      (RawCtxForwardAnnotationLift.forward : QueryImpl (RawCtxPendingOwnerQueries.Spec RatchetChain)
        (OracleComp (RawCtxPendingFamilyLiveQueries.Spec RatchetChain S B))) =
      PqxdhInitialPendingPost.primitiveForward := by
    funext query
    simp [QueryImpl.compose, RawCtxForwardAnnotationLift.forward, PqxdhInitialPendingPost.primitiveForward, OracleSpec.query]
  rw [← QueryImpl.simulateQ_compose, forwards]

set_option backward.isDefEq.respectTransparency false in
/-- The carried first-receive descriptor retains the actual prepared initializer marker and complete original success or failure path. -/
theorem finish_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B))) :
    simulateQ erase (finish mark decode index raw before trace outside after) =
      (PqxdhInitialFinishOrigin.owner mark PqxdhInitialPendingPost.preForward PqxdhInitialPendingPost.calls
        PqxdhInitialPendingPost.applicationForward PqxdhInitialPendingPost.initialForward decode raw (before.roles.1.2 index) >>=
          fun result => simulateQ erase (after result.1.1 (PqxdhInitialPendingPost.install index before result.1.2)
            (PqxdhInitialOriginPost.finish trace index result.2))) := by
  unfold finish PqxdhInitialFinishOrigin.owner
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [simulateQ_bind, QueryImpl.simulateQ_compose, plain_erase, bind_assoc]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => simp only [pure_bind]; rfl
    | some prepared =>
        simp only [PqxdhInitialGenericBeacon.tail, simulateQ_bind, plain_erase, bind_assoc]
        apply bind_congr
        intro kernel
        cases kernel with
        | none => simp only [pure_bind]; rfl
        | some kernel =>
            simp only [PqxdhInitialGenericBeacon.afterInitial, simulateQ_bind, plain_erase, bind_assoc]
            apply bind_congr
            intro application
            cases application with
            | none => simp only [pure_bind]; rfl
            | some application =>
                simp only [simulateQ_bind, ownerLift_erase, RawCtxForwardOwner.program_erase]
                have singleton : RawCtxPendingOwnerTails.program
                    (PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata).server_binding.identity_key_id decode
                    (RawCtxSelectedPublicTrace.SourceSpec.query (.inl (.inr application)))
                    (PqxdhInitialGenericBeacon.localOwner (PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata) kernel) =
                    (RawCtxChainOwner.rawReceive RawCtxPendingOwnerQueries.calls decode application).run
                      (PqxdhInitialGenericBeacon.localOwner (PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata) kernel) := by
                  simp [RawCtxPendingOwnerTails.program, RawCtxPendingOwnerQueries.compiler,
                    RawCtxChainOwner.ownerImpl, OracleSpec.query]
                rw [singleton, RawCtxGenericOwnerInterpretation.raw_interpretation]
                simp only [PqxdhInitialPendingPost.calls, bind_assoc, pure_bind, finishResult]
                apply bind_congr
                intro result
                simp only [PqxdhInitialFinishOrigin.tag, PqxdhInitialOriginContext.finishedTrace]
                have marker (reply : Option Pqxdh.Bytes) :
                    (if reply.isSome then some (mark prepared.root) else none) = reply.map (fun _ => mark prepared.root) := by
                  cases reply <;> rfl
                rw [marker]
  all_goals simp only [pure_bind]; rfl
/-- Construction follows the actual next original post request before continuing with its original adaptive client. -/
theorem program_query (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : (PostSpec extra S B).Domain)
    (outside : (PostSpec extra S B).Range request → OracleComp (PostSpec extra S B) Result)
    (state : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    program (X := X) (Response := Response) (Shared := Shared) mark sender route decode
      (((PostSpec extra S B).query request : OracleComp (PostSpec extra S B) _) >>= outside) state trace =
      (match request, outside with
      | .inl (.inl query), outside => record sender route decode query state trace outside
          (fun reply updated saved => program mark sender route decode (outside reply) updated saved)
      | .inl (.inr query), outside => do
          let reply ← simulateQ plain (PqxdhInitialPendingPost.selectorForward query)
          program mark sender route decode (outside reply) state trace
      | .inr (.finish index raw), outside => finish mark decode index raw state trace outside
          (fun reply updated saved => program mark sender route decode (outside reply) updated saved)) := by
  rcases request with (request | request) | request
  · rfl
  · rfl
  · cases request; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Erasing all carried descriptors reproduces the complete original adaptive post program with its exact pending requests and full state. -/
theorem program_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    simulateQ erase (program (X := X) (Response := Response) (Shared := Shared) mark sender route decode client before trace) =
      (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) client).run (before, trace) := by
  induction client using OracleComp.inductionOn generalizing before trace with
  | pure value => rfl
  | query_bind request outside ih =>
      rw [program_query]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rcases request with (request | request) | request
      · simp only [record, simulateQ_bind, RawCtxForwardAnnotationLift.erase_lift,
          RawCtxForwardLive.program_erase, RawCtxPendingFamilyLiveTails.program,
          PqxdhInitialOriginPost.compiler, StateT.run, bind_assoc, pure_bind]
        have singleton :
            (simulateQ (RawCtxPendingFamilyLiveQueries.compiler sender route decode)
              (((RawCtxProtocolReveals.SourceSpec S B).query request) : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _)).run before.roles =
              (RawCtxPendingFamilyLiveQueries.compiler sender route decode request).run before.roles := by
          simp [OracleSpec.query]
        simp only [StateT.run] at singleton
        rw [singleton]
        exact bind_congr fun reply => ih reply.1 { before with roles := reply.2 } (PqxdhInitialOriginPost.record trace request reply.1)
      · simp only [PqxdhInitialOriginPost.compiler, StateT.run, bind_assoc, pure_bind]
        exact bind_congr fun reply => ih reply before trace
      · cases request with
        | finish index raw =>
            rw [finish_erase]
            simp only [PqxdhInitialOriginPost.compiler, StateT.run, bind_assoc, pure_bind]
            exact bind_congr fun result => ih result.1.1 (PqxdhInitialPendingPost.install index before result.1.2) (PqxdhInitialOriginPost.finish trace index result.2)

private theorem sound_lift {Tag α β Value : Type} {base : OracleSpec α} {more : OracleSpec β}
    (saved : Tag → RawCtxForwardAnnotation.Frame base Value)
    (client : OracleComp (RawCtxForwardAnnotation.Spec Tag base) Value)
    (sound : Sound saved client) :
    Sound (fun tag => RawCtxForwardAnnotationLift.liftFrame (extra := more) (saved tag))
      (RawCtxForwardAnnotationLift.lift id client) := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      change (∀ tag, query.1.map id = some tag →
        (⟨.inl query.2, fun reply => simulateQ erase (RawCtxForwardAnnotationLift.lift id (next reply))⟩ :
          RawCtxForwardAnnotation.Frame (base + more) Value) = RawCtxForwardAnnotationLift.liftFrame (saved tag)) ∧ _
      refine ⟨?_, fun reply => ih reply (sound.2 reply)⟩
      intro tag present
      have original : query.1 = some tag := by simpa only [Option.map_id, id_eq] using present
      rw [← sound.1 tag original]
      simp only [RawCtxForwardAnnotationLift.liftFrame, RawCtxForwardAnnotationLift.erase_lift]
      rfl

private theorem plain_sound_bind {Value : Type}
    (saved : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B →
      RawCtxForwardAnnotation.Frame (Base extra RatchetChain I D K X Response Shared S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (client : OracleComp (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (sound : ∀ value, Sound saved (after value)) :
    Sound saved (simulateQ plain client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact sound value
  | query_bind query next ih =>
      change (∀ tag, none = some tag → _) ∧ _
      constructor
      · intro tag impossible
        cases impossible
      · exact fun reply => ih reply

set_option backward.isDefEq.respectTransparency false in
private theorem record_sound (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range request → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (afterErase : ∀ reply updated saved, simulateQ erase (after reply updated saved) =
      (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (outside reply)).run (updated, saved))
    (afterSound : ∀ reply updated saved, Sound (PqxdhInitialOriginContext.frame mark sender route decode) (after reply updated saved)) :
    Sound (PqxdhInitialOriginContext.frame mark sender route decode) (record sender route decode request before trace outside after) := by
  apply RawCtxForwardAnnotationLift.sound_lift_bind (RawCtxSelectedFamilyContext.frame sender route decode)
    (PqxdhInitialOriginContext.frame mark sender route decode) _ _ _
    (RawCtxForwardLive.program_sound sender route decode _ _) (fun result => afterSound result.1 { before with roles := result.2 } (PqxdhInitialOriginPost.record trace request result.1))
  intro tag
  simp only [PqxdhInitialOriginContext.frame, PqxdhInitialOriginContext.resume, PqxdhInitialBuilderContext.frame, PqxdhInitialPostContext.frame, RawCtxForwardAnnotationComposition.appendFrame,
    RawCtxForwardAnnotationLift.liftFrame, afterErase]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem ownerLift_sound_bind (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin B) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (afterErase : ∀ reply updated saved, simulateQ erase (after reply updated saved) =
      (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (outside reply)).run (updated, saved))
    (afterSound : ∀ reply updated saved, Sound (PqxdhInitialOriginContext.frame mark sender route decode) (after reply updated saved))
    (client : OracleComp (RawCtxForwardOwner.Spec Unit (core.option.Option RawCtxWholeOwner.Decrypted))
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingOwnerTails.Owner RatchetChain Unit))
    (innerSound : Sound (ownerFrame candidate.server_binding.identity_key_id decode) client) :
    Sound (PqxdhInitialOriginContext.frame mark sender route decode)
      (ownerLift origin index before trace control candidate outside client >>= fun result =>
        let published := finishResult index before control candidate result
        after published.1 published.2 (PqxdhInitialOriginContext.finishedTrace trace (some origin) index published.1)) := by
  apply RawCtxForwardAnnotationLift.sound_lift_bind
    (fun tag => RawCtxForwardAnnotationLift.liftFrame (ownerFrame candidate.server_binding.identity_key_id decode tag))
    (PqxdhInitialOriginContext.frame mark sender route decode) _ _ _
    (sound_lift _ _ innerSound) (fun result => afterSound _ _ _)
  intro tag
  simp only [PqxdhInitialOriginContext.frame, PqxdhInitialOriginContext.resume, PqxdhInitialBuilderContext.frame, PqxdhInitialPostContext.frame, RawCtxForwardAnnotationComposition.appendFrame,
    RawCtxForwardAnnotationLift.liftFrame, afterErase]
  have forwards : (RawCtxForwardAnnotationLift.forward : QueryImpl
      (RawCtxPendingFamilyLiveQueries.Spec RatchetChain S B)
      (OracleComp (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B))) ∘ₛ
      (RawCtxForwardAnnotationLift.forward : QueryImpl (RawCtxPendingOwnerQueries.Spec RatchetChain)
        (OracleComp (RawCtxPendingFamilyLiveQueries.Spec RatchetChain S B))) =
      PqxdhInitialPendingPost.primitiveForward := by
    funext query
    simp [QueryImpl.compose, RawCtxForwardAnnotationLift.forward, PqxdhInitialPendingPost.primitiveForward, OracleSpec.query]
  simp only [← QueryImpl.simulateQ_compose, forwards]

set_option backward.isDefEq.respectTransparency false in
private theorem finish_sound (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin B) (raw : Pqxdh.Bytes)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (afterErase : ∀ reply updated saved, simulateQ erase (after reply updated saved) =
      (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (outside reply)).run (updated, saved))
    (afterSound : ∀ reply updated saved, Sound (PqxdhInitialOriginContext.frame mark sender route decode) (after reply updated saved)) :
    Sound (PqxdhInitialOriginContext.frame mark sender route decode) (finish mark decode index raw before trace outside after) := by
  unfold finish
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    dsimp only
    rw [QueryImpl.simulateQ_compose]
    apply plain_sound_bind
    intro prepared
    cases prepared with
    | none => exact afterSound _ _ _
    | some prepared =>
        apply plain_sound_bind
        intro kernel
        cases kernel with
        | none => exact afterSound _ _ _
        | some kernel =>
            apply plain_sound_bind
            intro application
            cases application with
            | none => exact afterSound _ _ _
            | some application =>
                exact ownerLift_sound_bind mark (mark prepared.root) sender route decode index before trace control _ outside after afterErase afterSound _
                  (RawCtxForwardOwner.program_sound _ _ _ _)
  all_goals exact afterSound _ _ _

/-- Every carried pending descriptor is generated by the original full post source and names its complete future continuation. -/
theorem program_sound (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    Sound (PqxdhInitialOriginContext.frame mark sender route decode)
      (program (X := X) (Response := Response) (Shared := Shared) mark sender route decode client before trace) := by
  induction client using OracleComp.inductionOn generalizing before trace with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [program_query]
      rcases request with (request | request) | request
      · exact record_sound mark sender route decode request before trace outside _
          (fun reply updated saved => program_erase mark sender route decode (outside reply) updated saved) ih
      · exact plain_sound_bind _ _ _ (fun reply => ih reply before trace)
      · cases request with
        | finish index raw =>
            exact finish_sound mark sender route decode index raw before trace outside _
              (fun reply updated saved => program_erase mark sender route decode (outside reply) updated saved) ih

private theorem pre_covered_bind {Value : Type}
    (client : OracleComp (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) Value)
    (after : Value → OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (covered : ∀ value, RawCtxForwardCoverage.Covered selected (after value)) :
    RawCtxForwardCoverage.Covered selected
      (simulateQ (plain ∘ₛ PqxdhInitialPendingPost.preForward) client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact covered value
  | query_bind query next ih =>
      change none.isSome = false ∧ _
      exact ⟨rfl, fun reply => ih reply⟩

private theorem ownerLift_covered_bind (origin : Origin) (index : Fin B) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (afterCovered : ∀ reply updated saved, RawCtxForwardCoverage.Covered selected (after reply updated saved))
    (client : OracleComp (RawCtxForwardOwner.Spec Unit (core.option.Option RawCtxWholeOwner.Decrypted))
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingOwnerTails.Owner RatchetChain Unit))
    (innerCovered : RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected client) :
    RawCtxForwardCoverage.Covered selected
      (ownerLift origin index before trace control candidate outside client >>= fun result =>
        let published := finishResult index before control candidate result
        after published.1 published.2 (PqxdhInitialOriginContext.finishedTrace trace (some origin) index published.1)) := by
  have lifted : RawCtxForwardCoverage.Covered (RawCtxPendingFamilyLiveTails.selected (serverCount := S) (beaconCount := B))
      (RawCtxForwardAnnotationLift.lift id client) := by
    induction client using OracleComp.inductionOn with
    | pure value => trivial
    | query_bind query next ih =>
        change (query.1.map id).isSome = RawCtxPendingMixedPrefix.ownerSelected query.2 ∧ _
        exact ⟨by simpa only [Option.isSome_map] using
          (show query.1.isSome = RawCtxPendingMixedPrefix.ownerSelected query.2 from innerCovered.1), fun reply => ih reply (innerCovered.2 reply)⟩
  exact RawCtxForwardAnnotationLift.covered_lift_bind RawCtxPendingFamilyLiveTails.selected selected
    (fun _ => rfl) _ _ _ lifted (fun result => afterCovered _ _ _)

private theorem finish_covered (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (afterCovered : ∀ reply updated saved, RawCtxForwardCoverage.Covered selected (after reply updated saved)) :
    RawCtxForwardCoverage.Covered selected (finish mark decode index raw before trace outside after) := by
  unfold finish
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    apply pre_covered_bind
    intro prepared
    cases prepared with
    | none => exact afterCovered _ _ _
    | some prepared =>
        change none.isSome = false ∧ _
        refine ⟨rfl, ?_⟩
        intro kernel
        cases kernel with
        | none => exact afterCovered _ _ _
        | some kernel =>
            change none.isSome = false ∧ _
            refine ⟨rfl, ?_⟩
            intro application
            cases application with
            | none => exact afterCovered _ _ _
            | some application =>
                exact ownerLift_covered_bind (mark prepared.root) index before trace control _ outside after afterCovered _
                  (RawCtxForwardOwner.program_covered _ _ _ _)
  all_goals exact afterCovered _ _ _

/-- Every actual private derivation in the full post schedule carries its source descriptor under every reply; all preparation, initializer, read and selector callbacks remain explicit. -/
theorem program_covered (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    RawCtxForwardCoverage.Covered selected
      (program (X := X) (Response := Response) (Shared := Shared) mark sender route decode client before trace) := by
  induction client using OracleComp.inductionOn generalizing before trace with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [program_query]
      rcases request with (request | request) | request
      · exact RawCtxForwardAnnotationLift.covered_lift_bind RawCtxPendingFamilyLiveTails.selected selected
          (fun _ => rfl) _ _ _ (RawCtxForwardLive.program_covered sender route decode _ _)
          (fun result => ih result.1 { before with roles := result.2 } (PqxdhInitialOriginPost.record trace request result.1))
      · change none.isSome = false ∧ _
        exact ⟨rfl, fun reply => ih reply before trace⟩
      · cases request with
        | finish index raw => exact finish_covered mark decode index raw before trace outside _ ih


end BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.plain_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.plain_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.finish_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.finish_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.program_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.program_query

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.program_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.program_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.program_sound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost.program_covered
