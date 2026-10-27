import BeaconcryptCore.Computational.PqxdhInitialPostContext

/-!
Source construction attaches a typed descriptor to every private derivation while retaining the original whole post continuation. Record descriptors use the checked LIVE compiler for one original request. Initial Beacon receive descriptors use the checked owner compiler after the actual preparation, initializer and application callbacks. Every other callback remains explicit and untagged.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialForwardPost
open PqxdhInitialPostContext RawCtxForwardAnnotation RawCtxSelectedFamilyContext
variable {ι M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Spec (extra : OracleSpec ι) (M P I D K X Response Shared Result : Type) (S B : Nat) :=
  RawCtxForwardAnnotation.Spec (PqxdhInitialPostContext.Context extra M P I D K Result S B)
    (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B)

def plain : QueryImpl (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B)
    (OracleComp (Spec extra M P I D K X Response Shared Result S B)) :=
  fun query => (Spec extra M P I D K X Response Shared Result S B).query (none, query)

def selected : (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B).Domain → Bool
  | .inl query => RawCtxPendingFamilyLiveTails.selected query
  | .inr _ => false

noncomputable def record (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : NativeFront M P I D K S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range request → NativeFront M P I D K S B →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B)) := do
  let result ← RawCtxForwardAnnotationLift.lift (fun inner => PqxdhInitialPostContext.Context.record request before outside inner)
    (RawCtxForwardLive.program sender route decode ((RawCtxProtocolReveals.SourceSpec S B).query request) before.roles)
  after result.1 { before with roles := result.2 }

noncomputable def ownerLift (index : Fin B) (before : NativeFront M P I D K S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (client : OracleComp (RawCtxForwardOwner.Spec Unit (core.option.Option RawCtxWholeOwner.Decrypted))
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingOwnerTails.Owner RatchetChain Unit)) :
    OracleComp (Spec extra M P I D K X Response Shared Result S B)
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingOwnerTails.Owner RatchetChain Unit) :=
  RawCtxForwardAnnotationLift.lift
    (fun inner => PqxdhInitialPostContext.Context.finish index before control candidate outside inner)
    (RawCtxForwardAnnotationLift.lift (extra := RawCtxGenericFamilyRead.ReadSpec
      (RawCtxPendingOwnerQueries.Kernel RatchetChain) S B) id client)

noncomputable def finish (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B)) :
    OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B) :=
  match (before.roles.1.2 index).beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ (plain ∘ₛ PqxdhInitialPendingPost.preForward)
        (PqxdhBeaconPhase2Shared.prepare control (before.roles.1.2 index).beacon.identity prekey oneTime kem raw)
      match prepared with
      | none =>
          let result := PqxdhInitialGenericBeacon.finish control (before.roles.1.2 index) none
          after result.1 (PqxdhInitialPendingPost.install index before result.2)
      | some prepared => do
          let kernel ← simulateQ plain (PqxdhInitialPendingPost.initialForward prepared.root)
          match kernel with
          | none =>
              let result := PqxdhInitialGenericBeacon.finish control (before.roles.1.2 index) none
              after result.1 (PqxdhInitialPendingPost.install index before result.2)
          | some kernel => do
              let application ← simulateQ plain (PqxdhInitialPendingPost.applicationForward prepared.response)
              match application with
              | none =>
                  let result := PqxdhInitialGenericBeacon.finish control (before.roles.1.2 index) none
                  after result.1 (PqxdhInitialPendingPost.install index before result.2)
              | some application => do
                  let candidate := PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata
                  let result ← ownerLift index before control candidate outside
                    (RawCtxForwardOwner.program candidate.server_binding.identity_key_id decode
                      (RawCtxSelectedPublicTrace.SourceSpec.query (.inl (.inr application)))
                      (PqxdhInitialGenericBeacon.localOwner candidate kernel))
                  let published := finishResult index before control candidate result
                  after published.1 published.2
  | _ => after none (PqxdhInitialPendingPost.install index before (before.roles.1.2 index))

noncomputable def program (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result) :
    NativeFront M P I D K S B →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B) :=
  OracleComp.recOn client (fun result state => pure (result, state))
    (fun request outside recurse state => match request with
      | .inl (.inl query) => record sender route decode query state outside recurse
      | .inl (.inr query) => do
          let reply ← simulateQ plain (PqxdhInitialPendingPost.selectorForward query)
          recurse reply state
      | .inr (.finish index raw) => finish decode index raw state outside recurse)

/-- Untagged callbacks remain literal original source queries after annotation erasure. -/
theorem plain_erase {Value : Type}
    (client : OracleComp (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B) Value) :
    simulateQ erase (simulateQ (plain (M := M) (P := P) (Result := Result)) client) = client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, plain, erase]
      exact bind_congr ih

private theorem ownerLift_erase (index : Fin B) (before : NativeFront M P I D K S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (client : OracleComp (RawCtxForwardOwner.Spec Unit (core.option.Option RawCtxWholeOwner.Decrypted))
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingOwnerTails.Owner RatchetChain Unit)) :
    simulateQ erase (ownerLift (X := X) (Response := Response) (Shared := Shared) index before control candidate outside client) =
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
/-- Annotation erasure preserves the actual whole first-receive attempt, including inactive history ticks and every original callback. -/
theorem finish_erase (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B)) :
    simulateQ erase (finish decode index raw before outside after) =
      (PqxdhInitialGenericBeacon.owner PqxdhInitialPendingPost.preForward PqxdhInitialPendingPost.calls
        PqxdhInitialPendingPost.applicationForward PqxdhInitialPendingPost.initialForward decode raw (before.roles.1.2 index) >>=
          fun result => simulateQ erase (after result.1 (PqxdhInitialPendingPost.install index before result.2))) := by
  unfold finish PqxdhInitialGenericBeacon.owner
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [simulateQ_bind, QueryImpl.simulateQ_compose, plain_erase, bind_assoc]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => simp only [pure_bind]
    | some prepared =>
        simp only [PqxdhInitialGenericBeacon.tail, simulateQ_bind, plain_erase, bind_assoc]
        apply bind_congr
        intro kernel
        cases kernel with
        | none => simp only [pure_bind]
        | some kernel =>
            simp only [PqxdhInitialGenericBeacon.afterInitial, simulateQ_bind, plain_erase, bind_assoc]
            apply bind_congr
            intro application
            cases application with
            | none => simp only [pure_bind]
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
  all_goals simp only [pure_bind]

/-- Construction follows the actual next original post request before continuing with its original adaptive client. -/
theorem program_query (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : (PostSpec extra S B).Domain)
    (outside : (PostSpec extra S B).Range request → OracleComp (PostSpec extra S B) Result)
    (state : NativeFront M P I D K S B) :
    program (X := X) (Response := Response) (Shared := Shared) sender route decode
      (((PostSpec extra S B).query request : OracleComp (PostSpec extra S B) _) >>= outside) state =
      (match request, outside with
      | .inl (.inl query), outside => record sender route decode query state outside
          (fun reply updated => program sender route decode (outside reply) updated)
      | .inl (.inr query), outside => do
          let reply ← simulateQ plain (PqxdhInitialPendingPost.selectorForward query)
          program sender route decode (outside reply) state
      | .inr (.finish index raw), outside => finish decode index raw state outside
          (fun reply updated => program sender route decode (outside reply) updated)) := by
  rcases request with (request | request) | request
  · rfl
  · rfl
  · cases request; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Erasing all carried descriptors reproduces the complete original adaptive post program with its exact pending requests and full state. -/
theorem program_erase (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) :
    simulateQ erase (program (X := X) (Response := Response) (Shared := Shared) sender route decode client before) =
      (simulateQ (PqxdhInitialPendingPost.compiler sender route decode) client).run before := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind request outside ih =>
      rw [program_query]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rcases request with (request | request) | request
      · simp only [record, simulateQ_bind, RawCtxForwardAnnotationLift.erase_lift,
          RawCtxForwardLive.program_erase, RawCtxPendingFamilyLiveTails.program,
          PqxdhInitialPendingPost.compiler, StateT.run, bind_assoc, pure_bind]
        have singleton :
            (simulateQ (RawCtxPendingFamilyLiveQueries.compiler sender route decode)
              (((RawCtxProtocolReveals.SourceSpec S B).query request) : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _)).run before.roles =
              (RawCtxPendingFamilyLiveQueries.compiler sender route decode request).run before.roles := by
          simp [OracleSpec.query]
        simp only [StateT.run] at singleton
        rw [singleton]
        exact bind_congr fun reply => ih reply.1 { before with roles := reply.2 }
      · simp only [PqxdhInitialPendingPost.compiler, StateT.run, bind_assoc, pure_bind]
        exact bind_congr fun reply => ih reply before
      · cases request with
        | finish index raw =>
            rw [finish_erase]
            simp only [PqxdhInitialPendingPost.compiler, StateT.run, bind_assoc, pure_bind]
            exact bind_congr fun result => ih result.1 (PqxdhInitialPendingPost.install index before result.2)

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
    (saved : PqxdhInitialPostContext.Context extra M P I D K Result S B →
      PqxdhInitialPostContext.Frame extra M P I D K X Response Shared Result S B)
    (client : OracleComp (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
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
private theorem record_sound (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : NativeFront M P I D K S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range request → NativeFront M P I D K S B →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
    (afterErase : ∀ reply updated, simulateQ erase (after reply updated) =
      (simulateQ (PqxdhInitialPendingPost.compiler sender route decode) (outside reply)).run updated)
    (afterSound : ∀ reply updated, Sound (PqxdhInitialPostContext.frame sender route decode) (after reply updated)) :
    Sound (PqxdhInitialPostContext.frame sender route decode) (record sender route decode request before outside after) := by
  apply RawCtxForwardAnnotationLift.sound_lift_bind (RawCtxSelectedFamilyContext.frame sender route decode)
    (PqxdhInitialPostContext.frame sender route decode) _ _ _
    (RawCtxForwardLive.program_sound sender route decode _ _) (fun result => afterSound result.1 { before with roles := result.2 })
  intro tag
  simp only [PqxdhInitialPostContext.frame, RawCtxForwardAnnotationComposition.appendFrame,
    RawCtxForwardAnnotationLift.liftFrame, afterErase]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem ownerLift_sound_bind (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin B) (before : NativeFront M P I D K S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
    (afterErase : ∀ reply updated, simulateQ erase (after reply updated) =
      (simulateQ (PqxdhInitialPendingPost.compiler sender route decode) (outside reply)).run updated)
    (afterSound : ∀ reply updated, Sound (PqxdhInitialPostContext.frame sender route decode) (after reply updated))
    (client : OracleComp (RawCtxForwardOwner.Spec Unit (core.option.Option RawCtxWholeOwner.Decrypted))
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingOwnerTails.Owner RatchetChain Unit))
    (innerSound : Sound (ownerFrame candidate.server_binding.identity_key_id decode) client) :
    Sound (PqxdhInitialPostContext.frame sender route decode)
      (ownerLift index before control candidate outside client >>= fun result =>
        let published := finishResult index before control candidate result
        after published.1 published.2) := by
  apply RawCtxForwardAnnotationLift.sound_lift_bind
    (fun tag => RawCtxForwardAnnotationLift.liftFrame (ownerFrame candidate.server_binding.identity_key_id decode tag))
    (PqxdhInitialPostContext.frame sender route decode) _ _ _
    (sound_lift _ _ innerSound) (fun result => afterSound _ _)
  intro tag
  simp only [PqxdhInitialPostContext.frame, RawCtxForwardAnnotationComposition.appendFrame,
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
private theorem finish_sound (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin B) (raw : Pqxdh.Bytes)
    (before : NativeFront M P I D K S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
    (afterErase : ∀ reply updated, simulateQ erase (after reply updated) =
      (simulateQ (PqxdhInitialPendingPost.compiler sender route decode) (outside reply)).run updated)
    (afterSound : ∀ reply updated, Sound (PqxdhInitialPostContext.frame sender route decode) (after reply updated)) :
    Sound (PqxdhInitialPostContext.frame sender route decode) (finish decode index raw before outside after) := by
  unfold finish
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    dsimp only
    rw [QueryImpl.simulateQ_compose]
    apply plain_sound_bind
    intro prepared
    cases prepared with
    | none => exact afterSound _ _
    | some prepared =>
        apply plain_sound_bind
        intro kernel
        cases kernel with
        | none => exact afterSound _ _
        | some kernel =>
            apply plain_sound_bind
            intro application
            cases application with
            | none => exact afterSound _ _
            | some application =>
                exact ownerLift_sound_bind sender route decode index before control _ outside after afterErase afterSound _
                  (RawCtxForwardOwner.program_sound _ _ _ _)
  all_goals exact afterSound _ _

/-- Every carried pending descriptor is generated by the original full post source and names its complete future continuation. -/
theorem program_sound (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) :
    Sound (PqxdhInitialPostContext.frame sender route decode)
      (program (X := X) (Response := Response) (Shared := Shared) sender route decode client before) := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [program_query]
      rcases request with (request | request) | request
      · exact record_sound sender route decode request before outside _
          (fun reply updated => program_erase sender route decode (outside reply) updated) ih
      · exact plain_sound_bind _ _ _ (fun reply => ih reply before)
      · cases request with
        | finish index raw =>
            exact finish_sound sender route decode index raw before outside _
              (fun reply updated => program_erase sender route decode (outside reply) updated) ih

private theorem pre_covered_bind {Value : Type}
    (client : OracleComp (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) Value)
    (after : Value → OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
    (covered : ∀ value, RawCtxForwardCoverage.Covered selected (after value)) :
    RawCtxForwardCoverage.Covered selected
      (simulateQ (plain ∘ₛ PqxdhInitialPendingPost.preForward) client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact covered value
  | query_bind query next ih =>
      change none.isSome = false ∧ _
      exact ⟨rfl, fun reply => ih reply⟩

private theorem ownerLift_covered_bind (index : Fin B) (before : NativeFront M P I D K S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
    (afterCovered : ∀ reply updated, RawCtxForwardCoverage.Covered selected (after reply updated))
    (client : OracleComp (RawCtxForwardOwner.Spec Unit (core.option.Option RawCtxWholeOwner.Decrypted))
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingOwnerTails.Owner RatchetChain Unit))
    (innerCovered : RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected client) :
    RawCtxForwardCoverage.Covered selected
      (ownerLift index before control candidate outside client >>= fun result =>
        let published := finishResult index before control candidate result
        after published.1 published.2) := by
  have lifted : RawCtxForwardCoverage.Covered (RawCtxPendingFamilyLiveTails.selected (serverCount := S) (beaconCount := B))
      (RawCtxForwardAnnotationLift.lift id client) := by
    induction client using OracleComp.inductionOn with
    | pure value => trivial
    | query_bind query next ih =>
        change (query.1.map id).isSome = RawCtxPendingMixedPrefix.ownerSelected query.2 ∧ _
        exact ⟨by simpa only [Option.isSome_map] using
          (show query.1.isSome = RawCtxPendingMixedPrefix.ownerSelected query.2 from innerCovered.1), fun reply => ih reply (innerCovered.2 reply)⟩
  exact RawCtxForwardAnnotationLift.covered_lift_bind RawCtxPendingFamilyLiveTails.selected selected
    (fun _ => rfl) _ _ _ lifted (fun result => afterCovered _ _)

private theorem finish_covered (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
    (afterCovered : ∀ reply updated, RawCtxForwardCoverage.Covered selected (after reply updated)) :
    RawCtxForwardCoverage.Covered selected (finish decode index raw before outside after) := by
  unfold finish
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    apply pre_covered_bind
    intro prepared
    cases prepared with
    | none => exact afterCovered _ _
    | some prepared =>
        change none.isSome = false ∧ _
        refine ⟨rfl, ?_⟩
        intro kernel
        cases kernel with
        | none => exact afterCovered _ _
        | some kernel =>
            change none.isSome = false ∧ _
            refine ⟨rfl, ?_⟩
            intro application
            cases application with
            | none => exact afterCovered _ _
            | some application =>
                exact ownerLift_covered_bind index before control _ outside after afterCovered _
                  (RawCtxForwardOwner.program_covered _ _ _ _)
  all_goals exact afterCovered _ _

/-- Every actual private derivation in the full post schedule carries its source descriptor under every reply; all preparation, initializer, read and selector callbacks remain explicit. -/
theorem program_covered (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) :
    RawCtxForwardCoverage.Covered selected
      (program (X := X) (Response := Response) (Shared := Shared) sender route decode client before) := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [program_query]
      rcases request with (request | request) | request
      · exact RawCtxForwardAnnotationLift.covered_lift_bind RawCtxPendingFamilyLiveTails.selected selected
          (fun _ => rfl) _ _ _ (RawCtxForwardLive.program_covered sender route decode _ _)
          (fun result => ih result.1 { before with roles := result.2 })
      · change none.isSome = false ∧ _
        exact ⟨rfl, fun reply => ih reply before⟩
      · cases request with
        | finish index raw => exact finish_covered decode index raw before outside _ ih

end BeaconcryptCore.Computational.PqxdhInitialForwardPost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialForwardPost.plain_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialForwardPost.plain_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialForwardPost.finish_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialForwardPost.finish_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialForwardPost.program_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialForwardPost.program_query

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialForwardPost.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialForwardPost.program_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialForwardPost.program_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialForwardPost.program_sound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialForwardPost.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialForwardPost.program_covered
