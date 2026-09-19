import BeaconcryptCore.Computational.PqxdhInitialBuilderContext

/-!
The original Server builder constructs a first-send descriptor at its actual private request, then retains erase, serialization, publication and the full post client. Every admission gate stays before that request. The subsequent post compiler carries its own exact record and Beacon-finish descriptors in the same interface.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialForwardBuilder
open PqxdhInitialPostContext PqxdhInitialBuilderContext RawCtxForwardAnnotation
variable {ι M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Spec (extra : OracleSpec ι) (M P I D K X Response Shared Result : Type) (S B : Nat) :=
  RawCtxForwardAnnotation.Spec (PqxdhInitialBuilderContext.Context extra M P I D K Result S B)
    (Base extra RatchetChain I D K X Response Shared S B)
abbrev Publication (M P : Type) := PqxdhInitialGenericPublication.State
  (PqxdhInitialPendingPost.KernelOf RatchetChain) M P (List Pqxdh.Bytes)

def plain : QueryImpl (Base extra RatchetChain I D K X Response Shared S B)
    (OracleComp (Spec extra M P I D K X Response Shared Result S B)) :=
  fun query => (Spec extra M P I D K X Response Shared Result S B).query (none, query)

noncomputable def post (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) :
    OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B) :=
  mapTags Sum.inl (PqxdhInitialForwardPost.program sender route decode client before)

noncomputable def finished (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × Publication M P)) :=
  let installed := PqxdhInitialPendingBuilder.reinstall index before result
  post (X := X) (Response := Response) (Shared := Shared) sender route decode (outside installed.1) installed.2

noncomputable def publication (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B) := do
  let published ← simulateQ plain (afterSend PqxdhInitialPendingPost.auxForward candidate authenticated metadata
    (PqxdhInitialPendingBuilder.selected sender index before) result)
  finished sender route decode index before outside (.ok published)

noncomputable def send (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B) :=
  match RawCtxChainSend.normalBegin kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated) with
  | .exhausted entry _ => publication sender route decode index before candidate authenticated metadata outside (entry, none)
  | .requested pending => do
      let reply ← (Spec extra M P I D K X Response Shared Result S B).query
        (some (.inr ⟨index, before, metadata, candidate, authenticated, pending, outside⟩),
          .inl (.inl (.inr (.inl (.inl pending)))))
      let ready := RawCtxChainSend.ready pending reply
      let sealed ← (Spec extra M P I D K X Response Shared Result S B).query
        (none, .inl (.inl (.inr (.inl (.inr ready)))))
      publication sender route decode index before candidate authenticated metadata outside (ready.advanced, sealed)

noncomputable def candidate (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B) := do
  let input := PqxdhInitialPendingBuilder.selected sender index before
  let valid ← simulateQ plain (PqxdhInitialPendingPost.auxForward (.checkIdentity pending.beacon_identity_public_key))
  if !valid then finished sender route decode index before outside (.ok (none, input)) else do
    let reserved ← simulateQ plain (PqxdhInitialPendingPost.auxForward .reservePeer)
    if !reserved then finished sender route decode index before outside (.ok (none, input)) else
      match initial with
      | .fail error => finished sender route decode index before outside (.fail error)
      | .div => finished sender route decode index before outside .div
      | .ok kernel =>
          let plaintext := data.getD PqxdhServerRegistrationPublication.registrationWitness
          if plaintext.isEmpty then finished sender route decode index before outside (.ok (none, input))
          else if 8 + plaintext.length ≤ Usize.max then do
            let allocated ← simulateQ plain (PqxdhInitialPendingPost.auxForward (.reservePlaintext (8 + plaintext.length)))
            if !allocated then finished sender route decode index before outside (.ok (none, input)) else
              match pending.key_id_binding with
              | .fail error => finished sender route decode index before outside (.fail error)
              | .div => finished sender route decode index before outside .div
              | .ok binding =>
                  send sender route decode index before pending
                    (PqxdhRefinement.absBytes binding.bytes ++ plaintext) metadata outside kernel
          else finished sender route decode index before outside (.ok (none, input))

noncomputable def used (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B) :=
  let input := PqxdhInitialPendingBuilder.selected sender index before
  match pqxdh.server_next_key_id input.control with
  | .fail error => finished sender route decode index before outside (.fail error)
  | .div => finished sender route decode index before outside .div
  | .ok (.Err _) => finished sender route decode index before outside (.ok (none, input))
  | .ok (.Ok next) =>
      let availability := if (input.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available
      match PqxdhRegistrationInputs.prepare input.control pending ⟨input.server.identity, input.identityKeyId⟩ availability with
      | .fail error => finished sender route decode index before outside (.fail error)
      | .div => finished sender route decode index before outside .div
      | .ok (.Err _) => finished sender route decode index before outside (.ok (none, input))
      | .ok (.Ok prepared) => candidate sender route decode index before initial prepared data metadata outside

noncomputable def program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) :
    OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B) :=
  let current := PqxdhInitialPendingBuilder.consume index ready before
  let input := PqxdhInitialPendingBuilder.selected sender index current
  used sender route decode index current initial
    (PqxdhAcceptedRegistration.usedReady source.crypto ⟨input.server.identity, input.identityKeyId⟩ ready)
    ready.application metadata outside

private theorem plain_erase {Value : Type}
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value) :
    simulateQ erase (simulateQ (plain (M := M) (P := P) (Result := Result)) client) = client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, plain, erase]
      exact bind_congr ih

private theorem finished_erase (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × Publication M P)) :
    simulateQ erase (finished (X := X) (Response := Response) (Shared := Shared) sender route decode index before outside result) =
      let installed := PqxdhInitialPendingBuilder.reinstall index before result
      (simulateQ (PqxdhInitialPendingPost.compiler sender route decode) (outside installed.1)).run installed.2 := by
  simp only [finished, post, erase_mapTags, PqxdhInitialForwardPost.program_erase]

private theorem publication_erase (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    simulateQ erase (publication (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before candidate authenticated metadata outside result) =
      complete sender route decode index before candidate authenticated metadata outside result := by
  simp only [publication, complete, simulateQ_bind, plain_erase, finished_erase]

set_option backward.isDefEq.respectTransparency false in
private theorem send_erase (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    simulateQ erase (send (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before candidate authenticated metadata outside kernel) =
      (PqxdhInitialPendingPost.calls.send kernel
        (PqxdhServerRegistrationPublication.firstContext candidate authenticated) >>=
          complete sender route decode index before candidate authenticated metadata outside) := by
  unfold send PqxdhInitialPendingPost.calls
  simp only [RawCtxGenericOwnerInterpretation.interpretedCalls, RawCtxPendingOwnerQueries.calls]
  cases start : RawCtxChainSend.normalBegin kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated) with
  | exhausted entry context =>
      simp only [RawCtxPendingOwnerQueries.sendProgram, simulateQ_pure, pure_bind, publication_erase]
  | requested pending =>
      simp only [RawCtxPendingOwnerQueries.sendProgram, simulateQ_bind, simulateQ_spec_query,
        RawCtxPendingOwnerQueries.sendForward, PqxdhInitialPendingPost.primitiveForward,
        simulateQ_pure, bind_assoc, pure_bind, erase, publication_erase]
      rfl

private noncomputable def sourceFinished (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × Publication M P)) :
    OracleComp (Base extra RatchetChain I D K X Response Shared S B) (Result × NativeFront M P I D K S B) :=
  let installed := PqxdhInitialPendingBuilder.reinstall index before result
  (simulateQ (PqxdhInitialPendingPost.compiler sender route decode) (outside installed.1)).run installed.2

set_option backward.isDefEq.respectTransparency false in
private theorem candidate_erase (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    simulateQ erase (candidate (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before initial pending data metadata outside) =
      (PqxdhInitialGenericBuilder.candidate PqxdhInitialPendingPost.calls PqxdhInitialPendingPost.auxForward
        initial pending data metadata (PqxdhInitialPendingBuilder.selected sender index before) >>=
          sourceFinished sender route decode index before outside) := by
  simp only [candidate, PqxdhInitialGenericBuilder.candidate, simulateQ_bind, plain_erase, bind_assoc]
  apply bind_congr
  intro valid
  cases valid
  · simp only [Bool.not_false, if_true, finished_erase, sourceFinished, pure_bind]
  · simp only [Bool.not_true, Bool.false_eq_true, if_false, simulateQ_bind, plain_erase, bind_assoc]
    apply bind_congr
    intro reserved
    cases reserved
    · simp only [Bool.not_false, if_true, finished_erase, sourceFinished, pure_bind]
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases initial with
      | fail error => simp only [PqxdhInitialGenericBuilder.continueRust, finished_erase, sourceFinished, pure_bind]
      | div => simp only [PqxdhInitialGenericBuilder.continueRust, finished_erase, sourceFinished, pure_bind]
      | ok kernel =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          split
          · simp only [finished_erase, sourceFinished, pure_bind]
          · split
            · simp only [simulateQ_bind, plain_erase, bind_assoc]
              apply bind_congr
              intro allocated
              cases allocated
              · simp only [Bool.not_false, if_true, finished_erase, sourceFinished, pure_bind]
              · simp only [Bool.not_true, Bool.false_eq_true, if_false]
                cases binding : pending.key_id_binding with
                | fail error => simp only [finished_erase, sourceFinished, pure_bind]
                | div => simp only [finished_erase, sourceFinished, pure_bind]
                | ok binding =>
                    simp only [send_erase, after_factor, bind_map_left, bind_assoc, sourceFinished]
                    rfl
            · simp only [finished_erase, sourceFinished, pure_bind]

private theorem used_erase (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    simulateQ erase (used (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before initial pending data metadata outside) =
      (PqxdhInitialGenericBuilder.usedBuild PqxdhInitialPendingPost.calls PqxdhInitialPendingPost.auxForward
        initial pending data metadata (PqxdhInitialPendingBuilder.selected sender index before) >>=
          sourceFinished sender route decode index before outside) := by
  unfold used PqxdhInitialGenericBuilder.usedBuild
  dsimp only
  cases next : pqxdh.server_next_key_id (PqxdhInitialPendingBuilder.selected sender index before).control with
  | fail error => simp only [PqxdhInitialGenericBuilder.continueRust, finished_erase, sourceFinished, pure_bind]
  | div => simp only [PqxdhInitialGenericBuilder.continueRust, finished_erase, sourceFinished, pure_bind]
  | ok value =>
      cases value with
      | Err error => simp only [PqxdhInitialGenericBuilder.continueRust, finished_erase, sourceFinished, pure_bind]
      | Ok key =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          cases preparation : PqxdhRegistrationInputs.prepare
            (PqxdhInitialPendingBuilder.selected sender index before).control pending
            ⟨(PqxdhInitialPendingBuilder.selected sender index before).server.identity,
              (PqxdhInitialPendingBuilder.selected sender index before).identityKeyId⟩
            (if ((PqxdhInitialPendingBuilder.selected sender index before).server.peers key).isSome
              then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => simp only [finished_erase, sourceFinished, pure_bind]
          | div => simp only [finished_erase, sourceFinished, pure_bind]
          | ok prepared =>
              cases prepared with
              | Err error => simp only [finished_erase, sourceFinished, pure_bind]
              | Ok prepared => exact candidate_erase sender route decode index before initial prepared data metadata outside

/-- Removing source descriptors yields exactly the complete consumed-registration builder followed by the same original post client, before any projection of state or replies. -/
theorem program_erase (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) :
    simulateQ erase (program (X := X) (Response := Response) (Shared := Shared)
      source sender route decode initial index metadata ready outside before) =
      ((PqxdhInitialPendingBuilder.build source initial sender index metadata ready).run before >>= fun result =>
        (simulateQ (PqxdhInitialPendingPost.compiler sender route decode) (outside result.1)).run result.2) := by
  simp only [program, PqxdhInitialPendingBuilder.build, StateT.run, bind_map_left,
    PqxdhInitialGenericBuilder.readyBuild, used_erase]
  rfl

private def Good (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B)) : Prop :=
  Sound (PqxdhInitialBuilderContext.frame sender route decode) client ∧
    RawCtxForwardCoverage.Covered PqxdhInitialForwardPost.selected client

private theorem post_good (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) :
    Good sender route decode (post (X := X) (Response := Response) (Shared := Shared) sender route decode client before) := by
  have sourceSound := PqxdhInitialForwardPost.program_sound (X := X) (Response := Response) (Shared := Shared)
    sender route decode client before
  have sourceCovered := PqxdhInitialForwardPost.program_covered (X := X) (Response := Response) (Shared := Shared)
    sender route decode client before
  generalize source : PqxdhInitialForwardPost.program (X := X) (Response := Response) (Shared := Shared)
    sender route decode client before = work at sourceSound sourceCovered
  unfold post
  rw [source]
  clear source
  induction work using OracleComp.inductionOn with
  | pure value => exact ⟨trivial, trivial⟩
  | query_bind query next ih =>
      constructor
      · change (∀ tag, query.1.map Sum.inl = some tag → _) ∧ _
        refine ⟨?_, fun reply => (ih reply (sourceSound.2 reply) (sourceCovered.2 reply)).1⟩
        intro tag present
        obtain ⟨original, found, rfl⟩ := Option.map_eq_some_iff.mp present
        change (⟨query.2, fun reply => simulateQ erase (mapTags Sum.inl (next reply))⟩ :
          PqxdhInitialPostContext.Frame extra M P I D K X Response Shared Result S B) =
            PqxdhInitialPostContext.frame sender route decode original
        rw [← sourceSound.1 original found]
        simp only [erase_mapTags]
        rfl
      · change (query.1.map Sum.inl).isSome = PqxdhInitialForwardPost.selected query.2 ∧ _
        exact ⟨by simpa only [Option.isSome_map] using
          (show query.1.isSome = PqxdhInitialForwardPost.selected query.2 from sourceCovered.1),
          fun reply => (ih reply (sourceSound.2 reply) (sourceCovered.2 reply)).2⟩

private theorem finished_good (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × Publication M P)) :
    Good sender route decode (finished (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before outside result) := post_good sender route decode _ _

private theorem aux_good (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : PqxdhServerRegistrationPublication.AuxSpec.Domain)
    (next : PqxdhServerRegistrationPublication.AuxSpec.Range query →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
    (good : ∀ reply, Good sender route decode (next reply)) :
    Good sender route decode ((simulateQ plain (PqxdhInitialPendingPost.auxForward query)) >>= next) := by
  constructor
  · change (∀ tag, none = some tag → _) ∧ _
    constructor
    · intro tag impossible
      cases impossible
    · exact fun reply => (good reply).1
  · change none.isSome = false ∧ _
    exact ⟨rfl, fun reply => (good reply).2⟩

private theorem publication_good (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    Good sender route decode (publication (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before candidate authenticated metadata outside result) := by
  simp only [publication, afterSend, simulateQ_bind, bind_assoc]
  apply aux_good
  intro erased
  cases result.2 with
  | none => simpa only [simulateQ_pure, pure_bind] using finished_good sender route decode index before outside (.ok (none, _))
  | some encrypted =>
      simp only [simulateQ_bind, bind_assoc]
      apply aux_good
      intro serialized
      cases serialized <;> simpa only [simulateQ_pure, pure_bind] using finished_good sender route decode index before outside (.ok _)

private theorem untagged_good (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (query : (Base extra RatchetChain I D K X Response Shared S B).Domain)
    (unchosen : PqxdhInitialForwardPost.selected query = false)
    (next : (Base extra RatchetChain I D K X Response Shared S B).Range query →
      OracleComp (Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
    (good : ∀ reply, Good sender route decode (next reply)) :
    Good sender route decode (((Spec extra M P I D K X Response Shared Result S B).query (none, query) :
      OracleComp (Spec extra M P I D K X Response Shared Result S B) _) >>= next) := by
  constructor
  · change (∀ tag, none = some tag → _) ∧ _
    constructor
    · intro tag impossible
      cases impossible
    · exact fun reply => (good reply).1
  · change none.isSome = PqxdhInitialForwardPost.selected query ∧ _
    exact ⟨unchosen.symm, fun reply => (good reply).2⟩

set_option backward.isDefEq.respectTransparency false in
private theorem send_good (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    Good sender route decode (send (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before candidate authenticated metadata outside kernel) := by
  unfold send
  cases start : RawCtxChainSend.normalBegin kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated) with
  | exhausted entry context => exact publication_good sender route decode index before candidate authenticated metadata outside (entry, none)
  | requested pending =>
      have nextGood := fun reply => untagged_good sender route decode
        (.inl (.inl (.inr (.inl (.inr (RawCtxChainSend.ready pending reply)))))) rfl
        (fun sealed => publication (X := X) (Response := Response) (Shared := Shared) sender route decode
          index before candidate authenticated metadata outside ((RawCtxChainSend.ready pending reply).advanced, sealed))
        (fun sealed => publication_good sender route decode index before candidate authenticated metadata outside _)
      constructor
      · change (∀ tag, some (Sum.inr _) = some tag → _) ∧ _
        refine ⟨?_, fun reply => (nextGood reply).1⟩
        intro tag present
        cases present
        change (⟨.inl (.inl (.inr (.inl (.inl pending)))), fun reply => simulateQ erase
          (do let sealed ← ((Spec extra M P I D K X Response Shared Result S B).query
                (none, .inl (.inl (.inr (.inl (.inr (RawCtxChainSend.ready pending reply)))))) :
                  OracleComp (Spec extra M P I D K X Response Shared Result S B) (Option RawCtxSourceSend.Encrypted))
              publication sender route decode index before candidate authenticated metadata outside
                ((RawCtxChainSend.ready pending reply).advanced, sealed))⟩ :
            PqxdhInitialPostContext.Frame extra M P I D K X Response Shared Result S B) = _
        simp only [PqxdhInitialBuilderContext.frame, builderFrame, simulateQ_bind, simulateQ_spec_query,
          erase, publication_erase]
      · change (some (Sum.inr _)).isSome = true ∧ _
        exact ⟨rfl, fun reply => (nextGood reply).2⟩

private theorem candidate_good (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    Good sender route decode (candidate (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before initial pending data metadata outside) := by
  unfold candidate
  apply aux_good
  intro valid
  cases valid
  · exact finished_good sender route decode index before outside _
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    apply aux_good
    intro reserved
    cases reserved
    · exact finished_good sender route decode index before outside _
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases initial with
      | fail error => exact finished_good sender route decode index before outside _
      | div => exact finished_good sender route decode index before outside _
      | ok kernel =>
          dsimp only
          split
          · exact finished_good sender route decode index before outside _
          · split
            · apply aux_good
              intro allocated
              cases allocated
              · exact finished_good sender route decode index before outside _
              · simp only [Bool.not_true, Bool.false_eq_true, if_false]
                cases binding : pending.key_id_binding with
                | fail error => exact finished_good sender route decode index before outside _
                | div => exact finished_good sender route decode index before outside _
                | ok binding => exact send_good sender route decode index before pending _ metadata outside kernel
            · exact finished_good sender route decode index before outside _

private theorem used_good (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    Good sender route decode (used (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before initial pending data metadata outside) := by
  unfold used
  dsimp only
  cases next : pqxdh.server_next_key_id (PqxdhInitialPendingBuilder.selected sender index before).control with
  | fail error => exact finished_good sender route decode index before outside _
  | div => exact finished_good sender route decode index before outside _
  | ok value =>
      cases value with
      | Err error => exact finished_good sender route decode index before outside _
      | Ok key =>
          dsimp only
          cases preparation : PqxdhRegistrationInputs.prepare
            (PqxdhInitialPendingBuilder.selected sender index before).control pending
            ⟨(PqxdhInitialPendingBuilder.selected sender index before).server.identity,
              (PqxdhInitialPendingBuilder.selected sender index before).identityKeyId⟩
            (if ((PqxdhInitialPendingBuilder.selected sender index before).server.peers key).isSome
              then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => exact finished_good sender route decode index before outside _
          | div => exact finished_good sender route decode index before outside _
          | ok prepared =>
              cases prepared with
              | Err error => exact finished_good sender route decode index before outside _
              | Ok prepared => exact candidate_good sender route decode index before initial prepared data metadata outside

/-- Every descriptor carried before the original first ciphertext or any later post derivation names the complete actual erased source continuation. -/
theorem program_sound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) :
    Sound (PqxdhInitialBuilderContext.frame sender route decode)
      (program (X := X) (Response := Response) (Shared := Shared) source sender route decode initial index metadata ready outside before) :=
  (used_good sender route decode index (PqxdhInitialPendingBuilder.consume index ready before) initial _ ready.application metadata outside).1

/-- Every actual private derivation in the complete first-builder and full post program is covered under every possible callback reply. -/
theorem program_covered (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) :
    RawCtxForwardCoverage.Covered PqxdhInitialForwardPost.selected
      (program (X := X) (Response := Response) (Shared := Shared) source sender route decode initial index metadata ready outside before) :=
  (used_good sender route decode index (PqxdhInitialPendingBuilder.consume index ready before) initial _ ready.application metadata outside).2

end BeaconcryptCore.Computational.PqxdhInitialForwardBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialForwardBuilder.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialForwardBuilder.program_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialForwardBuilder.program_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialForwardBuilder.program_sound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialForwardBuilder.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialForwardBuilder.program_covered
