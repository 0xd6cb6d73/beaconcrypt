import BeaconcryptCore.Computational.PqxdhInitialOriginForwardPost
import BeaconcryptCore.Computational.PqxdhInitialForwardBuilder

/-!
The original consumed-registration builder carries its actual installation origin and the current private trace before the first send. Every admission, allocation, Rust failure, sealing and publication path is retained. A successful actual builder response records its installed owner and actual counter, then the complete original adaptive post client continues through the origin-aware forward compiler. Saved descriptors preserve that full continuation without recovering metadata from an erased function.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialOriginForwardBuilder
open PqxdhInitialPostContext PqxdhInitialBuilderContext RawCtxForwardAnnotation
variable {ι M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Spec (extra : OracleSpec ι) (M P I D K X Response Shared Result Origin : Type) (S B : Nat) :=
  RawCtxForwardAnnotation.Spec (PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (Base extra RatchetChain I D K X Response Shared S B)
abbrev Publication (M P : Type) := PqxdhInitialGenericPublication.State
  (PqxdhInitialPendingPost.KernelOf RatchetChain) M P (List Pqxdh.Bytes)

def plain : QueryImpl (Base extra RatchetChain I D K X Response Shared S B)
    (OracleComp (Spec extra M P I D K X Response Shared Result Origin S B)) :=
  fun query => (Spec extra M P I D K X Response Shared Result Origin S B).query (none, query)

noncomputable def post (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :=
  PqxdhInitialOriginForwardPost.program mark sender route decode client before trace

noncomputable def finished (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × Publication M P)) :=
  let installed := PqxdhInitialPendingBuilder.reinstall index before result
  post (X := X) (Response := Response) (Shared := Shared) mark sender route decode (outside installed.1) installed.2
    (PqxdhInitialOriginPost.afterBuilder trace installed.2 index origin installed.1)

noncomputable def publication (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) := do
  let published ← simulateQ plain (afterSend PqxdhInitialPendingPost.auxForward candidate authenticated metadata
    (PqxdhInitialPendingBuilder.selected sender index before) result)
  finished mark origin sender route decode index before trace outside (.ok published)

noncomputable def send (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :=
  match RawCtxChainSend.normalBegin kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated) with
  | .exhausted entry _ => publication mark origin sender route decode index before trace candidate authenticated metadata outside (entry, none)
  | .requested pending => do
      let reply ← (Spec extra M P I D K X Response Shared Result Origin S B).query
        (some ⟨.inr ⟨index, before, metadata, candidate, authenticated, pending, outside⟩, trace, some origin⟩,
          .inl (.inl (.inr (.inl (.inl pending)))))
      let ready := RawCtxChainSend.ready pending reply
      let sealed ← (Spec extra M P I D K X Response Shared Result Origin S B).query
        (none, .inl (.inl (.inr (.inl (.inr ready)))))
      publication mark origin sender route decode index before trace candidate authenticated metadata outside (ready.advanced, sealed)

noncomputable def candidate (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) := do
  let input := PqxdhInitialPendingBuilder.selected sender index before
  let valid ← simulateQ plain (PqxdhInitialPendingPost.auxForward (.checkIdentity pending.beacon_identity_public_key))
  if !valid then finished mark origin sender route decode index before trace outside (.ok (none, input)) else do
    let reserved ← simulateQ plain (PqxdhInitialPendingPost.auxForward .reservePeer)
    if !reserved then finished mark origin sender route decode index before trace outside (.ok (none, input)) else
      match initial with
      | .fail error => finished mark origin sender route decode index before trace outside (.fail error)
      | .div => finished mark origin sender route decode index before trace outside .div
      | .ok kernel =>
          let plaintext := data.getD PqxdhServerRegistrationPublication.registrationWitness
          if plaintext.isEmpty then finished mark origin sender route decode index before trace outside (.ok (none, input))
          else if 8 + plaintext.length ≤ Usize.max then do
            let allocated ← simulateQ plain (PqxdhInitialPendingPost.auxForward (.reservePlaintext (8 + plaintext.length)))
            if !allocated then finished mark origin sender route decode index before trace outside (.ok (none, input)) else
              match pending.key_id_binding with
              | .fail error => finished mark origin sender route decode index before trace outside (.fail error)
              | .div => finished mark origin sender route decode index before trace outside .div
              | .ok binding =>
                  send mark origin sender route decode index before trace pending
                    (PqxdhRefinement.absBytes binding.bytes ++ plaintext) metadata outside kernel
          else finished mark origin sender route decode index before trace outside (.ok (none, input))

noncomputable def used (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :=
  let input := PqxdhInitialPendingBuilder.selected sender index before
  match pqxdh.server_next_key_id input.control with
  | .fail error => finished mark origin sender route decode index before trace outside (.fail error)
  | .div => finished mark origin sender route decode index before trace outside .div
  | .ok (.Err _) => finished mark origin sender route decode index before trace outside (.ok (none, input))
  | .ok (.Ok next) =>
      let availability := if (input.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available
      match PqxdhRegistrationInputs.prepare input.control pending ⟨input.server.identity, input.identityKeyId⟩ availability with
      | .fail error => finished mark origin sender route decode index before trace outside (.fail error)
      | .div => finished mark origin sender route decode index before trace outside .div
      | .ok (.Err _) => finished mark origin sender route decode index before trace outside (.ok (none, input))
      | .ok (.Ok prepared) => candidate mark origin sender route decode index before trace initial prepared data metadata outside

noncomputable def program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :=
  let current := PqxdhInitialPendingBuilder.consume index ready before
  let input := PqxdhInitialPendingBuilder.selected sender index current
  used mark origin sender route decode index current trace initial
    (PqxdhAcceptedRegistration.usedReady source.crypto ⟨input.server.identity, input.identityKeyId⟩ ready)
    ready.application metadata outside

private theorem plain_erase {Value : Type}
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value) :
    simulateQ erase (simulateQ (plain (M := M) (P := P) (Result := Result) (Origin := Origin)) client) = client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, plain, erase]
      exact bind_congr ih

private theorem finished_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × Publication M P)) :
    simulateQ erase (finished (X := X) (Response := Response) (Shared := Shared) mark origin sender route decode index before trace outside result) =
      let installed := PqxdhInitialPendingBuilder.reinstall index before result
      (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (outside installed.1)).run
        (installed.2, PqxdhInitialOriginPost.afterBuilder trace installed.2 index origin installed.1) := by
  simp only [finished, post, PqxdhInitialOriginForwardPost.program_erase]

private theorem publication_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    simulateQ erase (publication (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace candidate authenticated metadata outside result) =
      PqxdhInitialOriginContext.complete mark sender route decode index before trace (some origin) candidate authenticated metadata outside result := by
  simp only [publication, PqxdhInitialOriginContext.complete, PqxdhInitialOriginContext.builtTrace, simulateQ_bind, plain_erase, finished_erase]

set_option backward.isDefEq.respectTransparency false in
private theorem send_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    simulateQ erase (send (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace candidate authenticated metadata outside kernel) =
      (PqxdhInitialPendingPost.calls.send kernel
        (PqxdhServerRegistrationPublication.firstContext candidate authenticated) >>=
          PqxdhInitialOriginContext.complete mark sender route decode index before trace (some origin) candidate authenticated metadata outside) := by
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

private noncomputable def sourceFinished (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × Publication M P)) :
    OracleComp (Base extra RatchetChain I D K X Response Shared S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :=
  let installed := PqxdhInitialPendingBuilder.reinstall index before result
  (simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode) (outside installed.1)).run
        (installed.2, PqxdhInitialOriginPost.afterBuilder trace installed.2 index origin installed.1)

set_option backward.isDefEq.respectTransparency false in
private theorem candidate_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    simulateQ erase (candidate (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace initial pending data metadata outside) =
      (PqxdhInitialGenericBuilder.candidate PqxdhInitialPendingPost.calls PqxdhInitialPendingPost.auxForward
        initial pending data metadata (PqxdhInitialPendingBuilder.selected sender index before) >>=
          sourceFinished mark origin sender route decode index before trace outside) := by
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

private theorem used_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    simulateQ erase (used (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace initial pending data metadata outside) =
      (PqxdhInitialGenericBuilder.usedBuild PqxdhInitialPendingPost.calls PqxdhInitialPendingPost.auxForward
        initial pending data metadata (PqxdhInitialPendingBuilder.selected sender index before) >>=
          sourceFinished mark origin sender route decode index before trace outside) := by
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
              | Ok prepared => exact candidate_erase mark origin sender route decode index before trace initial prepared data metadata outside

/-- Removing source descriptors yields exactly the complete consumed-registration builder followed by the same original post client, before any projection of state or replies. -/
theorem program_erase (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    simulateQ erase (program (X := X) (Response := Response) (Shared := Shared)
      source mark origin sender route decode initial index metadata ready outside before trace) =
      (PqxdhInitialOriginPost.sequence source initial mark origin sender route decode index metadata ready outside).run (before, trace) := by
  simp only [program, PqxdhInitialOriginPost.sequence, PqxdhInitialPendingBuilder.build, StateT.run, bind_map_left,
    PqxdhInitialGenericBuilder.readyBuild, used_erase]
  rfl

private def Good (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B))) : Prop :=
  Sound (PqxdhInitialOriginContext.frame mark sender route decode) client ∧
    RawCtxForwardCoverage.Covered PqxdhInitialForwardPost.selected client

private theorem post_good (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    Good mark sender route decode (post (X := X) (Response := Response) mark sender route decode client before trace) :=
  ⟨PqxdhInitialOriginForwardPost.program_sound mark sender route decode client before trace,
   PqxdhInitialOriginForwardPost.program_covered mark sender route decode client before trace⟩

private theorem finished_good (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × Publication M P)) :
    Good mark sender route decode (finished (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace outside result) := post_good mark sender route decode _ _ _

private theorem aux_good (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : PqxdhServerRegistrationPublication.AuxSpec.Domain)
    (next : PqxdhServerRegistrationPublication.AuxSpec.Range query →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (good : ∀ reply, Good mark sender route decode (next reply)) :
    Good mark sender route decode ((simulateQ plain (PqxdhInitialPendingPost.auxForward query)) >>= next) := by
  constructor
  · change (∀ tag, none = some tag → _) ∧ _
    constructor
    · intro tag impossible
      cases impossible
    · exact fun reply => (good reply).1
  · change none.isSome = false ∧ _
    exact ⟨rfl, fun reply => (good reply).2⟩

private theorem publication_good (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    Good mark sender route decode (publication (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace candidate authenticated metadata outside result) := by
  simp only [publication, afterSend, simulateQ_bind, bind_assoc]
  apply aux_good
  intro erased
  cases result.2 with
  | none => simpa only [simulateQ_pure, pure_bind] using finished_good mark origin sender route decode index before trace outside (.ok (none, _))
  | some encrypted =>
      simp only [simulateQ_bind, bind_assoc]
      apply aux_good
      intro serialized
      cases serialized <;> simpa only [simulateQ_pure, pure_bind] using finished_good mark origin sender route decode index before trace outside (.ok _)

private theorem untagged_good (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (query : (Base extra RatchetChain I D K X Response Shared S B).Domain)
    (unchosen : PqxdhInitialForwardPost.selected query = false)
    (next : (Base extra RatchetChain I D K X Response Shared S B).Range query →
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (good : ∀ reply, Good mark sender route decode (next reply)) :
    Good mark sender route decode (((Spec extra M P I D K X Response Shared Result Origin S B).query (none, query) :
      OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) _) >>= next) := by
  constructor
  · change (∀ tag, none = some tag → _) ∧ _
    constructor
    · intro tag impossible
      cases impossible
    · exact fun reply => (good reply).1
  · change none.isSome = PqxdhInitialForwardPost.selected query ∧ _
    exact ⟨unchosen.symm, fun reply => (good reply).2⟩

set_option backward.isDefEq.respectTransparency false in
private theorem send_good (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    Good mark sender route decode (send (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace candidate authenticated metadata outside kernel) := by
  unfold send
  cases start : RawCtxChainSend.normalBegin kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated) with
  | exhausted entry context => exact publication_good mark origin sender route decode index before trace candidate authenticated metadata outside (entry, none)
  | requested pending =>
      have nextGood := fun reply => untagged_good mark sender route decode
        (.inl (.inl (.inr (.inl (.inr (RawCtxChainSend.ready pending reply)))))) rfl
        (fun sealed => publication (X := X) (Response := Response) (Shared := Shared) mark origin sender route decode
          index before trace candidate authenticated metadata outside ((RawCtxChainSend.ready pending reply).advanced, sealed))
        (fun sealed => publication_good mark origin sender route decode index before trace candidate authenticated metadata outside _)
      constructor
      · change (∀ tag, some (⟨Sum.inr _, trace, some origin⟩ : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) = some tag → _) ∧ _
        refine ⟨?_, fun reply => (nextGood reply).1⟩
        intro tag present
        cases present
        change (⟨.inl (.inl (.inr (.inl (.inl pending)))), fun reply => simulateQ erase
          (do let sealed ← ((Spec extra M P I D K X Response Shared Result Origin S B).query
                (none, .inl (.inl (.inr (.inl (.inr (RawCtxChainSend.ready pending reply)))))) :
                  OracleComp (Spec extra M P I D K X Response Shared Result Origin S B) (Option RawCtxSourceSend.Encrypted))
              publication mark origin sender route decode index before trace candidate authenticated metadata outside
                ((RawCtxChainSend.ready pending reply).advanced, sealed))⟩ :
            RawCtxForwardAnnotation.Frame (Base extra RatchetChain I D K X Response Shared S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B))) = _
        simp only [PqxdhInitialOriginContext.frame, PqxdhInitialOriginContext.resume, PqxdhInitialBuilderContext.frame, builderFrame, simulateQ_bind, simulateQ_spec_query,
          erase, publication_erase]
      · change (some (⟨Sum.inr _, trace, some origin⟩ : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)).isSome = true ∧ _
        exact ⟨rfl, fun reply => (nextGood reply).2⟩

private theorem candidate_good (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    Good mark sender route decode (candidate (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace initial pending data metadata outside) := by
  unfold candidate
  apply aux_good
  intro valid
  cases valid
  · exact finished_good mark origin sender route decode index before trace outside _
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    apply aux_good
    intro reserved
    cases reserved
    · exact finished_good mark origin sender route decode index before trace outside _
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases initial with
      | fail error => exact finished_good mark origin sender route decode index before trace outside _
      | div => exact finished_good mark origin sender route decode index before trace outside _
      | ok kernel =>
          dsimp only
          split
          · exact finished_good mark origin sender route decode index before trace outside _
          · split
            · apply aux_good
              intro allocated
              cases allocated
              · exact finished_good mark origin sender route decode index before trace outside _
              · simp only [Bool.not_true, Bool.false_eq_true, if_false]
                cases binding : pending.key_id_binding with
                | fail error => exact finished_good mark origin sender route decode index before trace outside _
                | div => exact finished_good mark origin sender route decode index before trace outside _
                | ok binding => exact send_good mark origin sender route decode index before trace pending _ metadata outside kernel
            · exact finished_good mark origin sender route decode index before trace outside _

private theorem used_good (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    Good mark sender route decode (used (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace initial pending data metadata outside) := by
  unfold used
  dsimp only
  cases next : pqxdh.server_next_key_id (PqxdhInitialPendingBuilder.selected sender index before).control with
  | fail error => exact finished_good mark origin sender route decode index before trace outside _
  | div => exact finished_good mark origin sender route decode index before trace outside _
  | ok value =>
      cases value with
      | Err error => exact finished_good mark origin sender route decode index before trace outside _
      | Ok key =>
          dsimp only
          cases preparation : PqxdhRegistrationInputs.prepare
            (PqxdhInitialPendingBuilder.selected sender index before).control pending
            ⟨(PqxdhInitialPendingBuilder.selected sender index before).server.identity,
              (PqxdhInitialPendingBuilder.selected sender index before).identityKeyId⟩
            (if ((PqxdhInitialPendingBuilder.selected sender index before).server.peers key).isSome
              then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => exact finished_good mark origin sender route decode index before trace outside _
          | div => exact finished_good mark origin sender route decode index before trace outside _
          | ok prepared =>
              cases prepared with
              | Err error => exact finished_good mark origin sender route decode index before trace outside _
              | Ok prepared => exact candidate_good mark origin sender route decode index before trace initial prepared data metadata outside

/-- Every descriptor carried before the original first ciphertext or any later post derivation names the complete actual erased source continuation. -/
theorem program_sound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    Sound (PqxdhInitialOriginContext.frame mark sender route decode)
      (program (X := X) (Response := Response) (Shared := Shared) source mark origin sender route decode initial index metadata ready outside before trace) :=
  (used_good mark origin sender route decode index (PqxdhInitialPendingBuilder.consume index ready before) trace initial _ ready.application metadata outside).1

/-- Every actual private derivation in the complete first-builder and full post program is covered under every possible callback reply. -/
theorem program_covered (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    RawCtxForwardCoverage.Covered PqxdhInitialForwardPost.selected
      (program (X := X) (Response := Response) (Shared := Shared) source mark origin sender route decode initial index metadata ready outside before trace) :=
  (used_good mark origin sender route decode index (PqxdhInitialPendingBuilder.consume index ready before) trace initial _ ready.application metadata outside).2


end BeaconcryptCore.Computational.PqxdhInitialOriginForwardBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginForwardBuilder.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginForwardBuilder.program_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginForwardBuilder.program_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginForwardBuilder.program_sound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginForwardBuilder.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginForwardBuilder.program_covered
