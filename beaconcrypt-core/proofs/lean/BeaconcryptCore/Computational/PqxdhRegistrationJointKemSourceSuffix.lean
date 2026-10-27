-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootBytes

/-! Connect the literal resumed source collector to the initialized compiler's encapsulation hook. The entire optional collector and consumed state remain in place; the root-byte consequence is derived for that concrete stateful suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity
open PqxdhServerRootPreparation
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The exact composition already used by the exposed initialized collector; only its actual encapsulation is a public hook. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes) :
    QueryImpl (Spec Reader PqxdhJointGapDh.ScalarBytes Word32)
      (StateT (List Pqxdh.Bytes) (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK))) :=
  PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw ∘ₛ
    PqxdhRegistrationJointServerPrefix.compiler identityIndex

/-- The exact native callback remaining after the supplied encapsulation reply. Both consumed-registration state and all private requests survive. -/
noncomputable def suffix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (reply : PqxdhRegistrationJointKemCut.Reply) :=
  simulateQ (handler setup codec checks identityIndex raw)
    (PqxdhRegistrationJointKemCollected.afterEncapsulation verified ephemeral reply)

/-- Source preparation exposes its single ordered encapsulation after actual verification and earlier optional effects, with its original later callback. -/
noncomputable def ordered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes) :
    StateT (List Pqxdh.Bytes) (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK))
      (Option (Inputs Reader PqxdhJointGapDh.ScalarBytes Word32)) := do
  let verified ← simulateQ (handler setup codec checks identityIndex raw) (verifyInput raw)
  match verified with
  | none => pure none
  | some verified => do
      let ephemeral ← simulateQ (handler setup codec checks identityIndex raw)
        (PqxdhRegistrationJointKemCollected.beforeEncapsulation verified)
      match ephemeral with
      | none => pure none
      | some ephemeral => do
          let reply ← (handler setup codec checks identityIndex raw) (.encapsulate verified.keys.pqKey)
          suffix setup codec checks identityIndex raw verified ephemeral reply

/-- This is the complete same-source collector equality, not a chosen successful input or a marginal distribution equality. -/
theorem ordered_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes) :
    simulateQ (handler setup codec checks identityIndex raw) (collect raw) =
      ordered setup codec checks identityIndex raw := by
  simp only [collect, ordered, simulateQ_bind]
  apply bind_congr
  intro verified
  cases verified with
  | none => rfl
  | some verified =>
      dsimp only
      rw [PqxdhRegistrationJointKemCollected.collect_split]
      simp only [simulateQ_bind]
      apply bind_congr
      intro ephemeral
      cases ephemeral <;> simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, suffix]


/-- The initialized exposed preparation is this exact ordered collector with its unchanged incoming full native state around the consumed-set result. -/
theorem preparation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    (PqxdhRegistrationJointKemEncapsulation.prepare setup codec checks identityIndex raw).run state =
      (fun result => (result, state)) <$>
        (ordered setup codec checks identityIndex raw).run state.2.server.consumed := by
  simp only [PqxdhRegistrationJointKemEncapsulation.prepare, StateT.run,
    PqxdhRegistrationJointServerPrefix.clientPrefix, ← QueryImpl.simulateQ_compose]
  rw [← handler, ordered_source]


/-- The actual compiled encapsulation callback exposes exactly the original raw candidate and verified PQ key, retaining the consumed set for every optional reply. -/
theorem encapsulation_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (consumed : List Pqxdh.Bytes) :
    ((handler setup codec checks identityIndex raw) (.encapsulate verified.keys.pqKey)).run consumed =
      (fun reply => (reply, consumed)) <$>
        ((PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query (.inr (raw, verified.keys.pqKey)) :
          OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) _) := by
  rfl


/-- At the actual source operation the scanner saves the literal interpreted suffix and arbitrary whole-source continuation, before receiving any encapsulation answer. -/
theorem suffix_cut {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes)
    (next : (Option (Inputs Reader PqxdhJointGapDh.ScalarBytes Word32) × List Pqxdh.Bytes) →
      OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) :
    PqxdhRegistrationJointKemCut.scan setup (do
      let answer ← ((handler setup codec checks identityIndex raw) (.encapsulate verified.keys.pqKey)).run consumed
      let input ← (suffix setup codec checks identityIndex raw verified ephemeral answer.1).run answer.2
      next input) 0 =
      pure (.pending (raw, verified.keys.pqKey) (fun reply => do
        let input ← (suffix setup codec checks identityIndex raw verified ephemeral reply).run consumed
        next input)) := by
  rw [encapsulation_query, bind_map_left]
  exact PqxdhRegistrationJointKemCut.scan_target setup _ _


/-- Every successful concrete compiled suffix is a permitted execution of that same literal source callback, with its complete consumed-set poststate retained. -/
theorem suffix_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (reply : PqxdhRegistrationJointKemCut.Reply) (before after : List Pqxdh.Bytes)
    (input : Inputs Reader PqxdhJointGapDh.ScalarBytes Word32)
    (reached : (some input, after) ∈ support
      ((suffix setup codec checks identityIndex raw verified ephemeral reply).run before)) :
    some input ∈ support (PqxdhRegistrationJointKemCollected.afterEncapsulation verified ephemeral reply) := by
  apply support_simulateQ_run'_subset (handler setup codec checks identityIndex raw) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ reached


/-- Resuming the actual compiled suffix with the ordinary candidate and then accepting in the extracted core supplies the exact192-byte root input, in original DH order. -/
theorem root_bytes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (before after : List Pqxdh.Bytes) (input : Inputs Reader PqxdhJointGapDh.ScalarBytes Word32)
    (reached : (some input, after) ∈ support
      ((suffix setup codec checks identityIndex raw verified ephemeral
        (PqxdhRegistrationJointKemResume.reply ciphertext candidate)).run before))
    (control final : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (pending : pqxdh.PendingServerRegistration)
    (accepted : PqxdhServerRelatedRootInput.accept control binding input = ok (.Ok (final, pending))) :
    absBytes pending.root_key_input.bytes = PqxdhHiddenRoot.hiddenRootIKM
      (PqxdhPhase2InputBytes.coordinates input.first input.second input.third input.fourth) candidate :=
  PqxdhRegistrationJointKemRootBytes.challenge_input verified ephemeral ciphertext candidate input
    (suffix_support setup codec checks identityIndex raw verified ephemeral _ before after input reached)
    control final binding pending accepted


/-- The real production HKDF wrapper at those actual accepted bytes is the existing typed secret-input root function. This functional equation does not replace the native analysis backend or claim Extract pseudorandomness. -/
theorem root_reply (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (before after : List Pqxdh.Bytes) (input : Inputs Reader PqxdhJointGapDh.ScalarBytes Word32)
    (reached : (some input, after) ∈ support
      ((suffix setup codec checks identityIndex raw verified ephemeral
        (PqxdhRegistrationJointKemResume.reply ciphertext candidate)).run before))
    (control final : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (pending : pqxdh.PendingServerRegistration)
    (accepted : PqxdhServerRelatedRootInput.accept control binding input = ok (.Ok (final, pending))) :
    RawCtxSourceHkdf.rootResponse source.crypto pending.root_key_input =
      PqxdhRootTableInitialization.rootArray (PqxdhHiddenRoot.productionHiddenRoot source
        (PqxdhPhase2InputBytes.coordinates input.first input.second input.third input.fourth) candidate) := by
  have actual := PqxdhPhase2InputBytes.root_response source (PqxdhServerRelatedRootInput.secrets input)
    pending.root_key_input (PqxdhRegistrationJointKemRootBytes.accepted_input input control final binding pending accepted)
  have fields := PqxdhRegistrationJointKemRootBytes.challenge_fields verified ephemeral ciphertext candidate input
    (suffix_support setup codec checks identityIndex raw verified ephemeral _ before after input reached)
  simpa only [PqxdhServerRelatedRootInput.secrets, fields.2.2.2] using actual


/-- The actual full accept executes this ordered collector before its unchanged source allocation/root/consumption/publication tail, retaining the complete native poststate on every branch. -/
theorem accept_ordered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    (PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw).run state =
      (do
        let collected ← (ordered setup codec checks identityIndex raw).run state.2.server.consumed
        (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
          (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state.2 collected))).run state) := by
  simp only [PqxdhRegistrationJointKemEncapsulation.accept, StateT.run_bind]
  simp only [PqxdhRegistrationJointKemEncapsulation.lift, PqxdhRegistrationJointOpenBackend.native,
    nativeGet, localState, StateT.run, PqxdhLiveKemBirth.coins, simulateQ_pure, pure_bind]
  change ((PqxdhRegistrationJointKemEncapsulation.prepare setup codec checks identityIndex raw).run state >>= _) = _
  rw [preparation, bind_map_left]
  rfl

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.ordered_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.ordered_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.preparation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.encapsulation_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.encapsulation_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.suffix_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.suffix_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.suffix_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.suffix_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.root_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.root_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.root_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.root_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.accept_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix.accept_ordered
