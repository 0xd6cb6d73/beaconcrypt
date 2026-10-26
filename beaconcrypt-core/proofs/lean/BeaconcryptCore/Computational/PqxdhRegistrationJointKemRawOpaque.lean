-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAuthenticatedSelectedKem
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume

/-! The opaque form of the raw-ordinal KEM games (theorem T6). The KEM scan of `AcceptKemCut.exposeAt` is the image of an explicit scan whose active case saves only the source parameters of the selected raw accept: its raw bytes, the verified record, the ephemeral value, the consumed set, the native state, the owner list and the client continuation. All of them are fixed before the selected encapsulation, so none holds its ciphertext or shared secret. The saved continuation fed the ordinary challenge reply is the candidate-free executable resumption `KemOpaqueResume.resume` with the challenge marker, run under the private client interpreter `KemOpaqueResume.liftImpl`, followed by the rest of the tagged client. Consequently the explicit raw-ordinal branch of `KemRawGame`, in particular the KEM-ideal game of theorem T5, equals the opaque branch in which the candidate is only an argument of that interpreter, which materializes it only in its private root request, and of the router, which returns it only for the exact challenge ciphertext under the selected key. These are program equalities; they charge no advantage. The root interpreter is the restricted Extract-ROM root that the actual source uses, so no KDF backend is chosen, no Extract hybrid is performed and no secret-input KDF context is formed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointKemEncapsulation (actual commands)
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointKemChallenge (Context)
open PqxdhRegistrationJointKemResume (ResultState post reply)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointAcceptKemCut (exposeAt rawResume tagged hide)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointServerBirth (ClientCreated)
open PqxdhRegistrationJointKemOpaqueResume (liftImpl clientNative forwardClient)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The KEM cut of `exposeAt` with its active case described by source parameters instead of the Server's saved continuation `AcceptKemCut.rawResume`, which `toCut` rebuilds: the raw bytes of the selected raw accept, the verified record of their attached verification, the ephemeral value and consumed set after the steps before encapsulation, the native state and owner list at the selected accept, and the client continuation after it. Every field is fixed before the selected encapsulation, so no field holds its ciphertext or shared secret. These are private values of the reduction context, not public context. -/
inductive OpaqueCut (Reader KemSK X R : Type) where
  | complete (outcome : Outcome KemSK R)
  | pending (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
      (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
      (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
      (next : Option Nat → OracleComp (SourceSpec KemSK) X)

/-- The completion of a raw accept whose collected input is `collected`, from the native state at that accept: the actual accept tail followed by the rest of the tagged client, every later encapsulation interpreted in place by the actual encapsulator. -/
noncomputable def rejectRun (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (owners : List EncodedEntry) (state : NativeState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    OracleComp (PqxdhLiveKemBirth.Spec KemSK) (OpaqueCut Reader KemSK X R) := do
  let answer ← (PqxdhRegistrationJointOpenBackend.native
    (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state.2 collected)).run state
  (fun outcome => .complete outcome) <$> simulateQ (actual setup)
    (commands setup codec checks identityIndex publicIdentity (tagged observe raw next answer.1) owners answer.2)

/-- The explicit scan: the actual source prefix up to the selected raw accept, its attached verification and the steps before encapsulation, all interpreted exactly as in `KemCut.scan` of `exposeAt`. A completed prefix, a rejected verification and a rejection before encapsulation complete the whole run; otherwise the source parameters of the active cut are saved. -/
noncomputable def opaqueScan (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat) (owners : List EncodedEntry) (state : NativeState KemSK) :
    OracleComp (PqxdhLiveKemBirth.Spec KemSK) (OpaqueCut Reader KemSK X R) := do
  let reached ← simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity
    (PqxdhRegistrationJointAcceptCut.scan work index) owners state)
  match reached.1.1 with
  | .complete result => pure (.complete ((observe (result, none), reached.1.2), reached.2))
  | .pending raw next =>
    match PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
    | none =>
      rejectRun setup codec checks identityIndex publicIdentity observe raw next reached.1.2 reached.2
        (none, reached.2.2.server.consumed)
    | some value => do
      let prepared ← simulateQ (actual setup)
        ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
          (PqxdhRegistrationJointKemCollected.beforeEncapsulation value)).run reached.2.2.server.consumed)
      match prepared.1 with
      | none =>
        rejectRun setup codec checks identityIndex publicIdentity observe raw next reached.1.2 reached.2
          (none, prepared.2)
      | some ephemeral => pure (.pending raw value ephemeral prepared.2 reached.2 reached.1.2 next)

/-- The KEM cut described by an opaque cut: an active cut requests the encapsulation of the raw bytes with the verified PQ key and saves the literal continuation `AcceptKemCut.rawResume`. -/
noncomputable def toCut (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) :
    OpaqueCut Reader KemSK X R → PqxdhRegistrationJointKemCut.Cut KemSK (Outcome KemSK R)
  | .complete outcome => .complete outcome
  | .pending raw value ephemeral consumed native owners next =>
    .pending (raw, value.keys.pqKey) (rawResume setup codec checks identityIndex publicIdentity observe raw value
      ephemeral consumed native owners next)

/-- The opaque resumption of an active cut after a challenge ciphertext: the candidate-free executable resumption `KemOpaqueResume.resume` with the challenge marker, run under the private client interpreter `KemOpaqueResume.liftImpl`, whose tail interpreter materializes `candidate` only in the private root request, followed by the rest of the tagged client with every later encapsulation interpreted in place. -/
noncomputable def opaqueResume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R) := do
  let answer ← (simulateQ (liftImpl clientNative setup native.2.sessions candidate forwardClient)
    (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge native.2 consumed)).run native
  hide setup (commands setup codec checks identityIndex publicIdentity (tagged observe raw next answer.1) owners answer.2)

/-- The KEM scan of `exposeAt` is the image of the explicit opaque scan. This is a program equality, not a support statement. -/
theorem scan_opaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat) (owners : List EncodedEntry) (state : NativeState KemSK) :
    PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity observe work index owners state) 0 =
      toCut setup codec checks identityIndex publicIdentity observe <$>
        opaqueScan (Reader := Reader) setup codec checks identityIndex publicIdentity observe work index owners state := by
  rw [PqxdhRegistrationJointAcceptKemCut.exposeAt_scan, opaqueScan, map_bind]
  apply bind_congr
  rintro ⟨⟨cut, after⟩, native⟩
  cases cut with
  | complete result => simp only [map_pure, toCut]
  | pending raw next =>
    dsimp only
    rw [PqxdhRegistrationJointAcceptKemCut.accept_scan, PqxdhRegistrationJointAcceptKemCut.ordered_cut]
    rcases verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with _ | value
    · simp only [pure_bind, rejectRun, map_bind, PqxdhRegistrationJointAcceptKemCut.scan_hide, Functor.map_map, toCut]
    · simp only [bind_assoc, map_bind]
      apply bind_congr
      rintro ⟨_ | ephemeral, consumed⟩
      · simp only [pure_bind, rejectRun, map_bind, PqxdhRegistrationJointAcceptKemCut.scan_hide, Functor.map_map,
          toCut]
      · simp only [pure_bind, map_pure, toCut]
        rfl

/-- Fed the ordinary challenge reply, the saved continuation of an active cut is the opaque resumption: the literal suffix, accept tail and rest of the tagged client equal the candidate-free executable resumption with the challenge marker under the private client interpreter, followed by the same rest (`KemOpaqueResume.resume_reply`). -/
theorem rawResume_opaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    rawResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners next
      (reply ciphertext candidate) =
      opaqueResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners
        next ciphertext candidate :=
  PqxdhRegistrationJointKemOpaqueResume.resume_reply setup codec checks identityIndex publicIdentity raw value
    ephemeral ciphertext candidate native.2 consumed native
    (fun answer => hide setup (commands setup codec checks identityIndex publicIdentity
      (tagged observe raw next answer.1) owners answer.2))

/-- Theorem T6, first part. At an active KEM cut of `exposeAt`, reached at the selected raw accept, the request is the raw bytes with the verified PQ key of their attached verification, and for every challenge ciphertext and candidate the saved continuation fed the ordinary challenge reply is the opaque resumption of the same source parameters. -/
theorem rawCut_resume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat) (owners : List EncodedEntry) (state : NativeState KemSK)
    (request : PqxdhRegistrationJointKemCut.Request)
    (resume : PqxdhRegistrationJointKemCut.Reply →
      OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R))
    (reached : .pending request resume ∈ support (PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity observe work index owners state) 0)) :
    ∃ raw next value ephemeral consumed native after,
      PqxdhRegistrationJointAcceptCut.Cut.pending raw next ∈ support (PqxdhRegistrationJointAcceptCut.scan work index) ∧
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
      request = (raw, value.keys.pqKey) ∧
      ∀ ciphertext candidate, resume (reply ciphertext candidate) =
        opaqueResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native after
          next ciphertext candidate := by
  obtain ⟨raw, next, value, ephemeral, consumed, native, after, source, verified, rfl, rfl⟩ :=
    PqxdhRegistrationJointAcceptKemCut.rawCut_shape setup codec checks identityIndex publicIdentity observe work index
      owners state request resume reached
  exact ⟨raw, next, value, ephemeral, consumed, native, after, source, verified, rfl, fun ciphertext candidate =>
    rawResume_opaque setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native after
      next ciphertext candidate⟩

/-- The completion of a rejected raw accept is a completed opaque cut. -/
theorem rejectRun_complete (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (owners : List EncodedEntry) (state : NativeState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) (cut : OpaqueCut Reader KemSK X R)
    (reached : cut ∈ support (rejectRun setup codec checks identityIndex publicIdentity observe raw next owners state
      collected)) :
    ∃ outcome, cut = .complete outcome := by
  rw [rejectRun, mem_support_bind_iff] at reached
  obtain ⟨_, _, reached⟩ := reached
  rw [support_map] at reached
  obtain ⟨outcome, _, same⟩ := reached
  exact ⟨outcome, same.symm⟩

/-- An active opaque cut saves the raw bytes and client continuation of a reached pending raw-accept cut at the designated ordinal, and the verified record of their attached verification. -/
theorem opaque_pending (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat) (owners : List EncodedEntry) (state : NativeState KemSK)
    (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (after : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X)
    (reached : OpaqueCut.pending raw value ephemeral consumed native after next ∈
      support (opaqueScan setup codec checks identityIndex publicIdentity observe work index owners state)) :
    PqxdhRegistrationJointAcceptCut.Cut.pending raw next ∈ support (PqxdhRegistrationJointAcceptCut.scan work index) ∧
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value := by
  rw [opaqueScan, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨cut, after'⟩, native'⟩, prefixReached, reached⟩ := reached
  have source := PqxdhRegistrationJointAcceptKemCut.commands_support setup codec checks identityIndex publicIdentity
    _ owners state _ (PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _ prefixReached)
  cases cut with
  | complete result => simp at reached
  | pending raw' next' =>
    dsimp only at reached source
    rcases verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw' with _ | value'
    · rw [verified] at reached
      obtain ⟨_, contradiction⟩ := rejectRun_complete setup codec checks identityIndex publicIdentity observe raw' next'
        after' native' _ _ reached
      cases contradiction
    · rw [verified] at reached
      dsimp only at reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨⟨_ | ephemeral', consumed'⟩, _, reached⟩ := reached
      · obtain ⟨_, contradiction⟩ := rejectRun_complete setup codec checks identityIndex publicIdentity observe raw'
          next' after' native' _ _ reached
        cases contradiction
      · simp only [support_pure, Set.mem_singleton_iff, OpaqueCut.pending.injEq] at reached
        obtain ⟨rfl, rfl, -, -, -, -, rfl⟩ := reached
        exact ⟨source, verified⟩

/-- The saved context of the opaque raw-ordinal prephase: `KemChallenge.Context` with the opaque cut in place of the KEM cut. -/
inductive OpaqueContext (Reader KemSK A X : Type) (count : Nat) where
  | failed (state : PqxdhRegistrationJointServerPrefix.State KemSK A)
  | ready (created : ClientCreated Unit) (others : Fin count → MlKem768PublicKey × KemSK)
      (cut : Option (OpaqueCut Reader KemSK X Bool))
      (state : PqxdhDynamicKemJointSource.State KemSK) (runtime : A)

/-- The KEM-game context described by an opaque context, with the Server identity index and public identity of the created Server and the decision observation of `KemRawChallenge.rawScan`. -/
noncomputable def toContext (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) {count : Nat} : OpaqueContext Reader KemSK A X count → Context KemSK A Bool count
  | .failed state => .failed state
  | .ready created others cut state runtime =>
    .ready created others (cut.map (toCut setup codec checks created.server.server.metadata.identityIndex
      created.publicIdentity (decideTag decision))) state runtime

/-- The stopped-source raw-ordinal prephase `KemRawChallenge.sourcePreRaw` with the explicit opaque scan in place of the KEM scan. Initialization, local reservations and the stopped selected-first router are unchanged. -/
noncomputable def sourcePreOpaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    ProbComp (OpaqueContext Reader KemSK A X count) := do
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  match born.1 with
  | none => pure (.failed born.2)
  | some created => do
    let others ← PqxdhLiveKemSelection.sampleFamily
      (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
    let result ← (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
      (List.ofFn (selected.insertNth chosen others)))
      (opaqueScan setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
        (decideTag decision) work index [] (PqxdhRegistrationJointInitializedAccept.initial created))).run).run
          (born.2.1.1, PqxdhDynamicKemRouter.empty))
    pure (.ready created others result.1 result.2 born.2.2)

/-- The stopped-source raw-ordinal prephase is the image of the opaque prephase. -/
theorem preRaw_opaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    PqxdhRegistrationJointKemRawChallenge.sourcePreRaw setup codec checks ensureInit supplied decision work runtime
      count selected index chosen =
      toContext setup codec checks decision <$>
        sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
          index chosen := by
  simp only [PqxdhRegistrationJointKemRawChallenge.sourcePreRaw, sourcePreOpaque, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp only [map_pure, toContext]
  · simp only [map_bind]
    apply bind_congr
    intro others
    rw [PqxdhRegistrationJointKemRawChallenge.rawScan, scan_opaque, simulateQ_map, OptionT.run_map, StateT.run_map,
      bind_map_left]
    simp only [map_pure, toContext]

/-- The opaque postchallenge step: `KemResume.post` on the opaque context. An active cut whose requested key is the challenge key runs the opaque resumption under the same interpreter chain, the actual encapsulator followed by the dynamic joint router; every other case returns the context as inactive. The candidate is an argument only of the private client interpreter inside the opaque resumption and of the router, which returns it only for the exact challenge ciphertext under the selected key. -/
noncomputable def opaquePost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (ResultState KemSK A Bool count) := do
  match transcript.context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners next)) state _ =>
    if value.keys.pqKey = transcript.publicKey then
      let reached ← (((simulateQ (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey others)
        transcript.ciphertext candidate)
        (simulateQ (actual setup) (opaqueResume setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners next
          transcript.ciphertext candidate))).run).run state)
      pure (toContext setup codec checks decision transcript.context, some reached)
    else pure (toContext setup codec checks decision transcript.context, none)
  | _ => pure (toContext setup codec checks decision transcript.context, none)

/-- `KemResume.post` on the context described by an opaque context is the opaque postchallenge step. In the active case the saved continuation fed the challenge reply is rewritten by `KemOpaqueResume.resume_post` under the exact interpreter chain of `KemResume.post`. -/
theorem post_opaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (publicKey : MlKem768PublicKey)
    (ciphertext : MlKem768Ciphertext) (context : OpaqueContext Reader KemSK A X count)
    (candidate : MlKemSharedSecret) :
    post setup count selected ⟨publicKey, ciphertext, toContext setup codec checks decision context⟩ candidate =
      opaquePost setup codec checks decision count selected ⟨publicKey, ciphertext, context⟩ candidate := by
  cases context with
  | failed state => rfl
  | ready created others cut state runtime =>
    cases cut with
    | none => rfl
    | some cut =>
      cases cut with
      | complete outcome => rfl
      | pending raw value ephemeral consumed native owners next =>
        by_cases active : value.keys.pqKey = publicKey
        · simp only [post, opaquePost, toContext, toCut, Option.map_some, active, ↓reduceIte, rawResume, opaqueResume]
          rw [PqxdhRegistrationJointKemOpaqueResume.resume_post]
        · simp only [post, opaquePost, toContext, toCut, Option.map_some, active, ↓reduceIte]

/-- The opaque raw-ordinal branch: `KemRawGame.branch` with the opaque prephase and the opaque postchallenge step. With `real = false` it is the opaque form of the KEM-ideal game: the uniform candidate held by the challenger is an argument only of the private client interpreter of the opaque resumption and of the router, which hands it to the source's own Beacon-finish code only on a decapsulation of the exact challenge ciphertext under the selected key. -/
noncomputable def opaqueBranch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (opaquePost setup codec checks decision count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- Theorem T6. The explicit raw-ordinal branch of `KemRawGame` equals the opaque branch, for both values of the branch bit; with `real = false` this is the KEM-ideal game of theorem T5. This is a program equality with the same initialization, reservations, stopped router, challenger key generation, encapsulation, uniform draw, decapsulation evaluation and decision. It charges no advantage, forms no secret-input KDF context, and keeps the restricted Extract-ROM root interpreter of the actual source. -/
theorem branchRaw_opaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    PqxdhRegistrationJointKemRawGame.branch setup codec checks ensureInit supplied decision work runtime count selected
      index real =
      opaqueBranch setup codec checks ensureInit supplied decision work runtime count selected index real := by
  simp only [PqxdhRegistrationJointKemRawGame.branch, opaqueBranch, preRaw_opaque, bind_map_left, post_opaque]

/-- Theorem T5 with its KEM-ideal game in opaque form: the opaque continuation joined to the selected raw accept of the main theorem. The left side, the premises and the loss terms are exactly those of `AuthenticatedSelectedKem.authenticated_selected_kem`; only the KEM-ideal game on the right is replaced by the equal opaque branch (theorem T6). No Extract hybrid, context secrecy or KDF backend is claimed. -/
theorem authenticated_selected_opaque (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (decision : X → Bool) (kemIndex : Fin (count + 1)) (chosenOwner : Nat) (fallback : Pqxdh.Bytes)
    (dynamicFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (letI := Classical.propDecidable; 𝒟[(fun pair =>
        decide (PqxdhRegistrationJointKemRawBridge.Decided decision
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointAcceptOrigin.Protected setup codec checks kemIndex pair.1)) <$>
      PqxdhRegistrationJointAcceptCutReports.split setup codec checks ensureInit supplied (count + 1) work index
        runtime] {true}) ≤
    𝒟[opaqueBranch setup codec checks ensureInit supplied decision work runtime count kemIndex index false] {true} +
      ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work runtime
          count kemIndex index).toINDCCA).toReal +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) +
      ∑ target : Fin (count + 1), advantage setup.joint
        (PqxdhRegistrationJointNativeOriginBound.reduction setup codec checks ensureInit supplied count
          (PqxdhRegistrationJointAcceptCut.selected work index chosenOwner fallback) runtime
          dynamicFallback ordinaryFallback target) := by
  rw [← branchRaw_opaque]
  exact PqxdhRegistrationJointAuthenticatedSelectedKem.authenticated_selected_kem setup functional codec checks
    shortRejects ensureInit supplied count work runtime index budget certified capacity decision kemIndex chosenOwner
    fallback dynamicFallback ordinaryFallback

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.scan_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.scan_opaque

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.rawResume_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.rawResume_opaque

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.rawCut_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.rawCut_resume

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.rejectRun_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.rejectRun_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.opaque_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.opaque_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.preRaw_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.preRaw_opaque

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.post_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.post_opaque

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.branchRaw_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.branchRaw_opaque

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.authenticated_selected_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque.authenticated_selected_opaque
