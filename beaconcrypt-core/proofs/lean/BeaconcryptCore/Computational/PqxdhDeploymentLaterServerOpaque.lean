-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge

/-! LQ-F: theorem T6 for the logged source, and the composed KEM transfer. `OpaqueCut` is `KemRawOpaque.OpaqueCut` with one more saved field, the log at the cut; every saved field is fixed before the selected encapsulation, so none holds the ciphertext or the shared secret. `opaqueScan` is the explicit logged scan, and the KEM scan of the logged `exposeAt` is its image under `toCut` (`scan_opaque`). The stopped-source prephase of the generic KEM hop at the logged exposure is the image of the logged opaque prephase (`pre_opaque`), and `KemResume.post` on such a context is the logged opaque postchallenge step (`post_opaque`), by the existing `KemOpaqueResume.resume_post` with the logged rest, which appends the explicit ephemeral and depends on neither the ciphertext nor the candidate. Hence the branch of the KEM hop at the logged exposure equals the logged opaque branch (`branch_opaque`, theorem T6 for the logged source), in which the candidate is an argument only of the private client interpreter and of the router. `transfer` composes T4 for the logged source (`LaterServerBridge.actual_le_real`), the generic KEM hop (`LaterServerKemHop.real_le_ideal`) and T6: one ordinary one-key ML-KEM IND-CCA advantage and one ordinary ML-KEM correctness error, each with coefficient one. The only contract used is `FunctionalDecapsulation`, as in `KemRawGame`; no assumption is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointKemEncapsulation (actual)
open PqxdhRegistrationJointKemCommands (Outcome)
open PqxdhRegistrationJointKemChallenge (Context)
open PqxdhRegistrationJointKemResume (ResultState post reply)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointAcceptKemCut (hide)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointServerBirth (ClientCreated)
open PqxdhDeploymentLaterServerSource (Log Spec)
open PqxdhDeploymentLaterServerCommands (Cut scan commands run)
open PqxdhDeploymentLaterServerCut (exposeAt rawResume opaqueResume tagged)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The KEM cut of the logged `exposeAt` with its active case described by source parameters fixed before the selected encapsulation: raw bytes, verified record, ephemeral, consumed set, native state, owners, the log at the cut and the program continuation. No field holds the ciphertext or the shared secret. -/
inductive OpaqueCut (Reader KemSK X R : Type) where
  | complete (outcome : Outcome KemSK R)
  | pending (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
      (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
      (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
      (next : Option Nat → OracleComp (Spec KemSK) X)

/-- The completion of a raw accept with collected input `collected` and logged entry `logged`: the accept tail followed by the rest of the tagged logged program from the extended log. -/
noncomputable def rejectRun (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp (Spec KemSK) X) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes) :
    OracleComp (PqxdhLiveKemBirth.Spec KemSK) (OpaqueCut Reader KemSK X R) := do
  let answer ← (PqxdhRegistrationJointOpenBackend.native
    (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state.2 collected)).run state
  (fun outcome => .complete outcome) <$> simulateQ (actual setup)
    (commands setup codec checks identityIndex publicIdentity (tagged observe raw next answer.1) owners
      (log ++ [logged]) answer.2)

/-- The explicit logged scan: the logged prefix up to the selected raw accept, its attached verification and the logged steps before encapsulation; a completed prefix, a rejected verification (entry `none`) and a rejection before encapsulation (the entry of the logged steps, the generated scalar when generation was reached) complete the run; otherwise the source parameters of the active cut are saved. -/
noncomputable def opaqueScan (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) : OracleComp (PqxdhLiveKemBirth.Spec KemSK) (OpaqueCut Reader KemSK X R) := do
  let reached ← simulateQ (actual setup) (run setup codec checks identityIndex publicIdentity (scan work index) owners
    log state)
  match reached.1.1 with
  | .complete result => pure (.complete ((observe (result, none), reached.1.2.1), reached.2))
  | .pending raw next =>
    match PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
    | none =>
      rejectRun setup codec checks identityIndex publicIdentity observe raw next reached.1.2.1 reached.1.2.2 reached.2
        (none, reached.2.2.server.consumed) none
    | some value => do
      let prepared ← simulateQ (actual setup)
        ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
          (PqxdhDeploymentLaterServerSource.beforeLogged value)).run reached.2.2.server.consumed)
      match prepared.1.1 with
      | none =>
        rejectRun setup codec checks identityIndex publicIdentity observe raw next reached.1.2.1 reached.1.2.2 reached.2
          (none, prepared.2) prepared.1.2
      | some ephemeral =>
        pure (.pending raw value ephemeral prepared.2 reached.2 reached.1.2.1 reached.1.2.2 next)

/-- The KEM cut described by a logged opaque cut. -/
noncomputable def toCut (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) :
    OpaqueCut Reader KemSK X R → PqxdhRegistrationJointKemCut.Cut KemSK (Outcome KemSK R)
  | .complete outcome => .complete outcome
  | .pending raw value ephemeral consumed native owners log next =>
    .pending (raw, value.keys.pqKey) (rawResume setup codec checks identityIndex publicIdentity observe raw value
      ephemeral consumed native owners log next)

/-- The KEM scan of the logged `exposeAt` is the image of the explicit logged opaque scan. -/
theorem scan_opaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) :
    PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity observe work index owners log state) 0 =
      toCut setup codec checks identityIndex publicIdentity observe <$>
        opaqueScan (Reader := Reader) setup codec checks identityIndex publicIdentity observe work index owners log
          state := by
  rw [PqxdhDeploymentLaterServerCut.exposeAt_scan, opaqueScan, map_bind]
  apply bind_congr
  rintro ⟨⟨cut, after, logAt⟩, native⟩
  cases cut with
  | complete result => simp only [map_pure, toCut]
  | pending raw next =>
    dsimp only
    rw [PqxdhDeploymentLaterServerCut.accept_scan, PqxdhDeploymentLaterServerCut.ordered_cut]
    rcases verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with _ | value
    · simp only [pure_bind, rejectRun, map_bind, PqxdhRegistrationJointAcceptKemCut.scan_hide, Functor.map_map, toCut]
    · simp only [bind_assoc, map_bind]
      apply bind_congr
      rintro ⟨⟨_ | ephemeral, entry⟩, consumed⟩
      · simp only [pure_bind, rejectRun, map_bind, PqxdhRegistrationJointAcceptKemCut.scan_hide, Functor.map_map,
          toCut]
      · simp only [pure_bind, map_pure, toCut]
        congr 2
        funext reply
        simp only [rawResume, bind_map_left]

/-- The saved context of the logged opaque prephase. -/
inductive OpaqueContext (Reader KemSK A X : Type) (count : Nat) where
  | failed (state : PqxdhRegistrationJointServerPrefix.State KemSK A)
  | ready (created : ClientCreated Unit) (others : Fin count → MlKem768PublicKey × KemSK)
      (cut : Option (OpaqueCut Reader KemSK X Bool))
      (state : PqxdhDynamicKemJointSource.State KemSK) (runtime : A)

/-- The KEM-game context described by a logged opaque context. -/
noncomputable def toContext (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) {count : Nat} : OpaqueContext Reader KemSK A X count → Context KemSK A Bool count
  | .failed state => .failed state
  | .ready created others cut state runtime =>
    .ready created others (cut.map (toCut setup codec checks created.server.server.metadata.identityIndex
      created.publicIdentity (decideTag decision))) state runtime

/-- The stopped-source logged prephase with the explicit opaque scan in place of the KEM scan. -/
noncomputable def sourcePreOpaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (runtime : A)
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
        (decideTag decision) work index [] [] (PqxdhRegistrationJointInitializedAccept.initial created))).run).run
          (born.2.1.1, PqxdhDynamicKemRouter.empty))
    pure (.ready created others result.1 result.2 born.2.2)

/-- The stopped-source logged prephase of the KEM games is the image of the logged opaque prephase. -/
theorem pre_opaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    PqxdhDeploymentLaterServerKemHop.sourcePre setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected chosen =
      toContext setup codec checks decision <$>
        sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
          index chosen := by
  simp only [PqxdhDeploymentLaterServerKemHop.sourcePre, sourcePreOpaque, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp only [map_pure, toContext]
  · simp only [map_bind]
    apply bind_congr
    intro others
    rw [PqxdhDeploymentLaterServerCut.scanned, scan_opaque, simulateQ_map, OptionT.run_map, StateT.run_map,
      bind_map_left]
    simp only [map_pure, toContext]

/-- The logged opaque postchallenge step: `KemResume.post` on a logged opaque context. The candidate is an argument only of the private client interpreter inside the opaque resumption and of the router. -/
noncomputable def opaquePost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (ResultState KemSK A Bool count) := do
  match transcript.context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners log next)) state _ =>
    if value.keys.pqKey = transcript.publicKey then
      let reached ← (((simulateQ (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey others)
        transcript.ciphertext candidate)
        (simulateQ (actual setup) (opaqueResume setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners log next
          transcript.ciphertext candidate))).run).run state)
      pure (toContext setup codec checks decision transcript.context, some reached)
    else pure (toContext setup codec checks decision transcript.context, none)
  | _ => pure (toContext setup codec checks decision transcript.context, none)

/-- `KemResume.post` on the context described by a logged opaque context is the logged opaque postchallenge step, by `KemOpaqueResume.resume_post` with the logged rest. -/
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
      | pending raw value ephemeral consumed native owners log next =>
        by_cases active : value.keys.pqKey = publicKey
        · simp only [post, opaquePost, toContext, toCut, Option.map_some, active, ↓reduceIte, rawResume, opaqueResume]
          rw [PqxdhRegistrationJointKemOpaqueResume.resume_post]
        · simp only [post, opaquePost, toContext, toCut, Option.map_some, active, ↓reduceIte]

/-- The logged opaque branch: the generic KEM-hop branch at the logged exposure with the opaque prephase and the opaque postchallenge step. -/
noncomputable def opaqueBranch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (opaquePost setup codec checks decision count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- Theorem T6 for the logged source: the branch of the generic KEM hop at the logged exposure equals the logged opaque branch, for both values of the branch bit. A program equality; it charges no advantage. -/
theorem branch_opaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    PqxdhDeploymentLaterServerKemHop.branch setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected real =
      opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real := by
  simp only [PqxdhDeploymentLaterServerKemHop.branch, opaqueBranch, pre_opaque, bind_map_left, post_opaque]

/-- The KEM transfer for the logged source (T4, the KEM hop and T6 composed): in the logged initialized execution of the tagged logged program, with the log forgotten, the final-state event of T4 has probability at most that of the logged opaque KEM-ideal branch, plus one ordinary one-key ML-KEM IND-CCA advantage of the proof-carrying adversary at the logged exposure and one ordinary ML-KEM correctness error. The decision reads the program result, which may contain the Server reveal. -/
theorem transfer (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some (.inl 1)) (count + 1)) :
    (letI := Classical.propDecidable
    𝒟[(fun final => decide (PqxdhRegistrationJointKemRawBridge.Decided decision final ∧
        PqxdhRegistrationJointKemRawBridge.GoodKem selected final ∧
        PqxdhRegistrationJointKemRawBridge.KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map fun outcome =>
          PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied
          (PqxdhDeploymentLaterServerCommands.tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true}) ≤
    𝒟[opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false] {true} +
      ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit supplied
          (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected).toINDCCA).toReal +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  refine (PqxdhDeploymentLaterServerBridge.actual_le_real setup codec checks ensureInit supplied decision work runtime
    count selected index bounded).trans ?_
  rw [← branch_opaque]
  exact PqxdhDeploymentLaterServerKemHop.real_le_ideal setup functional ensureInit supplied
    (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque.scan_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque.scan_opaque

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque.pre_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque.pre_opaque

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque.post_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque.post_opaque

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque.branch_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque.branch_opaque

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque.transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque.transfer
