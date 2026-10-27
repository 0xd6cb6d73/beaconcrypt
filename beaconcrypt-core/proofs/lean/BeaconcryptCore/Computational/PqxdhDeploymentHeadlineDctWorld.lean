-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBillsFull

/-!
# CE-12 D-ct: the containment on the World and the closure of the explicit ciphertext-gap term

The explicit term `ctGapTerm` of the frozen CE-12 headlines is the probability of the ciphertext gap (`PqxdhDeploymentHeadlineGap.ctGapEvent`: an owner's first successful finish reads a different KEM ciphertext from the first successful build of the session that matches it before its acceptance). `PqxdhDeploymentHeadlineDctEvent.ctgap_term_world` already moved it into the per-target record worlds with the ideal environment `envGD`, up to the KEM and slot losses of the decision of `(ctGapNamed, ctClaim)`. This module bounds that decision on each World by `ctStat budget` and so closes the term (design sections 2, 3.2 and 4.7).

- `dct_contain`: on every World outcome where the decision holds, the reassembled final state has `KeyHit` (an R1 value whose sequence-one key is slot 0's key part, `PqxdhDeploymentHeadlineDctTable`) or the World's BLAKE2b cache has a collision (`CtxColl`, `PqxdhDeploymentHeadlineDctHash`). The claimed session is the selected accept, marked at coordinates holding slot 0 (`ideal_trace_world`, `IdealInv.peerMarked`, `Prov.marked`, `designate_peer`); its build carries the challenge ciphertext (`BeaconProv.built`, `ciphertextOf_written`), so the matched owner's finish input does not read it (`not_challengeRead`); the commitment invariant (`PqxdhDeploymentHeadlineDctInvariant.world_dctInv`) commits the build's public frame under slot 0's key part and the finish input's frame, which is the same frame by the pinned match, under the sequence-one key of an R1 value; one frame carries one digest, so the two cached inputs are equal (the keys agree) or distinct (a collision), `commit_same`.
- `ctgap_world`: the decision has probability at most `ctStat budget = r1Cap/2^256 + C(ctxCap, 2)/2^512` on the World of each target (`world_keyHit`, `coll_world`).
- `ctgap_term_le`: `ctGapTerm ≤ epsCt` (`ctgap_term_world` with `ctgap_world` per target), and `ctgap_term_billed` adds the bills of every reduction of `epsCt` (`PqxdhDeploymentHeadlineBillsFull.target_bills`).

No new assumption: the premises are the existing read-back contracts (`Phase1ReadBack`, `Phase2ReadBack`, `FrameReadBack`), the KEM contracts and resource bounds (`FunctionalDecapsulation`, `KemBound`, `qInit`), `SourceFullCorrect` and the budget.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealProvenance (BuiltIn)
open PqxdhServerAuthNegativeControl (Phase1ReadBack Phase2ReadBack FrameReadBack)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineDctEvent (LinkedGap ctSession ctClaim ctGapNamed ctStat epsCt)
open PqxdhDeploymentHeadlineDctCommit (CommitAt)
open PqxdhDeploymentHeadlineDctTable (KeyHit)
open PqxdhDeploymentHeadlineDctHash (CtxColl)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### Public bytes and commitments -/

section Bytes
variable (codec : Codec Reader Response)

/-- Under `Phase2ReadBack`, a build response written with the challenge ciphertext reads the challenge ciphertext. -/
theorem ciphertextOf_written (phase2 : Phase2ReadBack codec) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (response : PqxdhServerRegistrationPublication.Response)
    (written : PqxdhDeploymentIdealBeacon.ChallengeWritten codec challenge response) :
    PqxdhDeploymentHeadlineGap.ciphertextOf codec (some response.serialized) =
      some (PqxdhAcceptedRegistration.ciphertextArray challenge) := by
  obtain ⟨candidate, encrypted, carried, write⟩ := written
  obtain ⟨parsed, readEq, ciphertextEq, -⟩ := phase2 _ _ write
  show (codec.read2 response.serialized).bind codec.ciphertext = _
  rw [readEq, Option.bind_some, ciphertextEq]
  change some candidate.kem_ciphertext = _
  rw [carried]

/-- Two commitments of one public frame in one BLAKE2b cache: the frame's record carries one digest, so either its two cached inputs are equal, and then so are the two keys, or they differ, and then the cache has a collision. -/
theorem commit_same (cache : CtxRomAuth.CtxRO.QueryCache) (bytes bytes' : Pqxdh.Bytes)
    (record : RawCtxReceive.DecodedFrame)
    (framed : PqxdhServerAuthRecordPublicationEvent.frame codec bytes = some record)
    (framed' : PqxdhServerAuthRecordPublicationEvent.frame codec bytes' = some record) (key key' : List UInt8)
    (first : CommitAt codec cache bytes key) (second : CommitAt codec cache bytes' key') : key = key' ∨ CtxColl cache := by
  obtain ⟨frame, frameEq, cipher, digest, input, decoded, committed, cached, taken⟩ := first
  obtain ⟨frame', frameEq', cipher', digest', input', decoded', committed', cached', taken'⟩ := second
  rw [framed, Option.some.injEq] at frameEq
  rw [framed', Option.some.injEq] at frameEq'
  subst frameEq frameEq'
  rw [decoded, Option.some.injEq] at decoded'
  subst decoded'
  have same : digest = digest' := List.Vector.toList_injective (committed.symm.trans committed')
  subst same
  by_cases inputs : input = input'
  · subst inputs
    exact Or.inl (taken.symm.trans taken')
  · exact Or.inr ⟨((), input), ((), input'), digest, fun equal => inputs (congrArg Prod.snd equal), cached, cached'⟩

end Bytes

/-! ### The containment -/

section Contain
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder)

open Classical in
/-- `dct_contain` (design section 2): on every outcome of the record world with the ideal environment of a target, the decision of `(ctGapNamed, ctClaim)` at the target implies the hit of an R1 value's sequence-one key on slot 0's key part, or a BLAKE2b collision of the World's cache. The claimed session is the selected accept (`designate_peer` and the link of `LinkedGap`), which is marked at coordinates holding slot 0 (`ideal_trace_world`, `IdealInv.peerMarked`, `Prov.marked`); the owner's finish input does not read the challenge ciphertext (`BeaconProv.built`, `ciphertextOf_written`, `not_challengeRead`); so the invariant `DctInv` commits the build's frame under slot 0's key part and the finish input's frame, which is the same frame, under the sequence-one key of an R1 value (`commit_same`). -/
theorem dct_contain (phase1 : Phase1ReadBack codec) (phase2 : Phase2ReadBack codec) (frameBack : FrameReadBack codec)
    (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary),
      (PqxdhRecordLiftWorld.observed result).any (PqxdhDeploymentIdealHandoff.decisionOn setup codec budget
          (ctGapNamed setup codec budget) (ctClaim setup.source.crypto codec) g) = true →
        (PqxdhDeploymentEnvironmentJoin.joined result).any
            (fun value => decide (KeyHit setup (PqxdhDeploymentEnvironmentDraw.dropX value.2.2.2))) = true ∨
          (result.1.isSome && decide (CtxColl result.2.primitive.2)) = true := by
  intro result member decided
  rcases found : result.1 with _ | value
  · simp [PqxdhRecordLiftWorld.observed, found] at decided
  simp only [PqxdhRecordLiftWorld.observed, found, Option.map_some, Option.any_some] at decided
  unfold PqxdhDeploymentIdealHandoff.decisionOn ctGapNamed at decided
  simp only [Bool.and_eq_true, decide_eq_true_eq] at decided
  obtain ⟨⟨⟨-, ready⟩, -⟩, targeted⟩ := decided
  -- The claim: the smallest linked gap session `j`, its first build, and the designation of its peer.
  unfold PqxdhDeploymentKemTransfer.target ctClaim at targeted
  obtain ⟨handle, claimed, designatedIn⟩ := Option.bind_eq_some_iff.mp targeted
  obtain ⟨j, sessionFound, claimed⟩ := Option.bind_eq_some_iff.mp claimed
  obtain ⟨response, builtFound, rfl⟩ := Option.map_eq_some_iff.mp claimed
  have linked : LinkedGap setup.source.crypto codec value.2.1.2.transcript j := by
    unfold ctSession at sessionFound
    simpa only [decide_eq_true_eq] using List.find?_some sessionFound
  have designatedG : PqxdhDeploymentTranscript.designate setup.source.crypto codec setup.serverKeyId
      value.2.1.2.transcript (.peer response.keyId) =
        some ((Target.ofCE budget g).accept, (Target.ofCE budget g).kem.val) := by
    unfold PqxdhDeploymentTranscript.designateIn at designatedIn
    obtain ⟨target, designated, ranged⟩ := Option.bind_eq_some_iff.mp designatedIn
    rw [designated]
    split_ifs at ranged with first second
    simp only [Option.some.injEq] at ranged
    subst ranged
    rfl
  -- The World facts at the outcome.
  obtain ⟨annotated, annotatedMember, sameValue, -⟩ := PqxdhDeploymentIdealProvenance.annotated_cover setup codec route
    _ setup.serverKeyId bounds mode adversary result member
  obtain ⟨-, -, inv, prov, beacon⟩ := PqxdhDeploymentIdealBeacon.world_beacon setup codec route checks
    (Target.ofCE budget g) ensureInit 0 runtime setup.serverKeyId bounds mode adversary annotated annotatedMember value
    (by rw [sameValue]; exact found)
  obtain ⟨traceL1, traceL3⟩ := PqxdhDeploymentIdealProvenance.ideal_trace_world setup codec route checks phase1
    (Target.ofCE budget g) ensureInit 0 runtime bounds mode adversary result member value found
  obtain ⟨c', peered⟩ := traceL3 response.keyId designatedG
  obtain ⟨slotZero, -⟩ := traceL1 response.keyId c' peered
  obtain ⟨s, marked⟩ := inv.peerMarked response.keyId c' peered
  obtain ⟨selected, -, -⟩ := prov.marked s c' marked
  subst selected
  -- The claimed session is the selected accept.
  obtain ⟨linkedResponse, -, -, -, linkFound, -⟩ := PqxdhDeploymentTranscript.designate_peer _ _ _ _ _ _ _ designatedG
  obtain ⟨⟨c, before, raw, binding, acceptedFound, -, pin, differ⟩, linkedBuild, built', link⟩ := linked
  rw [builtFound, Option.some.injEq] at built'
  subst built'
  rw [linkFound] at link
  simp only [Option.map_some, Option.some.injEq] at link
  subst link
  -- The pinned build and the owner's finish input share one public frame.
  obtain ⟨-, -, -, payload, reply, record, -, -, -, -, buildMember, -, rawFrame, replyFrame⟩ := pin
  have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw acceptedFound
  have replyBuilt : BuiltIn value.2.1.2.transcript (Target.ofCE budget g).accept reply :=
    ⟨payload, PqxdhDeploymentServerAuth.build_entry _ _ payload reply (prefixed.subset buildMember)⟩
  have responseBuilt : BuiltIn value.2.1.2.transcript (Target.ofCE budget g).accept response :=
    PqxdhDeploymentKeyMatch.buildOf_mem _ _ response builtFound
  obtain ⟨finishFound, -⟩ := PqxdhDeploymentHeadlineGap.ready_accepted _ ready c before raw acceptedFound
  obtain ⟨finishReply, finishMember⟩ := PqxdhDeploymentIdealBeacon.finishOf_mem _ c raw finishFound
  -- The finish input does not read the challenge ciphertext.
  have carries := ciphertextOf_written codec phase2 _ response (beacon.built _ c' response marked responseBuilt)
  rw [finishFound, builtFound, Option.map_some] at differ
  have notRead := PqxdhDeploymentHeadlineDctCommit.not_challengeRead codec _ raw (some response.serialized) carries
    differ
  -- The commitment invariant on the reassembled state.
  have joinedEq : PqxdhDeploymentEnvironmentJoin.joined result = some (value.1, value.2.1.1, value.2.1.2,
      PqxdhDeploymentEnvironmentJoin.merge value.2.2 result.2) := by
    simp only [PqxdhDeploymentEnvironmentJoin.joined, found, Option.map_some]
  have dct := PqxdhDeploymentHeadlineDctInvariant.world_dctInv setup codec checks route (Target.ofCE budget g) phase2
    frameBack ensureInit 0 runtime bounds mode adversary result member _ joinedEq
  obtain ⟨u, v, rootFound, rootCommit⟩ := dct.finishRoot c raw finishReply finishMember notRead
  rcases dct.markedCommit _ c' reply marked replyBuilt with ⟨noSlot, -⟩ | ⟨slot, material, allocated, cachedMaterial,
    buildCommit⟩
  · exact absurd (noSlot.symm.trans slotZero) (by simp)
  change value.2.2.backend.2.2.1.1 c' = some slot at allocated
  rw [slotZero, Option.some.injEq] at allocated
  subst allocated
  rcases commit_same codec _ reply.serialized raw record replyFrame rawFrame _ _ buildCommit rootCommit with
    keys | collision
  · left
    rw [joinedEq, Option.any_some, decide_eq_true_eq]
    refine ⟨u, v, material.1, rootFound, ?_, (List.Vector.toList_injective keys).symm⟩
    show ((PqxdhDeploymentEnvironmentDraw.dropX (PqxdhDeploymentEnvironmentJoin.merge value.2.2 result.2)).backend.1
      0).map Prod.fst = some material.1
    rw [cachedMaterial, Option.map_some]
  · right
    rw [Option.isSome_some, Bool.true_and, decide_eq_true_eq]
    exact collision

end Contain

/-! ### The World bound and the closure of the explicit term -/

section Closure
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)

open Classical in
/-- `ctgap_world` (design-v2 section 8, the binding World form): on the record world with the ideal environment of the target of a designation, the decision of `(ctGapNamed, ctClaim)` has probability at most `ctStat budget` (`dct_contain`, then `world_keyHit` and `coll_world`). -/
theorem ctgap_world (phase1 : Phase1ReadBack codec) (phase2 : Phase2ReadBack codec) (frameBack : FrameReadBack codec)
    (caps : KemCaps) (bounded : KemBound setup caps) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any
        (PqxdhDeploymentIdealHandoff.decisionOn setup codec budget (ctGapNamed setup codec budget)
          (ctClaim setup.source.crypto codec) g)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary] {true} ≤ ctStat budget :=
  (PqxdhDeploymentHeadlineGap.chance_le_add_support _ _ _ _
    (dct_contain setup codec checks route phase1 phase2 frameBack ensureInit runtime bounds mode adversary budget g)).trans
    (add_le_add (PqxdhDeploymentHeadlineDctTable.world_keyHit setup codec checks route (Target.ofCE budget g) ensureInit
      0 runtime bounds mode adversary budget respects)
      (PqxdhDeploymentHeadlineDctHash.coll_world setup codec checks route ensureInit bounds mode adversary budget caps
        bounded qInit initBound respects g runtime))

/-- `ctgap_term_le`: the explicit ciphertext-gap term of the frozen headlines is at most `epsCt` (`ctgap_term_world`, then `ctgap_world` at each target). -/
theorem ctgap_term_le (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (phase1 : Phase1ReadBack codec) (phase2 : Phase2ReadBack codec) (frameBack : FrameReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) :
    PqxdhDeploymentHeadlineGap.ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime ≤
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime := by
  refine (PqxdhDeploymentHeadlineDctEvent.ctgap_term_world setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects runtime).trans ?_
  unfold epsCt
  refine Finset.sum_le_sum fun g _ => ?_
  have world := ctgap_world setup codec checks route ensureInit phase1 phase2 frameBack caps bounded qInit initBound
    bounds mode adversary budget respects ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity) runtime
  calc _ ≤ ctStat budget + ENNReal.ofReal (PqxdhDeploymentHeadlineChain.kemLoss setup codec checks route ensureInit
          bounds mode adversary budget (ctGapNamed setup codec budget) (ctClaim setup.source.crypto codec)
          ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity) runtime) +
        ENNReal.ofReal (PqxdhDeploymentHeadlineChain.slotLoss setup codec checks route ensureInit bounds mode adversary
          budget (ctGapNamed setup codec budget) (ctClaim setup.source.crypto codec)
          ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity) runtime) :=
        add_le_add (add_le_add world le_rfl) le_rfl
    _ = _ := by ring

/-- `ctgap_term_le` with the bills of every reduction of `epsCt` (`PqxdhDeploymentHeadlineBillsFull.target_bills`, whose KEM and slot fields are quantified over every event and claim, so they bill the KEM and slot losses at `(ctGapNamed, ctClaim)`). -/
theorem ctgap_term_billed (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (phase1 : Phase1ReadBack codec) (phase2 : Phase2ReadBack codec) (frameBack : FrameReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    PqxdhDeploymentHeadlineGap.ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime ≤
      epsCt setup codec checks route ensureInit bounds mode adversary budget runtime ∧
    PqxdhDeploymentHeadlineBillsFull.TargetBills setup codec checks route caps ensureInit qInit bounds mode adversary
      budget runtime :=
  ⟨ctgap_term_le setup codec checks route ensureInit functional phase1 phase2 frameBack correct caps bounded qInit
      initBound bounds mode adversary budget respects runtime,
    PqxdhDeploymentHeadlineBillsFull.target_bills setup codec checks route correct caps bounded ensureInit qInit initBound
      bounds mode adversary budget respects runtime fallback⟩

end Closure

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.ciphertextOf_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.ciphertextOf_written

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.commit_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.commit_same

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.dct_contain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.dct_contain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.ctgap_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.ctgap_world

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.ctgap_term_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.ctgap_term_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctWorld.ctgap_term_billed
