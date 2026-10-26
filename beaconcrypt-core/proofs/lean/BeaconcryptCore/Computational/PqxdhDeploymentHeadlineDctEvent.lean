-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain
import BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay

/-!
# CE-12 D-ct, the CE side: the named ciphertext-gap event and its split over targets

The explicit term `ctGapTerm` of the F-ct2 headlines (`PqxdhDeploymentHeadlineGap`) is the probability that the experiment ends with `CtGapEvent`: some owner `c` accepted with a pinned match `j` whose build ciphertext differs from `c`'s finish ciphertext. This module moves it into the per-target ideal worlds (design-v2 section 8, the D-ct final design section 3).

- Claim. `LinkedGap j`: session `j` has a ciphertext gap with some owner and the key ID of its first successful build links back to `j` (`linkOf`). `ctSession` is the smallest linked gap session below the number of accept attempts, and `ctClaim` names the Server peer that session built.
- Event. `ctGapNamed` is `ctGapEvent` together with the public `FinishReady` of the transcript and the claim designated inside the budget. On every outcome of the experiment of a budget-respecting adversary `ctGapEvent` implies `ctGapNamed` (`ctgap_named`): `FinishReady` holds on every outcome (`ready_game`); the gap session's first build exists, and its key ID links back to it because successful builds take pairwise distinct key IDs (`keyId_game`: the native Server installs a build at a free key ID, `build_footprint`, and never removes a peer, `native_peers_kept`); and the session's accept bytes verify to the gap owner's published keys, so `designate` names the session and an owner (`designate_peer_complete`) inside the budget (`range_game`).
- Split. `ctgap_split_sum`: `ctGapTerm` is the sum over targets `g` of the probability of the event with the claim designating `g` (`split_named`). `ctgap_term_world`: each summand is at most the probability of the decision of `g` on the record world with the ideal environment of `g` plus `kemLoss` and `slotLoss` (`chain_slot`, `ideal_world`).
- Bound. `ctStat` is the statistical term of the World bound (`r1Cap` R1 values against a uniform 256-bit key, and the birthday term of `ctxCap` BLAKE2b calls), and `epsCt` is the sum over targets of `kemLoss`, `slotLoss` and `ctStat`.

No assumption beyond the premises of `chain_slot` (`FunctionalDecapsulation`, `SourceFullCorrect`), the approved read-back contracts and the budget is used.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentTranscript (buildOf linkOf acceptCount acceptOf)
open PqxdhDeploymentRecordKernels (PeerStep peerKernel)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### The claim, the event and the bound -/

section Definitions
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)

/-- Session `j` has a ciphertext gap with some owner, and the key ID of its first successful build links back to it. -/
def LinkedGap (transcript : List Entry) (j : ℕ) : Prop :=
  (∃ c, PqxdhDeploymentHeadlineGap.CtGap crypto codec transcript c j) ∧
    ∃ response, buildOf transcript j = some response ∧ (linkOf transcript response.keyId).map Prod.fst = some j

open Classical in
/-- The smallest linked gap session below the number of accept attempts. -/
noncomputable def ctSession (transcript : List Entry) : Option ℕ :=
  (List.range (acceptCount transcript)).find? fun j => decide (LinkedGap crypto codec transcript j)

/-- `ctClaim`: the Server peer built by the smallest linked gap session. -/
noncomputable def ctClaim (observed : Observed X) : Option Handle :=
  (ctSession crypto codec observed.2.1.transcript).bind fun j =>
    (buildOf observed.2.1.transcript j).map fun response => .peer response.keyId

end Definitions

open Classical in
/-- The event of the split: the public gap event, the public finish-readiness of the transcript, and the claim designated inside the budget. -/
noncomputable def ctGapNamed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (observed : Observed X) : Bool :=
  PqxdhDeploymentHeadlineGap.ctGapEvent setup.source.crypto codec observed &&
    decide (PqxdhDeploymentHeadlineGap.FinishReady observed.2.1.transcript) &&
    (PqxdhDeploymentKemTransfer.target setup.source.crypto codec setup.serverKeyId budget
      (ctClaim setup.source.crypto codec) observed).isSome

/-- R1 (Extract-table) values a run can create: public HMAC calls, Server accept roots, Beacon finish roots. -/
def r1Cap (budget : Budget) : ℕ := budget.hmac + budget.accept + budget.finish

/-- BLAKE2b calls of the record world (`PqxdhDeploymentEnvironment.c4_closed`'s count, CE-11's shared-hash cap). -/
def ctxCap (budget : Budget) : ℕ := budget.hash + budget.sends + budget.receives + budget.build + budget.finish

/-- The statistical term of one target: the averaged R1 term and the birthday term of the record world's BLAKE2b cache. -/
noncomputable def ctStat (budget : Budget) : ℝ≥0∞ :=
  (r1Cap budget : ℝ≥0∞) / 2 ^ 256 + ((ctxCap budget).choose 2 : ℝ≥0∞) / 2 ^ 512

/-- `ε_ct`: over every target, the KEM and slot losses of the decision of `(ctGapNamed, ctClaim)` and `ctStat`. -/
noncomputable def epsCt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A) : ℝ≥0∞ :=
  ∑ g : Fin budget.accept × Fin budget.create,
    (ENNReal.ofReal (PqxdhDeploymentHeadlineChain.kemLoss setup codec checks route ensureInit bounds mode adversary
        budget (ctGapNamed setup codec budget) (ctClaim setup.source.crypto codec)
        ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity) runtime) +
      ENNReal.ofReal (PqxdhDeploymentHeadlineChain.slotLoss setup codec checks route ensureInit bounds mode adversary
        budget (ctGapNamed setup codec budget) (ctClaim setup.source.crypto codec)
        ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity) runtime) +
      ctStat budget)

/-! ### Server peers are never removed -/

section Peers

/-- Every Server peer installed before is installed after. -/
def PeersKept (before after : PqxdhDeploymentNative.State KemSK) : Prop :=
  ∀ kid, (before.native.shared.2.server.server.peers kid).isSome = true →
    (after.native.shared.2.server.server.peers kid).isSome = true

theorem peersKept_trans {first second third : PqxdhDeploymentNative.State KemSK} (one : PeersKept first second)
    (two : PeersKept second third) : PeersKept first third :=
  fun kid installed => two kid (one kid installed)

/-- A registration step that keeps every peer kernel except installations keeps every peer. -/
theorem peerStep_kept (c : Pqxdh.Crypto) (before after : RawCtxServerRouting.Server Unit Unit) (step : PeerStep c before after)
    (kid : Aeneas.Std.U64) (installed : (before.peers kid).isSome = true) : (after.peers kid).isSome = true := by
  have kernel : (peerKernel before kid).isSome = true := by
    simp only [peerKernel, Option.isSome_map]
    exact installed
  rcases step kid with same | ⟨absent, _⟩
  · have after' : (peerKernel after kid).isSome = true := by rw [same]; exact kernel
    simpa only [peerKernel, Option.isSome_map] using after'
  · rw [absent] at kernel
    cases kernel

/-- Putting a peer back keeps every peer. -/
theorem putPeer_kept (server : RawCtxServerRouting.Server Unit Unit) (selected : Aeneas.Std.U64)
    (peer : RawCtxServerRouting.Peer Unit) (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (kid : Aeneas.Std.U64) (installed : (server.peers kid).isSome = true) :
    ((RawCtxServerRouting.putPeer server selected peer kernel).peers kid).isSome = true := by
  by_cases same : kid = selected
  · subst same
    rw [RawCtxServerRouting.putPeer_selected]
    rfl
  · rw [RawCtxServerRouting.putPeer_other _ _ _ _ _ same]
    exact installed

/-- A Server record step keeps every peer: a send or a routed receive puts the addressed peer back with its new kernel. -/
theorem serverStep_kept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.serverStep setup codec route query).run state)) :
    PeersKept state result.2 := by
  intro kid installed
  simp only [PqxdhDeploymentNative.serverStep, StateT.run, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  change inner ∈ support (StateT.run (PqxdhDeploymentNative.record setup codec _) state.native) at member
  rw [PqxdhDeploymentNative.record_run, support_map] at member
  obtain ⟨recorded, recordedMember, rfl⟩ := member
  have reached := PqxdhDeploymentRecordReplay.logged_support _ _ _ recorded recordedMember
  change ((recorded.1.1.2.server.peers kid).isSome = true)
  rcases query with ⟨plaintext, target⟩ | raw
  · change _ ∈ support ((simulateQ (PqxdhDeploymentNative.primitives setup codec) (RawCtxServerMixed.sendServer
      (PqxdhDeploymentNative.senderId state) plaintext target (PqxdhDeploymentNative.serverView state))).run _) at reached
    rw [RawCtxServerMixed.send_interpretation] at reached
    rcases RawCtxServerSend.sendGame_cases _ _ plaintext target _ _ _ reached with ⟨_, missing⟩ | ⟨peer, step, _,
      _, shape⟩
    · rw [congrArg (fun reached => reached.1.2) missing]
      exact installed
    · rw [congrArg (fun reached => reached.1.2) shape]
      exact putPeer_kept _ target peer _ kid installed
  · change _ ∈ support ((simulateQ (PqxdhDeploymentNative.primitives setup codec) (RawCtxServerMixed.rawServer route
      codec.frameRead raw (PqxdhDeploymentNative.serverView state))).run _) at reached
    rw [RawCtxServerMixed.raw_interpretation, PqxdhDeploymentNative.primitives,
      RawCtxReceiveConsumption.shared_receiveNative] at reached
    rcases RawCtxServerRouting.rawGame_cases _ route codec.frameRead raw _ _ _ reached with
      rejected | ⟨routed, peer, received, _, _, _, shape⟩
    · rw [congrArg (fun reached => reached.1.2) rejected]
      exact installed
    · rw [congrArg (fun reached => reached.1.2) shape]
      exact putPeer_kept _ routed peer _ kid installed

/-- Every query of the native deployment handler keeps every Server peer. -/
theorem native_peers_kept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (query : PqxdhDeploymentInterface.Spec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (result : PqxdhDeploymentInterface.Spec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state)) :
    PeersKept state result.2 := by
  have source : ∀ (request : PqxdhRegistrationSchedule.Request)
      (result : PqxdhRegistrationSchedule.QuerySpec request × PqxdhDeploymentNative.State KemSK),
      result ∈ support ((PqxdhDeploymentNative.onNative
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request))).run state) →
      PeersKept state result.2 := by
    intro request result member
    obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state result member
    exact peerStep_kept _ _ _ (PqxdhDeploymentRecordKernels.source_step setup codec checks serverSeed request
      state.native inner innerMember).1
  rcases query with coin | command
  · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact fun _ installed => installed
  · cases command with
    | create pin keyId =>
        cases parsed : PqxdhDeploymentInterface.parsePin pin with
        | none =>
            simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            subst supported
            exact fun _ installed => installed
        | some word =>
            simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_map, support_map, Set.mem_image] at supported
            obtain ⟨inner, member, rfl⟩ := supported
            exact source (.create word keyId) inner member
    | bundle owner => exact source (.bundle owner) result supported
    | accept raw => exact source (.accept raw) result supported
    | build session payload => exact source (.build session payload) result supported
    | finish owner raw => exact source (.finish owner raw) result supported
    | hmac key message => exact source (.hmac key message) result supported
    | hash bytes => exact source (.hash bytes) result supported
    | serverSend kid plaintext => exact serverStep_kept setup codec route (.inl (plaintext, kid)) state result supported
    | serverRaw raw => exact serverStep_kept setup codec route (.inr raw) state result supported
    | beaconSend index plaintext =>
        intro kid installed
        rw [(PqxdhDeploymentNative.beaconStep_fields setup codec index (.inl plaintext) state result supported).2.2.1]
        exact installed
    | beaconRaw index raw =>
        intro kid installed
        rw [(PqxdhDeploymentNative.beaconStep_fields setup codec index (.inr raw) state result supported).2.2.1]
        exact installed

/-- A whole native program keeps every Server peer. -/
theorem run_peers_kept {Value : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (program : OracleComp PqxdhDeploymentInterface.Spec Value) (state : PqxdhDeploymentNative.State KemSK)
    (result : Value × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
      program).run state)) :
    PeersKept state result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
    (fun after => PeersKept state after)
    (fun query middle kept next member => peersKept_trans kept
      (native_peers_kept setup codec checks route serverSeed query middle next member))
    program state (fun _ installed => installed) result supported

end Peers

/-! ### Successful builds take pairwise distinct key IDs -/

section KeyIds

/-- The key ID of a successful build entry. -/
def buildKeyId : Entry → Option Aeneas.Std.U64
  | ⟨.inl (.inr (.build _ _)), some response⟩ => some response.keyId
  | _ => none

/-- The CE run invariant behind the link of a build's key ID: every successful build's key ID is an installed Server peer, and successful builds have pairwise distinct key IDs. -/
structure KeyIdTrace (transcript : List Entry) (native : PqxdhDeploymentNative.State KemSK) : Prop where
  installed : ∀ s payload r, (⟨.inl (.inr (.build s payload)), some r⟩ : Entry) ∈ transcript →
    (native.native.shared.2.server.server.peers r.keyId).isSome = true
  distinct : (transcript.filterMap buildKeyId).Nodup

/-- A successful build entry's key ID is in the key-ID list. -/
theorem buildKeyId_mem (transcript : List Entry) (s : ℕ) (payload : Option Pqxdh.Bytes)
    (r : PqxdhServerRegistrationPublication.Response)
    (member : (⟨.inl (.inr (.build s payload)), some r⟩ : Entry) ∈ transcript) :
    r.keyId ∈ transcript.filterMap buildKeyId :=
  List.mem_filterMap.mpr ⟨_, member, rfl⟩

/-- A key ID in the key-ID list belongs to a successful build entry. -/
theorem mem_buildKeyId (transcript : List Entry) (kid : Aeneas.Std.U64) (member : kid ∈ transcript.filterMap buildKeyId) :
    ∃ s payload r, (⟨.inl (.inr (.build s payload)), some r⟩ : Entry) ∈ transcript ∧ r.keyId = kid := by
  obtain ⟨entry, entryMember, found⟩ := List.mem_filterMap.mp member
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · cases found
  · cases command with
    | build s payload =>
        cases reply with
        | none => cases found
        | some r =>
            simp only [buildKeyId, Option.some.injEq] at found
            exact ⟨s, payload, r, entryMember, found⟩
    | _ => cases found
  · cases found

/-- A successful native build installs its key ID, which was free before. -/
theorem native_build_fresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed
      (.inr (.build session payload))).run state))
    (response : PqxdhServerRegistrationPublication.Response) (built : result.1 = some response) :
    state.native.shared.2.server.server.peers response.keyId = none ∧
      (result.2.native.shared.2.server.server.peers response.keyId).isSome = true := by
  obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state result supported
  simp only [PqxdhRegistrationSchedule.handler, ← PqxdhServerAuthNative.build_native setup codec checks serverSeed
    PqxdhRegistrationSchedule.observationScalar] at innerMember
  obtain ⟨_, reached⟩ :=
    PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ state.native inner innerMember
  obtain ⟨_, _, _, _, _, _, published⟩ := PqxdhDeploymentCompileFootprint.build_footprint setup codec checks session
    payload _ _ reached
  obtain ⟨token, kernel, fields, _, free, peers, _⟩ := published response built
  refine ⟨free, ?_⟩
  change (inner.2.shared.2.server.server.peers response.keyId).isSome = true
  rw [peers, Function.update_self]
  rfl

/-- One query of the experiment keeps `KeyIdTrace`. -/
theorem keyId_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (query : PqxdhDeploymentInterface.Query) (state : PqxdhDeploymentSecrecy.State KemSK)
    (trace : KeyIdTrace state.1.transcript state.2)
    (result : PqxdhDeploymentInterface.FullSpec.Range query × PqxdhDeploymentSecrecy.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds query).run
      state)) :
    KeyIdTrace result.2.1.transcript result.2.2 := by
  rcases state with ⟨ledger, native⟩
  rw [PqxdhDeploymentEligibility.handler_run, support_map] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at member
    obtain ⟨answer, answerMember, rfl⟩ := member
    have kept := native_peers_kept setup codec checks route serverSeed request native answer answerMember
    have fresh : ∀ kid, buildKeyId ⟨.inl request, answer.1⟩ = some kid →
        native.native.shared.2.server.server.peers kid = none ∧
          (answer.2.native.shared.2.server.server.peers kid).isSome = true := by
      intro kid found
      rcases request with coin | command
      · cases found
      · cases command with
        | build session payload =>
            rcases answer with ⟨_ | response, after⟩
            · cases found
            · simp only [buildKeyId, Option.some.injEq] at found
              subst found
              exact native_build_fresh setup codec checks route serverSeed session payload native _ answerMember
                response rfl
        | _ => cases found
    refine ⟨fun s payload r entry => ?_, ?_⟩
    · change (⟨.inl (.inr (.build s payload)), some r⟩ : Entry) ∈ ledger.transcript ++ [(⟨.inl request, answer.1⟩ : Entry)]
        at entry
      rcases List.mem_append.mp entry with old | new
      · exact kept _ (trace.installed s payload r old)
      · rw [List.mem_singleton] at new
        exact (fresh r.keyId (by rw [← new]; rfl)).2
    · change ((ledger.transcript ++ [(⟨.inl request, answer.1⟩ : Entry)]).filterMap buildKeyId).Nodup
      rw [List.filterMap_append, List.nodup_append]
      refine ⟨trace.distinct, ?_, ?_⟩
      · cases found : buildKeyId ⟨.inl request, answer.1⟩ <;> simp [found]
      · intro kid old kid' new
        cases found : buildKeyId ⟨.inl request, answer.1⟩ with
        | none => simp [found] at new
        | some value =>
            simp only [List.filterMap_cons, found, List.filterMap_nil, List.mem_singleton] at new
            subst new
            intro same
            subst same
            obtain ⟨s, payload, r, entry, keyEq⟩ := mem_buildKeyId _ kid old
            have installed := trace.installed s payload r entry
            rw [keyEq, (fresh kid found).1] at installed
            cases installed
  · have value : reached.1 ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId
        bounds (.inr secrecy)).run ledger) := by
      apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
        _ native
      rw [StateT.run'_eq, support_map]
      exact ⟨reached, member, rfl⟩
    have recorded := PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy
      ledger reached.1 value
    have kept := run_peers_kept setup codec checks route serverSeed _ native reached member
    show KeyIdTrace reached.1.2.transcript reached.2
    rw [recorded]
    refine ⟨fun s payload r entry => ?_, ?_⟩
    · rcases List.mem_append.mp entry with old | new
      · exact kept _ (trace.installed s payload r old)
      · simp at new
    · have quiet : buildKeyId (⟨.inr secrecy, reached.1.1⟩ : Entry) = none := rfl
      rw [List.filterMap_append, List.filterMap_cons, quiet, List.filterMap_nil, List.append_nil]
      exact trace.distinct

/-- `KeyIdTrace` on every outcome of the experiment. -/
theorem keyId_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) :
    KeyIdTrace final.1.transcript final.2 := by
  simp only [PqxdhDeploymentSecrecy.game, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, _, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    cases reached
    exact OracleComp.simulateQ_run_preserves_inv_of_query
      (PqxdhDeploymentSecrecy.handler setup codec checks route constructed.seed bounds)
      (fun state => KeyIdTrace state.1.transcript state.2)
      (fun query state trace result member => keyId_step setup codec checks route constructed.seed bounds query state
        trace result member)
      (PqxdhDeploymentInterface.asModeO mode adversary)
      (PqxdhDeploymentSecrecy.Ledger.empty, PqxdhDeploymentNative.initial constructed)
      ⟨fun _ _ _ entry => by simp [PqxdhDeploymentSecrecy.Ledger.empty] at entry,
        by simp [PqxdhDeploymentSecrecy.Ledger.empty]⟩ _ executedMember

/-- With distinct build key IDs, the first build of a session is the first build of its key ID. -/
theorem link_of_distinct (transcript : List Entry) (distinct : (transcript.filterMap buildKeyId).Nodup) (j : ℕ)
    (response : PqxdhServerRegistrationPublication.Response) (found : buildOf transcript j = some response) :
    (linkOf transcript response.keyId).map Prod.fst = some j := by
  induction transcript with
  | nil => cases found
  | cons entry rest ih =>
      rcases entry with ⟨(coin | command) | secrecy, reply⟩
      · exact ih (by simpa [List.filterMap_cons, buildKeyId] using distinct)
          (by simpa [buildOf, List.findSome?_cons] using found)
      · cases command with
        | build s payload =>
            cases reply with
            | none =>
                exact ih (by simpa [List.filterMap_cons, buildKeyId] using distinct)
                  (by simpa [buildOf, List.findSome?_cons] using found)
            | some built =>
                simp only [List.filterMap_cons, buildKeyId, List.nodup_cons] at distinct
                by_cases same : s = j
                · subst same
                  simp only [buildOf, List.findSome?_cons, ite_true, Option.some.injEq] at found
                  subst found
                  simp [linkOf]
                · have rest_found : buildOf rest j = some response := by
                    simpa [buildOf, List.findSome?_cons, same] using found
                  by_cases key : built.keyId = response.keyId
                  · exfalso
                    obtain ⟨payload', member⟩ := PqxdhDeploymentKeyMatch.buildOf_mem rest j response rest_found
                    exact distinct.1 (key ▸ buildKeyId_mem rest j payload' response member)
                  · have step : linkOf (⟨.inl (.inr (.build s payload)), some built⟩ :: rest) response.keyId =
                        linkOf rest response.keyId := by
                      simp [linkOf, key]
                    rw [step]
                    exact ih distinct.2 rest_found
        | _ =>
            exact ih (by simpa [List.filterMap_cons, buildKeyId] using distinct)
              (by simpa [buildOf, List.findSome?_cons] using found)
      · exact ih (by simpa [List.filterMap_cons, buildKeyId] using distinct)
          (by simpa [buildOf, List.findSome?_cons] using found)

/-- On every outcome of the experiment, the first build of every session links back to it. -/
theorem build_keyId_link (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) (j : ℕ)
    (response : PqxdhServerRegistrationPublication.Response) (found : buildOf final.1.transcript j = some response) :
    (linkOf final.1.transcript response.keyId).map Prod.fst = some j :=
  link_of_distinct _ (keyId_game setup codec checks route ensureInit identityIndex bounds mode adversary runtime outcome
    supported created output final reached).distinct j response found

end KeyIds

/-! ### The gap event is the named event on the support -/

section Named

/-- On every outcome of the experiment, a gap session is a linked gap session below the number of accept attempts, whose accept bytes are the matched accept's. -/
theorem linkedGap_of_gap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (c j : ℕ)
    (gap : PqxdhDeploymentHeadlineGap.CtGap setup.source.crypto codec final.1.transcript c j) :
    LinkedGap setup.source.crypto codec final.1.transcript j ∧ j < acceptCount final.1.transcript := by
  obtain ⟨before, raw, binding, acceptedFound, bindingFound, pin, different⟩ := gap
  obtain ⟨acceptRaw, candidate, keys, payload, reply, record, acceptMember, candidateFound, keysFound, publishedFound,
    buildMember, _, _, _⟩ := pin
  have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw acceptedFound
  have buildEntry := PqxdhDeploymentServerAuth.build_entry final.1.transcript j payload reply
    (prefixed.subset buildMember)
  have buildSome : (buildOf final.1.transcript j).isSome := by
    unfold buildOf
    rw [List.findSome?_isSome_iff]
    exact ⟨_, buildEntry, by simp⟩
  obtain ⟨response, responseFound⟩ := Option.isSome_iff_exists.mp buildSome
  have link := build_keyId_link setup codec checks route ensureInit 0 bounds mode adversary runtime outcome member
    created output final found j response responseFound
  obtain ⟨sessionBound, _⟩ := PqxdhDeploymentHeadlineGap.accept_positional setup codec checks route ensureInit phase1
    phase2 bounds mode adversary runtime outcome member created output final found acceptRaw j
    (PqxdhDeploymentHeadlineGap.accept_entry _ acceptRaw (some j) (prefixed.subset acceptMember))
  exact ⟨⟨⟨c, before, raw, binding, acceptedFound, bindingFound, ⟨acceptRaw, candidate, keys, payload, reply, record,
    acceptMember, candidateFound, keysFound, publishedFound, buildMember, by assumption, by assumption,
    by assumption⟩, different⟩, response, responseFound, link⟩, sessionBound⟩

/-- On every outcome of the experiment of a budget-respecting adversary, the Server peer of a linked gap session is designated inside the budget. -/
theorem linkedGap_designated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (j : ℕ)
    (linked : LinkedGap setup.source.crypto codec final.1.transcript j)
    (response : PqxdhServerRegistrationPublication.Response) (built : buildOf final.1.transcript j = some response) :
    (PqxdhDeploymentTranscript.designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript
      (.peer response.keyId)).isSome = true := by
  obtain ⟨⟨c, before, raw, binding, acceptedFound, bindingFound, pin, _⟩, response', built', link⟩ := linked
  rw [built] at built'
  cases built'
  obtain ⟨acceptRaw, candidate, keys, payload, reply, record, acceptMember, candidateFound, keysFound, publishedFound,
    buildMember, _, _, _⟩ := pin
  have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw acceptedFound
  obtain ⟨_, acceptFound⟩ := PqxdhDeploymentHeadlineGap.accept_positional setup codec checks route ensureInit phase1
    phase2 bounds mode adversary runtime outcome member created output final found acceptRaw j
    (PqxdhDeploymentHeadlineGap.accept_entry _ acceptRaw (some j) (prefixed.subset acceptMember))
  obtain ⟨⟨session, linkedResponse⟩, linkFound, sessionEq⟩ := Option.map_eq_some_iff.mp link
  simp only at sessionEq
  subst sessionEq
  unfold PqxdhDeploymentServerAuthEvent.publishedKeys PqxdhDeploymentServerAuthEvent.keysOfBundle at publishedFound
  obtain ⟨bytes, bytesFound, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨published, candidateRead, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedRest
  obtain ⟨identityKey, identityParsed, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedRest
  obtain ⟨tuple, tupleFound, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedRest
  simp only [Option.pure_def, Option.some.injEq] at publishedRest
  have bundleFound : PqxdhDeploymentTranscript.bundleOf final.1.transcript c = some bytes := by
    rw [← PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_regsOf]
    exact PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_prefix _ _ prefixed c bytes bytesFound
  have publishes : PqxdhDeploymentTranscript.Publishes codec final.1.transcript candidate keys.2.pqKey c := by
    refine ⟨published, by rw [bundleFound, Option.bind_some, candidateRead], ?_, ?_⟩
    · rw [(PqxdhEd25519EufCma.parseIdentity_eq_some_iff _ _).mp identityParsed,
        PqxdhDeploymentHeadlineGap.acceptedKeys_identity setup.source.crypto candidate keys.1 keys.2 keysFound,
        ← publishedRest]
    · rw [← publishedRest]
      exact PqxdhDeploymentHeadlineGap.candidateTuple_pq published tuple tupleFound
  have createdBound : c < (PqxdhDeploymentTranscript.summarize final.1.transcript).owners.length :=
    (List.getElem?_eq_some_iff.mp bindingFound).1
  obtain ⟨first, _, designated⟩ := PqxdhDeploymentTranscript.designate_peer_complete setup.source.crypto codec
    setup.serverKeyId response.keyId final.1.transcript session linkedResponse acceptRaw candidate keys c linkFound
    acceptFound candidateFound keysFound createdBound publishes
  have observed : PqxdhDeploymentKemTransfer.observeGame outcome.1 = some (output, final.1, final.2.produced) := by
    rw [found]
    rfl
  obtain ⟨firstBound, kBound⟩ := PqxdhDeploymentTargetRange.range_game setup codec checks route ensureInit phase1
    phase2 bounds mode adversary budget respects runtime outcome member _ observed (.peer response.keyId) session first
    designated
  rw [PqxdhDeploymentTargetRange.designateIn_range _ codec _ budget _ (.peer response.keyId) session first designated
    firstBound kBound]
  rfl

/-- `ctgap_named`: on every outcome of the experiment of a budget-respecting adversary, the gap event implies the named event. -/
theorem ctgap_named (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (held : happens (PqxdhDeploymentHeadlineGap.ctGapEvent setup.source.crypto codec) outcome = true) :
    happens (ctGapNamed setup codec budget) outcome = true := by
  classical
  unfold happens at held ⊢
  cases found : outcome.1 with
  | none => simp [found, PqxdhDeploymentKemTransfer.observeGame] at held
  | some value =>
      obtain ⟨created, output, final⟩ := value
      rw [found] at held
      change Option.any _ (some (output, final.1, final.2.produced)) = true at held ⊢
      rw [Option.any_some] at held ⊢
      have gapEvent := held
      simp only [PqxdhDeploymentHeadlineGap.ctGapEvent, decide_eq_true_eq] at held
      obtain ⟨c, j, gap⟩ := held
      have ready := PqxdhDeploymentHeadlineGap.ready_game setup codec checks route ensureInit 0 bounds mode adversary
        runtime outcome member created output final found
      obtain ⟨linked, bound⟩ := linkedGap_of_gap setup codec checks route ensureInit phase1 phase2 bounds mode adversary
        runtime outcome member created output final found c j gap
      have some : (ctSession setup.source.crypto codec final.1.transcript).isSome := by
        unfold ctSession
        rw [List.find?_isSome]
        exact ⟨j, List.mem_range.mpr bound, decide_eq_true linked⟩
      obtain ⟨chosen, chosenFound⟩ := Option.isSome_iff_exists.mp some
      have chosenLinked : LinkedGap setup.source.crypto codec final.1.transcript chosen := by
        have holds := List.find?_some chosenFound
        simpa using holds
      obtain ⟨_, response, built, _⟩ := id chosenLinked
      have designated := linkedGap_designated setup codec checks route ensureInit phase1 phase2 bounds mode adversary
        budget respects runtime outcome member created output final found chosen chosenLinked response built
      simp only [ctGapNamed, gapEvent, ready, decide_true, Bool.true_and, PqxdhDeploymentKemTransfer.target, ctClaim,
        chosenFound, Option.bind_some, built, Option.map_some]
      exact designated

end Named

/-! ### The split over targets and the per-target ideal worlds -/

section Split

/-- `ctgap_split_sum`: the explicit term is the sum over targets of the probability that the experiment ends with the named event and the claim designating the target. -/
theorem ctgap_split_sum (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    PqxdhDeploymentHeadlineGap.ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime =
      ∑ g : Fin budget.accept × Fin budget.create,
        𝒟[(fun outcome => decide (happens (ctGapNamed setup codec budget) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget (ctClaim setup.source.crypto codec) outcome =
            some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} := by
  unfold PqxdhDeploymentHeadlineGap.ctGapTerm
  rw [PqxdhDeploymentHeadlineSymbolicLor.chance_eq_support _ _
    (fun outcome => happens (ctGapNamed setup codec budget) outcome) fun outcome member =>
      ⟨ctgap_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects runtime outcome
        member, fun named => by
          unfold happens at named ⊢
          cases found : PqxdhDeploymentKemTransfer.observeGame outcome.1 with
          | none => simp [found] at named
          | some observed =>
              rw [found, Option.any_some] at named
              rw [Option.any_some]
              simp only [ctGapNamed, Bool.and_eq_true] at named
              exact named.1.1⟩]
  exact PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects (ctGapNamed setup codec budget) (ctClaim setup.source.crypto codec) runtime fun observed held => by
      simp only [ctGapNamed, Bool.and_eq_true] at held
      exact held.2

/-- `ctgap_term_world` (the D-ct checkpoint): the explicit term is at most the sum over targets `g` of the probability of the decision of `(ctGapNamed, ctClaim)` at `g` on the record world with the ideal environment of `g`, plus `kemLoss` and `slotLoss` of that decision. -/
theorem ctgap_term_world (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) :
    PqxdhDeploymentHeadlineGap.ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any
            (PqxdhDeploymentIdealHandoff.decisionOn setup codec budget (ctGapNamed setup codec budget)
              (ctClaim setup.source.crypto codec) ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
          PqxdhRecordLiftWorld.run setup codec route
            (PqxdhDeploymentIdealEnv.envGD setup codec checks
              (PqxdhDeploymentIdealParams.Target.ofCE budget
                ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity)) ensureInit 0 runtime)
            setup.serverKeyId bounds mode adversary] {true} +
          ENNReal.ofReal (PqxdhDeploymentHeadlineChain.kemLoss setup codec checks route ensureInit bounds mode adversary
            budget (ctGapNamed setup codec budget) (ctClaim setup.source.crypto codec)
            ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity) runtime) +
          ENNReal.ofReal (PqxdhDeploymentHeadlineChain.slotLoss setup codec checks route ensureInit bounds mode adversary
            budget (ctGapNamed setup codec budget) (ctClaim setup.source.crypto codec)
            ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity) runtime)) := by
  rw [ctgap_split_sum setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects runtime]
  refine Finset.sum_le_sum fun g _ => ?_
  have chain := PqxdhDeploymentHeadlineChain.chain_slot setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects (ctGapNamed setup codec budget) (ctClaim setup.source.crypto codec)
    ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity) runtime
  rw [PqxdhDeploymentIdealHandoff.ideal_world setup codec route checks phase1 phase2 ensureInit bounds mode adversary
    budget respects (ctGapNamed setup codec budget) (ctClaim setup.source.crypto codec)
    ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity) runtime] at chain
  exact chain

end Split

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.peersKept_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.peersKept_trans

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.peerStep_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.peerStep_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.putPeer_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.putPeer_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.serverStep_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.serverStep_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.native_peers_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.native_peers_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.run_peers_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.run_peers_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.buildKeyId_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.buildKeyId_mem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.mem_buildKeyId' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.mem_buildKeyId

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.native_build_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.native_build_fresh

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.keyId_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.keyId_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.keyId_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.keyId_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.link_of_distinct' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.link_of_distinct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.build_keyId_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.build_keyId_link

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.linkedGap_of_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.linkedGap_of_gap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.linkedGap_designated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.linkedGap_designated

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.ctgap_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.ctgap_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.ctgap_split_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.ctgap_split_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.ctgap_term_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctEvent.ctgap_term_world
