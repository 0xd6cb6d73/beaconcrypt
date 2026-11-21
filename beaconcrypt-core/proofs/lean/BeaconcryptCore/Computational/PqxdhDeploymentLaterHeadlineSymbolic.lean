-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineKeyTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineApp
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic

/-!
# Symbolic corollaries of the later-quantum CE-12 headlines (CE-12 P3, design.md section 9.1, design-v2 section 10)

The symbolic-eligibility corollaries of CE-APP-L and CE-KT-L: the later headline events with the public designation replaced by symbolic eligibility (`PqxdhDeploymentHeadlineGap.SymServer` for a Server peer under the final native identity keys, `SymBeacon` for an owner pinned to the constructed Server and the protected key ID), read on the LQ-F outcome through its classical projection `asClassical` (the Server's public data, the post adversary's output, the run-phase ledger and the final deployment state). The events are CE-12 P2's symbolic events (`PqxdhDeploymentHeadlineSymbolic.AppWinSym`, `AppWinPeerSym`, `AppWinOwnerSym`, `KtSym`, `KtPeerSym`, `KtOwnerSym`) at the post output type.

- The run-phase transfer (`classical_later`): an event of the Server's public data, the ledger and the deployment state that ignores the caches has the same probability at the end of the LQ-F game as at the end of the classical common deployment experiment of the run-phase adversary `first` (`PqxdhDeploymentLaterServerGame.game_classical_event`). The gap events (`ServerGap`, `BeaconGap`) read only the constructed Server, the run-phase transcript and the final owners' identity keys, which the post phase does not change (`serverGap_run`, `beaconGap_run`, `gapRun_caches`), so their probabilities on the LQ-F game are their probabilities on the classical experiment of `first` (`serverGap_later`, `beaconGap_later`, `gaps_later`).
- Containments on every LQ-F outcome, from CE-12 P2's pointwise containments on the projected outcome (`PqxdhDeploymentHeadlineSymbolic.app_sym`, `app_peer_sym`, `app_owner_sym`, `kt_sym`, `kt_peer_sym`, `kt_owner_sym`) with `happens_asClassical` and `eligible_asClassical`: `ce_app_later_sym_le`, `ce_app_server_later_sym_le`, `ce_app_beacon_later_sym_le`, `ce_kt_later_sym_le`, `ce_kt_server_later_sym_le`, `ce_kt_beacon_later_sym_le`.
- Corollaries with the bounds: `ce_app_later_sym` (CE-APP-L's bound + `ε_A2pub + ε_A1 + ctGapTerm`), `ce_app_server_later_sym` (CE-APP-L Server's bound + `ε_A2pub`), `ce_app_beacon_later_sym` (CE-APP-L's bound + `ε_A1 + ctGapTerm`), `ce_kt_later_sym` (CE-KT-L's one-sided summed bound + `ε_A2pub + ε_A1 + ctGapTerm`), `ce_kt_server_later_sym` (+ `ε_A2pub`), `ce_kt_beacon_later_sym` (+ `ε_A1 + ctGapTerm`). Every symbolic term is a run-phase classical term of `first` (`PqxdhDeploymentHeadlineGap.a2pubTerm`, `a1Term`, `ctGapTerm` at `first`): CE-A2pub, CE-A1 and the ciphertext gap are never cited on the later compiled program.

Explicit term: `ctGapTerm` is CE-12 P2's F-ct2 public ciphertext-gap term of the classical experiment of `first` (the D-ct spike's stop rule fired). No symbolic form of CE-LOR-L is stated here. No new assumption or contract; the premises are those of the later headlines, of `server_gap_bound` and of CE-A1. Later mode claims confidentiality only: no origin, binding or authentication statement.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_add_support)
open PqxdhDeploymentHeadlineSymbolic (appSym appPeerSym appOwnerSym ktSym ktPeerSym ktOwnerSym)
open PqxdhDeploymentHeadlineEvents (appEvent appPeerEvent appHandle)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-! ### The classical projection of an LQ-F outcome -/

section Projection

/-- The classical projection of an LQ-F outcome: the Server's public data, the post adversary's output, the run-phase ledger and the final deployment state (the ledger and the final state form the classical experiment's state `PqxdhDeploymentSecrecy.State`), with the runtime state. -/
def asClassical (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × PqxdhDeploymentSecrecy.State KemSK) × A :=
  (outcome.1.map fun result => (result.1, result.2.1, (result.2.2.1, result.2.2.2.2.1)), outcome.2)

/-- The classical event of the projection is the LQ-F event: both observe the post adversary's output, the run-phase ledger and the produced frames. -/
theorem happens_asClassical (event : Observed Out → Bool)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A) :
    PqxdhDeploymentKemTransfer.happens event (asClassical outcome) =
      PqxdhDeploymentLaterServerTransfer.happens event outcome := by
  rcases outcome with ⟨_ | result, after⟩ <;> rfl

/-- The classical plain eligibility of the projection is the LQ-F plain eligibility `eligibleL`. -/
theorem eligible_asClassical (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    (claim : Observed Out → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A) :
    PqxdhDeploymentTargetRange.eligible crypto codec serverKid claim (asClassical outcome) =
      PqxdhDeploymentLaterTargetRange.eligibleL crypto codec serverKid claim outcome := by
  rcases outcome with ⟨_ | result, after⟩ <;> rfl

/-- A run-phase projection (the Server's public data and the classical state) as a classical outcome with a unit output and a unit runtime state. -/
def runOutcome (run : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × PqxdhDeploymentSecrecy.State KemSK)) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Unit × PqxdhDeploymentSecrecy.State KemSK) × Unit :=
  (run.map fun value => (value.1, (), value.2), ())

open Classical in
/-- The Server-side gap on a constructed outcome: some Server peer with `SymServer` under the final owners' identity keys is not designated inside the budget. -/
theorem serverGap_some {Y B : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : Y)
    (final : PqxdhDeploymentSecrecy.State KemSK) (after : B) :
    serverGap setup codec budget (some (created, output, final), after) =
      decide (∃ keyId, PqxdhDeploymentHeadlineGap.SymServer setup.source.crypto codec final.1.transcript
          (PqxdhDeploymentPublishedTuple.ownerIdentities setup final.2.native) keyId ∧
        PqxdhDeploymentTranscript.designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript
          (.peer keyId) = none) := by
  rw [Bool.eq_iff_iff]
  simp only [serverGap, decide_eq_true_eq]
  unfold ServerGap
  constructor
  · rintro ⟨createdFound, outputFound, finalFound, found, rest⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl, rfl⟩ := found
    exact rest
  · intro rest
    exact ⟨created, output, final, rfl, rest⟩

open Classical in
/-- The Beacon-side gap on a constructed outcome: some owner with `SymBeacon` (pinned to the constructed Server and the protected key ID) is not designated inside the budget. -/
theorem beaconGap_some {Y B : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : Y)
    (final : PqxdhDeploymentSecrecy.State KemSK) (after : B) :
    beaconGap setup codec budget (some (created, output, final), after) =
      decide (∃ c, PqxdhDeploymentHeadlineGap.SymBeacon final.1.transcript
          (PqxdhDeploymentServerAuthEvent.protectedBinding setup created).1 setup.serverKeyId c ∧
        PqxdhDeploymentTranscript.designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript
          (.owner c) = none) := by
  rw [Bool.eq_iff_iff]
  simp only [beaconGap, decide_eq_true_eq]
  unfold BeaconGap
  constructor
  · rintro ⟨createdFound, outputFound, finalFound, found, rest⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl, rfl⟩ := found
    exact rest
  · intro rest
    exact ⟨created, output, final, rfl, rest⟩

/-- Neither gap holds when no Server was constructed. -/
theorem gaps_none {Y B : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (after : B) :
    serverGap setup codec budget
        ((none : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y ×
          PqxdhDeploymentSecrecy.State KemSK)), after) = false ∧
      beaconGap setup codec budget
        ((none : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y ×
          PqxdhDeploymentSecrecy.State KemSK)), after) = false := by
  constructor <;> simp [serverGap, ServerGap, beaconGap, BeaconGap]

/-- The Server-side gap reads an outcome only through its run-phase projection (the Server's public data and the classical state), not through the output or the runtime state. -/
theorem serverGap_run {Y B : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B) :
    serverGap setup codec budget outcome =
      serverGap setup codec budget (runOutcome (outcome.1.map fun value => (value.1, value.2.2))) := by
  rcases outcome with ⟨_ | ⟨created, output, final⟩, after⟩
  · simp only [Option.map_none, runOutcome]
    rw [(gaps_none setup codec budget after).1, (gaps_none setup codec budget ()).1]
  · simp only [Option.map_some, runOutcome]
    rw [serverGap_some, serverGap_some]

/-- The Beacon-side gap reads an outcome only through its run-phase projection. -/
theorem beaconGap_run {Y B : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B) :
    beaconGap setup codec budget outcome =
      beaconGap setup codec budget (runOutcome (outcome.1.map fun value => (value.1, value.2.2))) := by
  rcases outcome with ⟨_ | ⟨created, output, final⟩, after⟩
  · simp only [Option.map_none, runOutcome]
    rw [(gaps_none setup codec budget after).2, (gaps_none setup codec budget ()).2]
  · simp only [Option.map_some, runOutcome]
    rw [beaconGap_some, beaconGap_some]

/-- The gaps ignore the caches: two deployment states that differ at most in the Extract family, the BLAKE2b cache and the ghost touch list (`PqxdhDeploymentLater.Caches`) have the same owners' identity keys, so both gaps agree on them. -/
theorem gapRun_caches (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (ledger : PqxdhDeploymentSecrecy.Ledger)
    (state result : PqxdhDeploymentNative.State KemSK) (caches : PqxdhDeploymentLater.Caches state result) :
    serverGap setup codec budget (runOutcome (some (created, (ledger, result)))) =
        serverGap setup codec budget (runOutcome (some (created, (ledger, state)))) ∧
      beaconGap setup codec budget (runOutcome (some (created, (ledger, result)))) =
        beaconGap setup codec budget (runOutcome (some (created, (ledger, state)))) := by
  simp only [runOutcome, Option.map_some]
  rw [serverGap_some, serverGap_some, beaconGap_some, beaconGap_some]
  unfold PqxdhDeploymentLater.Caches at caches
  rw [caches]
  exact ⟨rfl, rfl⟩

/-- The run-phase transfer: an event of the Server's public data and the classical state that ignores the caches has the same probability on the classical projection of the LQ-F game as on the classical experiment of the run-phase adversary (`PqxdhDeploymentLaterServerGame.game_classical_event`). -/
theorem classical_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A)
    (event : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × PqxdhDeploymentSecrecy.State KemSK) → Bool)
    (invariant : ∀ created ledger state result, PqxdhDeploymentLater.Caches state result →
      event (some (created, (ledger, result))) = event (some (created, (ledger, state)))) :
    𝒟[(fun outcome => event ((asClassical outcome).1.map fun value => (value.1, value.2.2))) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} =
      𝒟[(fun outcome => event (outcome.1.map fun value => (value.1, value.2.2))) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode first).run runtime] {true} := by
  have moved := PqxdhDeploymentLaterServerGame.game_classical_event setup codec checks route ensureInit 0 bounds mode
    first second event invariant runtime
  have same : (fun outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A =>
      event ((asClassical outcome).1.map fun value => (value.1, value.2.2))) =
      fun outcome => event (outcome.1.map fun result => (result.1, (result.2.2.1, result.2.2.2.2.1))) := by
    funext outcome
    rcases outcome with ⟨_ | result, after⟩ <;> rfl
  rw [same, moved]

/-- The union of the gaps has the same probability on the classical projection of the LQ-F game as on the classical experiment of the run-phase adversary `first`. -/
theorem gaps_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (runtime : A) :
    𝒟[(fun outcome => serverGap setup codec budget (asClassical outcome) ||
        beaconGap setup codec budget (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} =
      𝒟[(fun outcome => serverGap setup codec budget outcome || beaconGap setup codec budget outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode first).run runtime] {true} := by
  have moved := classical_later setup codec checks route ensureInit bounds mode first second runtime
    (fun run => serverGap setup codec budget (runOutcome run) || beaconGap setup codec budget (runOutcome run))
    (fun created ledger state result caches => by
      rw [(gapRun_caches setup codec budget created ledger state result caches).1,
        (gapRun_caches setup codec budget created ledger state result caches).2])
  simp only [← serverGap_run, ← beaconGap_run] at moved
  exact moved

/-- The Server-side gap has the same probability on the classical projection of the LQ-F game as on the classical experiment of the run-phase adversary `first`. -/
theorem serverGap_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (runtime : A) :
    𝒟[(fun outcome => serverGap setup codec budget (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} =
      𝒟[serverGap setup codec budget <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode first).run runtime] {true} := by
  have moved := classical_later setup codec checks route ensureInit bounds mode first second runtime
    (fun run => serverGap setup codec budget (runOutcome run))
    (fun created ledger state result caches => (gapRun_caches setup codec budget created ledger state result caches).1)
  simp only [← serverGap_run] at moved
  exact moved

/-- The Beacon-side gap has the same probability on the classical projection of the LQ-F game as on the classical experiment of the run-phase adversary `first`. -/
theorem beaconGap_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (runtime : A) :
    𝒟[(fun outcome => beaconGap setup codec budget (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} =
      𝒟[beaconGap setup codec budget <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode first).run runtime] {true} := by
  have moved := classical_later setup codec checks route ensureInit bounds mode first second runtime
    (fun run => beaconGap setup codec budget (runOutcome run))
    (fun created ledger state result caches => (gapRun_caches setup codec budget created ledger state result caches).2)
  simp only [← beaconGap_run] at moved
  exact moved

end Projection

/-! ### Containments on the LQ-F game -/

section Containments

/-- The symbolic CE-APP-L win (any claimed handle) is at most the CE-APP-L win plus both gaps, on the LQ-F game (`PqxdhDeploymentHeadlineSymbolic.app_sym` on the classical projection). -/
theorem ce_app_later_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (runtime : A) (appClaim : Out → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun outcome => appSym setup codec appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} +
      𝒟[(fun outcome => serverGap setup codec budget (asClassical outcome) ||
          beaconGap setup codec budget (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome _ held => ?_
  simp only [appSym, decide_eq_true_eq] at held
  rcases PqxdhDeploymentHeadlineSymbolic.app_sym setup codec budget appClaim (asClassical outcome) held with
    ce | gap | gap
  · left
    rw [← happens_asClassical]
    exact ce
  · right
    simp [serverGap, gap]
  · right
    simp [beaconGap, gap]

/-- The symbolic CE-APP-L win on a Server peer is at most the Server-side CE-APP-L win plus the Server-side gap, on the LQ-F game (`app_peer_sym`). -/
theorem ce_app_server_later_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (runtime : A) (appClaim : Out → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun outcome => appPeerSym setup codec appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} +
      𝒟[(fun outcome => serverGap setup codec budget (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome _ held => ?_
  simp only [appPeerSym, decide_eq_true_eq] at held
  rcases PqxdhDeploymentHeadlineSymbolic.app_peer_sym setup codec budget appClaim (asClassical outcome) held with
    ce | gap
  · left
    rw [← happens_asClassical]
    exact ce
  · right
    simp [serverGap, gap]

/-- The symbolic CE-APP-L win on a Beacon owner is at most the CE-APP-L win plus the Beacon-side gap, on the LQ-F game (`app_owner_sym`). -/
theorem ce_app_beacon_later_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (runtime : A) (appClaim : Out → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun outcome => appOwnerSym setup appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} +
      𝒟[(fun outcome => beaconGap setup codec budget (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome _ held => ?_
  simp only [appOwnerSym, decide_eq_true_eq] at held
  rcases PqxdhDeploymentHeadlineSymbolic.app_owner_sym setup codec budget appClaim (asClassical outcome) held with
    ce | gap
  · left
    rw [← happens_asClassical]
    exact ce
  · right
    simp [beaconGap, gap]

/-- An LQ-F event whose claim names a symbolically eligible handle is at most the event with a designated claim (`eligibleL`) plus both gaps, on the LQ-F game (`kt_sym`). -/
theorem ce_kt_later_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (runtime : A) (event : Observed Out → Bool) (claim : Observed Out → Option Handle) :
    𝒟[(fun outcome => ktSym setup codec event claim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[(fun outcome => decide (PqxdhDeploymentLaterServerTransfer.happens event outcome = true ∧
          (PqxdhDeploymentLaterTargetRange.eligibleL setup.source.crypto codec setup.serverKeyId claim
            outcome).isSome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} +
      𝒟[(fun outcome => serverGap setup codec budget (asClassical outcome) ||
          beaconGap setup codec budget (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome _ held => ?_
  simp only [ktSym, decide_eq_true_eq] at held
  rcases PqxdhDeploymentHeadlineSymbolic.kt_sym setup codec budget event claim (asClassical outcome) held with
    ce | gap | gap
  · left
    rw [happens_asClassical, eligible_asClassical] at ce
    exact decide_eq_true ce
  · right
    simp [serverGap, gap]
  · right
    simp [beaconGap, gap]

/-- An LQ-F event whose claim names a Server peer with `SymServer` is at most the event with a designated claim plus the Server-side gap, on the LQ-F game (`kt_peer_sym`). -/
theorem ce_kt_server_later_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (runtime : A) (event : Observed Out → Bool) (claim : Observed Out → Option Handle) :
    𝒟[(fun outcome => ktPeerSym setup codec event claim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[(fun outcome => decide (PqxdhDeploymentLaterServerTransfer.happens event outcome = true ∧
          (PqxdhDeploymentLaterTargetRange.eligibleL setup.source.crypto codec setup.serverKeyId claim
            outcome).isSome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} +
      𝒟[(fun outcome => serverGap setup codec budget (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome _ held => ?_
  simp only [ktPeerSym, decide_eq_true_eq] at held
  rcases PqxdhDeploymentHeadlineSymbolic.kt_peer_sym setup codec budget event claim (asClassical outcome) held with
    ce | gap
  · left
    rw [happens_asClassical, eligible_asClassical] at ce
    exact decide_eq_true ce
  · right
    simp [serverGap, gap]

/-- An LQ-F event whose claim names an owner with `SymBeacon` is at most the event with a designated claim plus the Beacon-side gap, on the LQ-F game (`kt_owner_sym`). -/
theorem ce_kt_beacon_later_sym_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (runtime : A) (event : Observed Out → Bool) (claim : Observed Out → Option Handle) :
    𝒟[(fun outcome => ktOwnerSym setup event claim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      𝒟[(fun outcome => decide (PqxdhDeploymentLaterServerTransfer.happens event outcome = true ∧
          (PqxdhDeploymentLaterTargetRange.eligibleL setup.source.crypto codec setup.serverKeyId claim
            outcome).isSome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} +
      𝒟[(fun outcome => beaconGap setup codec budget (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome _ held => ?_
  simp only [ktOwnerSym, decide_eq_true_eq] at held
  rcases PqxdhDeploymentHeadlineSymbolic.kt_owner_sym setup codec budget event claim (asClassical outcome) held with
    ce | gap
  · left
    rw [happens_asClassical, eligible_asClassical] at ce
    exact decide_eq_true ce
  · right
    simp [beaconGap, gap]

end Containments

/-! ### The later symbolic corollaries -/

section Corollaries

/-- **CE-APP-L, symbolic eligibility** (any claimed handle, mode P): the probability that the LQ-F game ends with the post adversary's claimed fresh message, sent on a symbolically eligible handle, equal to its guess is at most CE-APP-L's bound (`PqxdhDeploymentLaterHeadlineApp.ce_app_later`) plus `ε_A2pub + ε_A1 + ctGapTerm` of the run-phase adversary `first` (CE-12 P2's `sym_gap` on the classical experiment of `first`, carried to the LQ-F game by `gaps_later`). Premises: those of `ce_app_later`, of `server_gap_bound` (`shortRejects`) and of CE-A1 (`FrameReadBack`, `ReadWritable`, `X25519ClassLaw`, `X25519ScalarSpread`, `HasAttachedVerificationAdapter`). -/
theorem ce_app_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => appSym setup codec appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
            post (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P first runtime) := by
  refine (ce_app_later_sym_le setup codec checks route ensureInit bounds .P first second budget runtime
    appClaim).trans (add_le_add (PqxdhDeploymentLaterHeadlineApp.ce_app_later setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound bounds first second budget respects post
      postRespects runtime fallback appClaim) ?_)
  rw [gaps_later setup codec checks route ensureInit bounds .P first second budget runtime]
  exact PqxdhDeploymentHeadlineGap.sym_gap setup codec checks caps bounded shortRejects route ensureInit phase1 phase2
    frameReadBack writable law spread correct adapter bounds .P first budget respects runtime identityFallback
    ordinaryFallback a1Fallback signatureFallback

/-- **CE-APP-L on a Server peer, symbolic eligibility** (mode P): the probability that the LQ-F game ends with the post adversary's claimed fresh message, sent on a Server peer with `SymServer`, equal to its guess is at most CE-APP-L Server's bound (`ce_app_server_later`) plus `ε_A2pub` of the run-phase adversary `first` (`server_gap_bound`, carried by `serverGap_later`). Premises: those of `ce_app_server_later` and `shortRejects`. -/
theorem ce_app_server_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => appPeerSym setup codec appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
            post (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (serverSlotted setup codec budget
              (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback ordinaryFallback := by
  refine (ce_app_server_later_sym_le setup codec checks route ensureInit bounds .P first second budget runtime
    appClaim).trans (add_le_add (PqxdhDeploymentLaterHeadlineApp.ce_app_server_later setup functional codec checks
      route ensureInit phase1 phase2 correct caps bounded qInit initBound bounds first second budget respects post
      postRespects runtime fallback appClaim) ?_)
  rw [serverGap_later setup codec checks route ensureInit bounds .P first second budget runtime]
  exact PqxdhDeploymentHeadlineGap.server_gap_bound setup codec checks shortRejects route ensureInit phase1 phase2
    bounds .P first budget respects runtime identityFallback ordinaryFallback

/-- **CE-APP-L on a Beacon owner, symbolic eligibility** (mode P): the probability that the LQ-F game ends with the post adversary's claimed fresh message, sent on an owner with `SymBeacon`, equal to its guess is at most CE-APP-L's bound (`ce_app_later`) plus `ε_A1 + ctGapTerm` of the run-phase adversary `first` (`ce_a1_linked`, carried by `beaconGap_later`); no `ε_A2pub`. Premises: those of `ce_app_later` and of CE-A1. -/
theorem ce_app_beacon_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (appClaim : Out → Option (Nat × Pqxdh.Bytes))
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => appOwnerSym setup appClaim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
            post (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
            (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim) (appHandle appClaim)
              (g.1, g.2.castSucc)) +
          ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹)) +
      (ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P first runtime) := by
  refine (ce_app_beacon_later_sym_le setup codec checks route ensureInit bounds .P first second budget runtime
    appClaim).trans (add_le_add (PqxdhDeploymentLaterHeadlineApp.ce_app_later setup functional codec checks route
      ensureInit phase1 phase2 correct caps bounded qInit initBound bounds first second budget respects post
      postRespects runtime fallback appClaim) ?_)
  rw [beaconGap_later setup codec checks route ensureInit bounds .P first second budget runtime]
  exact (PqxdhDeploymentHeadlineGap.ce_a1_linked setup codec checks caps bounded route ensureInit phase1 phase2
    frameReadBack writable law spread correct adapter bounds .P first budget respects runtime a1Fallback
    signatureFallback).1

/-- **CE-KT-L, symbolic eligibility** (any claimed handle): the probability that the LQ-F game ends with an event whose claim names a symbolically eligible handle is at most CE-KT-L's one-sided summed bound (`PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum_le`: the sum over the targets of the later ideal game's probability plus `kemLossL` and `slotLossL`) plus `ε_A2pub + ε_A1 + ctGapTerm` of the run-phase adversary `first`. Premises: those of `ce_kt_later_sum_le`, of `server_gap_bound` and of CE-A1 (CE-KT-L's own premises do not include `KemBound`, which CE-A1 needs). -/
theorem ce_kt_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (respects : budget.Respects first)
    (post : PostBudget) (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => ktSym setup codec event claim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime))) +
      (a2pubTerm setup codec checks route ensureInit bounds mode first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds mode first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds mode first runtime) := by
  refine (ce_kt_later_sym_le setup codec checks route ensureInit bounds mode first second budget runtime event
    claim).trans (add_le_add (PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum_le setup functional codec checks
      route ensureInit phase1 phase2 correct bounds mode first second budget respects post postRespects event claim
      runtime) ?_)
  rw [gaps_later setup codec checks route ensureInit bounds mode first second budget runtime]
  exact PqxdhDeploymentHeadlineGap.sym_gap setup codec checks caps bounded shortRejects route ensureInit phase1 phase2
    frameReadBack writable law spread correct adapter bounds mode first budget respects runtime identityFallback
    ordinaryFallback a1Fallback signatureFallback

/-- **CE-KT-L, Server-side symbolic eligibility**: the probability that the LQ-F game ends with an event whose claim names a Server peer with `SymServer` is at most CE-KT-L's one-sided summed bound plus `ε_A2pub` of the run-phase adversary `first`; no `ε_A1`, no `ctGapTerm`, no CE-A1 premise. Premises: those of `ce_kt_later_sum_le` and `shortRejects`. -/
theorem ce_kt_server_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (respects : budget.Respects first)
    (post : PostBudget) (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => ktPeerSym setup codec event claim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime))) +
      a2pubTerm setup codec checks route ensureInit bounds mode first budget runtime identityFallback
        ordinaryFallback := by
  refine (ce_kt_server_later_sym_le setup codec checks route ensureInit bounds mode first second budget runtime event
    claim).trans (add_le_add (PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum_le setup functional codec checks
      route ensureInit phase1 phase2 correct bounds mode first second budget respects post postRespects event claim
      runtime) ?_)
  rw [serverGap_later setup codec checks route ensureInit bounds mode first second budget runtime]
  exact PqxdhDeploymentHeadlineGap.server_gap_bound setup codec checks shortRejects route ensureInit phase1 phase2
    bounds mode first budget respects runtime identityFallback ordinaryFallback

/-- **CE-KT-L, Beacon-side symbolic eligibility**: the probability that the LQ-F game ends with an event whose claim names an owner with `SymBeacon` is at most CE-KT-L's one-sided summed bound plus `ε_A1 + ctGapTerm` of the run-phase adversary `first` (`ce_a1_linked`); no `ε_A2pub`. Premises: those of `ce_kt_later_sum_le` and of CE-A1 (`KemBound`, `FrameReadBack`, `ReadWritable`, `X25519ClassLaw`, `X25519ScalarSpread`, `HasAttachedVerificationAdapter`). -/
theorem ce_kt_beacon_later_sym (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget) (respects : budget.Respects first)
    (post : PostBudget) (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (runtime : A)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => ktOwnerSym setup event claim (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim (g.1, g.2.castSucc) <$>
            (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget (g.1, g.2.castSucc)
              ensureInit bounds mode first second).run runtime] {true} +
          ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds mode first second budget event claim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds mode first second
            budget post event claim (g.1, g.2.castSucc) runtime))) +
      (ENNReal.ofReal (a1Term setup codec checks caps route bounds mode first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds mode first runtime) := by
  refine (ce_kt_beacon_later_sym_le setup codec checks route ensureInit bounds mode first second budget runtime event
    claim).trans (add_le_add (PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum_le setup functional codec checks
      route ensureInit phase1 phase2 correct bounds mode first second budget respects post postRespects event claim
      runtime) ?_)
  rw [beaconGap_later setup codec checks route ensureInit bounds mode first second budget runtime]
  exact (PqxdhDeploymentHeadlineGap.ce_a1_linked setup codec checks caps bounded route ensureInit phase1 phase2
    frameReadBack writable law spread correct adapter bounds mode first budget respects runtime a1Fallback
    signatureFallback).1

end Corollaries

end BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.happens_asClassical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.happens_asClassical

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.eligible_asClassical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.eligible_asClassical

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.serverGap_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.serverGap_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.beaconGap_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.beaconGap_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.gaps_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.gaps_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.serverGap_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.serverGap_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.beaconGap_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.beaconGap_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.gapRun_caches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.gapRun_caches

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.classical_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.classical_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.gaps_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.gaps_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.serverGap_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.serverGap_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.beaconGap_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.beaconGap_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_server_later_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_server_later_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_later_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_later_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_server_later_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_server_later_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_beacon_later_sym_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_beacon_later_sym_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_server_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_server_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_app_beacon_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_server_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_server_later_sym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_beacon_later_sym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic.ce_kt_beacon_later_sym
