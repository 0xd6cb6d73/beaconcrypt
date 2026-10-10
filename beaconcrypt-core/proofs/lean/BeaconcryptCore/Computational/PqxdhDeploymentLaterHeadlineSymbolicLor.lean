-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolic
import BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineLor
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolicLor

/-!
# `symbolic_lor` for the later-quantum game (CE-12 P3, design.md section 9.1, design-v2 sections 7.5 and 10)

The symbolic left-or-right corollary of CE-LOR-L with the public NoBundleFailure filter: CE-12 P2's `symbolic_lor` (`PqxdhDeploymentHeadlineSymbolicLor`) carried to the LQ-F game (`PqxdhDeploymentLaterServerGame.game`), with the symbolic eligibility read on the classical projection of the LQ-F outcome (`PqxdhDeploymentLaterHeadlineSymbolic.asClassical`: the Server's public data, the post adversary's output, the run-phase ledger and the final deployment state) and the guess read from the post adversary's output.

- Related outcomes (`Kin`): the same constructed Server (or none), the same ledger and deployment states that differ at most in the caches. Every event of the corollary holds on related outcomes alike, whatever their outputs (`kin_lorEligSym`, `kin_lorEligPeerSym`, `kin_serverGap`, `kin_beaconGap`, `kin_identity`, `kin_identity_decide`, `kin_happens`, `kin_ctColl`; `caches_refl`, `kin_run`).
- The support transfer (`support_later`): every outcome of the LQ-F game is related, through its classical projection, to an outcome of the classical common deployment experiment of the run-phase adversary `first` (`PqxdhDeploymentLaterServerGame.game_frame`, `runPhase_classical`). With it, CE-12 P2's support facts hold on the LQ-F game: the inclusion `e_CE ∧ NBF ⊆ e_sym ∧ NBF` (`lor_inclusion_later`) and the differences (`lor_difference_later`: a Server-side or Beacon-side gap, an identity collision or a ciphertext collision; `lor_difference_peer_later`: a Server-side gap or an identity collision).
- The run-phase transfer of the difference terms (`collisions_later`, `identity_later`, with `PqxdhDeploymentLaterHeadlineSymbolic.gaps_later` and `serverGap_later`): each has its probability on the classical experiment of `first` (`game_classical_event`).
- `symbolic_lor_later_le`, `lor_difference_later_bound`, `symbolic_lor_later` (`|adv_sym − adv_CE| ≤ ½(ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ctCollTerm)` of `first`) and `symbolic_lor_later_bound` (with CE-LOR-L's bound at `nbfFilter`); the Server-side forms `symbolic_lor_server_later_le`, `lor_difference_server_later_bound`, `symbolic_lor_server_later` (`½(ε_A2pub + ε_inj)`) and `symbolic_lor_server_later_bound` (with `ce_lor_server_later`'s bound, no `β_g`).

Every symbolic term is a run-phase classical term of `first`: CE-A2pub, CE-A1, the ciphertext gap, the identity collision and the ciphertext collision are never cited on the later compiled program. Explicit terms: `ctGapTerm` (F-ct2) and `ctCollTerm` (CE-12 P2's explicit ciphertext-collision term; its closed form `ε_ctcoll` is CE-12 P2b's `ct_collision_game`, not on central). No new assumption or contract; the premises are those of CE-LOR-L and of CE-12 P2's `symbolic_lor` at `first`. Later mode claims confidentiality only: no origin, binding or authentication statement.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec PostBudget Caches)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineGap (serverGap beaconGap ServerGap BeaconGap a2pubTerm a1Term ctGapTerm
  chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (IdentityCollision ctCollEvent ctCollTerm injTerm)
open PqxdhDeploymentHeadlineEvents (LorElig PeerTests lorEligEvent lorWinEvent lorEligPeerEvent lorWinPeerEvent
  lorClaim)
open PqxdhDeploymentHeadlineSymbolicLor (LorEligSym LorWinSym lorEligSym lorWinSym LorEligPeerSym LorWinPeerSym
  lorEligPeerSym lorWinPeerSym nbfFilter)
open PqxdhDeploymentLaterHeadlineSymbolic (asClassical runOutcome classical_later)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-! ### Related outcomes -/

section Kin

/-- Two classical-shaped outcome values are related (`Kin`) when both have no constructed Server, or both have the same constructed Server and the same ledger and deployment states that differ at most in the caches (`PqxdhDeploymentLater.Caches`, the first state the earlier one); their outputs are arbitrary. -/
def Kin {Y Z : Type}
    (first : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK))
    (second : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Z × PqxdhDeploymentSecrecy.State KemSK)) :
    Prop :=
  (first = none ∧ second = none) ∨ ∃ created y z ledger native native', first = some (created, y, (ledger, native)) ∧
    second = some (created, z, (ledger, native')) ∧ Caches native native'

/-- Every deployment state differs from itself at most in the caches. -/
theorem caches_refl (state : PqxdhDeploymentNative.State KemSK) : Caches state state := rfl

/-- `LorEligSym` holds on related outcomes alike: it reads the constructed Server, the ledger and the owners' identity keys, which the caches do not hold. -/
theorem kin_lorEligSym {Y Z B C : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (first : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B)
    (second : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Z × PqxdhDeploymentSecrecy.State KemSK) × C)
    (kin : Kin first.1 second.1) : LorEligSym setup codec first ↔ LorEligSym setup codec second := by
  rcases kin with ⟨none₁, none₂⟩ | ⟨created, y, z, ledger, native, native', found₁, found₂, caches⟩
  · constructor
    · rintro ⟨_, _, _, found, _⟩
      rw [none₁] at found
      cases found
    · rintro ⟨_, _, _, found, _⟩
      rw [none₂] at found
      cases found
  · unfold Caches at caches
    constructor
    · rintro ⟨createdFound, output, final, found, rest⟩
      rw [found₁, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      refine ⟨created, z, (ledger, native'), found₂, ?_⟩
      rw [caches]
      exact rest
    · rintro ⟨createdFound, output, final, found, rest⟩
      rw [found₂, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      refine ⟨created, y, (ledger, native), found₁, ?_⟩
      rw [caches] at rest
      exact rest

/-- `LorEligPeerSym` holds on related outcomes alike (`kin_lorEligSym`; `PeerTests` reads only the transcript). -/
theorem kin_lorEligPeerSym {Y Z B C : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (first : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B)
    (second : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Z × PqxdhDeploymentSecrecy.State KemSK) × C)
    (kin : Kin first.1 second.1) : LorEligPeerSym setup codec first ↔ LorEligPeerSym setup codec second := by
  have elig := kin_lorEligSym setup codec first second kin
  rcases kin with ⟨none₁, none₂⟩ | ⟨created, y, z, ledger, native, native', found₁, found₂, caches⟩
  · constructor
    · rintro ⟨_, _, _, _, found, _⟩
      rw [none₁] at found
      cases found
    · rintro ⟨_, _, _, _, found, _⟩
      rw [none₂] at found
      cases found
  · unfold Caches at caches
    constructor
    · rintro ⟨symbolic, createdFound, output, final, found, peers⟩
      rw [found₁, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      exact ⟨elig.mp symbolic, created, z, (ledger, native'), found₂, peers⟩
    · rintro ⟨symbolic, createdFound, output, final, found, peers⟩
      rw [found₂, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      exact ⟨elig.mpr symbolic, created, y, (ledger, native), found₁, peers⟩

/-- The Server-side gap holds on related outcomes alike. -/
theorem kin_serverGap {Y Z B C : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (first : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B)
    (second : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Z × PqxdhDeploymentSecrecy.State KemSK) × C)
    (kin : Kin first.1 second.1) : ServerGap setup codec budget first ↔ ServerGap setup codec budget second := by
  rcases kin with ⟨none₁, none₂⟩ | ⟨created, y, z, ledger, native, native', found₁, found₂, caches⟩
  · constructor
    · rintro ⟨_, _, _, found, _⟩
      rw [none₁] at found
      cases found
    · rintro ⟨_, _, _, found, _⟩
      rw [none₂] at found
      cases found
  · unfold Caches at caches
    constructor
    · rintro ⟨createdFound, output, final, found, rest⟩
      rw [found₁, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      refine ⟨created, z, (ledger, native'), found₂, ?_⟩
      rw [caches]
      exact rest
    · rintro ⟨createdFound, output, final, found, rest⟩
      rw [found₂, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      refine ⟨created, y, (ledger, native), found₁, ?_⟩
      rw [caches] at rest
      exact rest

/-- The Beacon-side gap holds on related outcomes alike. -/
theorem kin_beaconGap {Y Z B C : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (first : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B)
    (second : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Z × PqxdhDeploymentSecrecy.State KemSK) × C)
    (kin : Kin first.1 second.1) : BeaconGap setup codec budget first ↔ BeaconGap setup codec budget second := by
  rcases kin with ⟨none₁, none₂⟩ | ⟨created, y, z, ledger, native, native', found₁, found₂, caches⟩
  · constructor
    · rintro ⟨_, _, _, found, _⟩
      rw [none₁] at found
      cases found
    · rintro ⟨_, _, _, found, _⟩
      rw [none₂] at found
      cases found
  · constructor
    · rintro ⟨createdFound, output, final, found, rest⟩
      rw [found₁, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      exact ⟨created, z, (ledger, native'), found₂, rest⟩
    · rintro ⟨createdFound, output, final, found, rest⟩
      rw [found₂, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      exact ⟨created, y, (ledger, native), found₁, rest⟩

/-- An identity collision holds on related outcomes alike: it reads only the owners' identity seeds. -/
theorem kin_identity {Y Z B C : Type} (setup : Setup baseSpec KemSK)
    (first : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B)
    (second : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Z × PqxdhDeploymentSecrecy.State KemSK) × C)
    (kin : Kin first.1 second.1) : IdentityCollision setup first ↔ IdentityCollision setup second := by
  rcases kin with ⟨none₁, none₂⟩ | ⟨created, y, z, ledger, native, native', found₁, found₂, caches⟩
  · constructor
    · rintro ⟨_, _, _, found, _⟩
      rw [none₁] at found
      cases found
    · rintro ⟨_, _, _, found, _⟩
      rw [none₂] at found
      cases found
  · unfold Caches at caches
    constructor
    · rintro ⟨createdFound, output, final, found, rest⟩
      rw [found₁, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      refine ⟨created, z, (ledger, native'), found₂, ?_⟩
      rw [caches]
      exact rest
    · rintro ⟨createdFound, output, final, found, rest⟩
      rw [found₂, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      refine ⟨created, y, (ledger, native), found₁, ?_⟩
      rw [caches] at rest
      exact rest

open Classical in
/-- The CE-LOR eligibility event (any public filter) and the Server-side eligibility event hold on related outcomes alike: they read only the ledger of the observation. -/
theorem kin_happens {Y Z B C : Type} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Aeneas.Std.U64) (budget : Budget) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (first : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B)
    (second : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Z × PqxdhDeploymentSecrecy.State KemSK) × C)
    (kin : Kin first.1 second.1) :
    PqxdhDeploymentKemTransfer.happens (lorEligEvent crypto codec serverKid budget filter) first =
        PqxdhDeploymentKemTransfer.happens (lorEligEvent crypto codec serverKid budget filter) second ∧
      PqxdhDeploymentKemTransfer.happens (lorEligPeerEvent crypto codec serverKid budget filter) first =
        PqxdhDeploymentKemTransfer.happens (lorEligPeerEvent crypto codec serverKid budget filter) second := by
  rcases first with ⟨firstValue, firstAfter⟩
  rcases second with ⟨secondValue, secondAfter⟩
  rcases kin with ⟨none₁, none₂⟩ | ⟨created, y, z, ledger, native, native', found₁, found₂, caches⟩
  · simp only at none₁ none₂
    subst none₁ none₂
    exact ⟨rfl, rfl⟩
  · simp only at found₁ found₂
    subst found₁ found₂
    refine ⟨?_, ?_⟩
    · simp only [PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentKemTransfer.observeGame, Option.map_some,
        Option.any_some, lorEligEvent]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      exact Iff.rfl
    · simp only [PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentKemTransfer.observeGame, Option.map_some,
        Option.any_some, lorEligPeerEvent]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      exact Iff.rfl

open Classical in
/-- The ciphertext-collision event holds on related outcomes alike: it reads only the transcript. -/
theorem kin_ctColl {Y Z B C : Type} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (first : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B)
    (second : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Z × PqxdhDeploymentSecrecy.State KemSK) × C)
    (kin : Kin first.1 second.1) :
    PqxdhDeploymentKemTransfer.happens (ctCollEvent crypto codec) first =
      PqxdhDeploymentKemTransfer.happens (ctCollEvent crypto codec) second := by
  rcases first with ⟨firstValue, firstAfter⟩
  rcases second with ⟨secondValue, secondAfter⟩
  rcases kin with ⟨none₁, none₂⟩ | ⟨created, y, z, ledger, native, native', found₁, found₂, caches⟩
  · simp only at none₁ none₂
    subst none₁ none₂
    rfl
  · simp only at found₁ found₂
    subst found₁ found₂
    simp only [PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentKemTransfer.observeGame, Option.map_some,
      Option.any_some, ctCollEvent]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    exact Iff.rfl

/-- `decide` of an identity collision is the same on related outcomes. -/
theorem kin_identity_decide {Y Z B C : Type} (setup : Setup baseSpec KemSK)
    (first : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B)
    (second : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Z × PqxdhDeploymentSecrecy.State KemSK) × C)
    (kin : Kin first.1 second.1) :
    @decide (IdentityCollision setup first) (Classical.propDecidable _) =
      @decide (IdentityCollision setup second) (Classical.propDecidable _) :=
  decide_eq_decide.mpr (kin_identity setup first second kin)

/-- The support transfer: every outcome of the LQ-F game is related, through its classical projection, to an outcome of the classical common deployment experiment of the run-phase adversary `first`: the same constructed Server (or none), the same run-phase ledger, and a run-phase deployment state from which the final one differs at most in the caches (`PqxdhDeploymentLaterServerGame.game_frame`, `runPhase_classical`). -/
theorem support_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode
      first second).run runtime)) :
    ∃ classical ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode first).run
        runtime), Kin classical.1 (asClassical outcome).1 := by
  rw [← PqxdhDeploymentLaterServerGame.runPhase_classical setup codec checks route ensureInit 0 bounds mode first
    runtime]
  simp only [PqxdhDeploymentLaterServerGame.game, StateT.run, mem_support_bind_iff] at member
  obtain ⟨born, bornMember, rest⟩ := member
  rcases hborn : born.1 with _ | created
  · rw [hborn] at rest
    simp only [support_pure, Set.mem_singleton_iff] at rest
    subst rest
    refine ⟨(none, born.2), ?_, Or.inl ⟨rfl, rfl⟩⟩
    rw [support_map]
    refine ⟨(none, born.2), ?_, rfl⟩
    simp only [PqxdhDeploymentLaterServerGame.runPhase, StateT.run, mem_support_bind_iff]
    refine ⟨born, bornMember, ?_⟩
    rw [hborn]
    simp
  · rw [hborn] at rest
    simp only [support_map, Set.mem_image] at rest
    obtain ⟨result, resultMember, rfl⟩ := rest
    obtain ⟨run, runMember, ledgerSame, _, _, caches⟩ := PqxdhDeploymentLaterServerGame.game_frame setup codec checks
      route created.seed bounds mode first second (PqxdhDeploymentNative.initial created) result resultMember
    refine ⟨(some (PqxdhRegistrationJointServerBirth.encode created, run.1, (run.2.1, run.2.2.2.1)), born.2), ?_,
      Or.inr ⟨PqxdhRegistrationJointServerBirth.encode created, run.1, result.1, run.2.1, run.2.2.2.1,
        result.2.2.2.1, rfl, ?_, caches⟩⟩
    · rw [support_map]
      refine ⟨(some (PqxdhRegistrationJointServerBirth.encode created, run), born.2), ?_, rfl⟩
      simp only [PqxdhDeploymentLaterServerGame.runPhase, StateT.run, mem_support_bind_iff]
      refine ⟨born, bornMember, ?_⟩
      rw [hborn, support_map]
      exact ⟨run, runMember, rfl⟩
    · simp only [asClassical, Option.map_some, ledgerSame]

end Kin

/-! ### The support facts on the LQ-F game -/

section Support

/-- The inclusion `e_CE ∧ NBF ⊆ e_sym ∧ NBF` on every outcome of the LQ-F game (`PqxdhDeploymentHeadlineSymbolicLor.lor_inclusion` on a related outcome of the classical experiment of `first`, `support_later`, `kin_lorEligSym`). -/
theorem lor_inclusion_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (runtime : A) (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode
      first second).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : Out)
    (final : PqxdhDeploymentSecrecy.State KemSK) (found : (asClassical outcome).1 = some (created, output, final))
    (g : Fin budget.accept × Fin budget.capacity)
    (eligible : LorElig setup.source.crypto codec setup.serverKeyId budget nbfFilter g (output, final.1, final.2.produced)) :
    LorEligSym setup codec (asClassical outcome) := by
  obtain ⟨classical, classicalMember, kin⟩ := support_later setup codec checks route ensureInit bounds mode first second
    runtime outcome member
  have related := kin
  rcases kin with ⟨_, none₂⟩ | ⟨created', x, z, ledger, native, native', found₁, found₂, _⟩
  · rw [none₂] at found
    cases found
  · rw [found₂, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl, rfl⟩ := found
    have symbolic := PqxdhDeploymentHeadlineSymbolicLor.lor_inclusion setup codec checks route ensureInit phase1 phase2
      bounds mode first budget runtime classical classicalMember _ x (ledger, native) found₁ g eligible
    exact (kin_lorEligSym setup codec classical (asClassical outcome) related).mp symbolic

/-- The difference `(e_sym ∧ NBF) ∖ e_CE` on every outcome of the LQ-F game: a Server-side or Beacon-side gap, an identity collision or a ciphertext collision, each read on the classical projection (`PqxdhDeploymentHeadlineSymbolicLor.lor_difference` on a related outcome of the classical experiment of `first`). -/
theorem lor_difference_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (runtime : A) (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode
      first second).run runtime))
    (holds : LorEligSym setup codec (asClassical outcome)) :
    PqxdhDeploymentKemTransfer.happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter)
        (asClassical outcome) = true ∨
      ServerGap setup codec budget (asClassical outcome) ∨ BeaconGap setup codec budget (asClassical outcome) ∨
      IdentityCollision setup (asClassical outcome) ∨
      PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto codec) (asClassical outcome) = true := by
  obtain ⟨classical, classicalMember, kin⟩ := support_later setup codec checks route ensureInit bounds mode first second
    runtime outcome member
  have symbolic := (kin_lorEligSym setup codec classical (asClassical outcome) kin).mpr holds
  have same := kin_happens setup.source.crypto codec setup.serverKeyId budget nbfFilter classical (asClassical outcome)
    kin
  rcases PqxdhDeploymentHeadlineSymbolicLor.lor_difference setup codec checks route ensureInit phase1 bounds mode first
    budget runtime classical classicalMember symbolic with elig | gap | gap | collision | coll
  · exact Or.inl (same.1 ▸ elig)
  · exact Or.inr (Or.inl ((kin_serverGap setup codec budget classical (asClassical outcome) kin).mp gap))
  · exact Or.inr (Or.inr (Or.inl ((kin_beaconGap setup codec budget classical (asClassical outcome) kin).mp gap)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ((kin_identity setup classical (asClassical outcome) kin).mp collision))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ((kin_ctColl setup.source.crypto codec classical (asClassical outcome)
      kin) ▸ coll))))

/-- The Server-side difference on every outcome of the LQ-F game: a Server-side gap or an identity collision, read on the classical projection (`PqxdhDeploymentHeadlineSymbolicLor.lor_difference_peer` on a related outcome). -/
theorem lor_difference_peer_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (runtime : A) (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode
      first second).run runtime))
    (holds : LorEligPeerSym setup codec (asClassical outcome)) :
    PqxdhDeploymentKemTransfer.happens (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter)
        (asClassical outcome) = true ∨
      ServerGap setup codec budget (asClassical outcome) ∨ IdentityCollision setup (asClassical outcome) := by
  obtain ⟨classical, classicalMember, kin⟩ := support_later setup codec checks route ensureInit bounds mode first second
    runtime outcome member
  have symbolic := (kin_lorEligPeerSym setup codec classical (asClassical outcome) kin).mpr holds
  have same := kin_happens setup.source.crypto codec setup.serverKeyId budget nbfFilter classical (asClassical outcome)
    kin
  rcases PqxdhDeploymentHeadlineSymbolicLor.lor_difference_peer setup codec checks route ensureInit phase1 bounds mode
    first budget runtime classical classicalMember symbolic with elig | gap | collision
  · exact Or.inl (same.2 ▸ elig)
  · exact Or.inr (Or.inl ((kin_serverGap setup codec budget classical (asClassical outcome) kin).mp gap))
  · exact Or.inr (Or.inr ((kin_identity setup classical (asClassical outcome) kin).mp collision))

/-- The relation of an outcome value to its run-phase projection with a unit output. -/
theorem kin_run {Y B : Type}
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y × PqxdhDeploymentSecrecy.State KemSK) × B) :
    Kin outcome.1 (runOutcome (outcome.1.map fun value => (value.1, value.2.2))).1 := by
  rcases outcome with ⟨_ | ⟨created, y, ledger, native⟩, after⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨created, y, (), ledger, native, native, rfl, rfl, caches_refl native⟩

open Classical in
/-- An identity collision or a ciphertext collision has the same probability on the classical projection of the LQ-F game as on the classical experiment of the run-phase adversary `first` (`PqxdhDeploymentLaterHeadlineSymbolic.classical_later`). -/
theorem collisions_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (runtime : A) :
    𝒟[(fun outcome => decide (IdentityCollision setup (asClassical outcome)) ||
        PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto codec) (asClassical outcome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} =
      𝒟[(fun outcome => decide (IdentityCollision setup outcome) ||
          PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto codec) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode first).run runtime] {true} := by
  have run : ∀ {Y B : Type} (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y ×
      PqxdhDeploymentSecrecy.State KemSK) × B),
      (decide (IdentityCollision setup outcome) ||
        PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto codec) outcome) =
      (decide (IdentityCollision setup (runOutcome (outcome.1.map fun value => (value.1, value.2.2)))) ||
        PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto codec)
          (runOutcome (outcome.1.map fun value => (value.1, value.2.2)))) := by
    intro Y B outcome
    have kin := kin_run outcome
    rw [kin_identity_decide setup outcome _ kin, kin_ctColl setup.source.crypto codec outcome _ kin]
  have moved := classical_later setup codec checks route ensureInit bounds mode first second runtime
    (fun value => decide (IdentityCollision setup (runOutcome value)) ||
      PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto codec) (runOutcome value))
    (fun created ledger state result caches => by
      have kin : Kin (runOutcome (some (created, (ledger, state)))).1
          (runOutcome (some (created, (ledger, result)))).1 :=
        Or.inr ⟨created, (), (), ledger, state, result, rfl, rfl, caches⟩
      rw [kin_identity_decide setup _ _ kin, kin_ctColl setup.source.crypto codec _ _ kin])
  simp only [← run] at moved
  exact moved

open Classical in
/-- An identity collision has the same probability on the classical projection of the LQ-F game as on the classical experiment of the run-phase adversary `first`. -/
theorem identity_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (runtime : A) :
    𝒟[(fun outcome => decide (IdentityCollision setup (asClassical outcome))) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} =
      𝒟[(fun outcome => decide (IdentityCollision setup outcome)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode first).run runtime] {true} := by
  have run : ∀ {Y B : Type} (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Y ×
      PqxdhDeploymentSecrecy.State KemSK) × B),
      decide (IdentityCollision setup outcome) =
        decide (IdentityCollision setup (runOutcome (outcome.1.map fun value => (value.1, value.2.2)))) := by
    intro Y B outcome
    exact kin_identity_decide setup outcome _ (kin_run outcome)
  have moved := classical_later setup codec checks route ensureInit bounds mode first second runtime
    (fun value => decide (IdentityCollision setup (runOutcome value)))
    (fun created ledger state result caches => by
      have kin : Kin (runOutcome (some (created, (ledger, state)))).1
          (runOutcome (some (created, (ledger, result)))).1 :=
        Or.inr ⟨created, (), (), ledger, state, result, rfl, rfl, caches⟩
      exact (kin_identity_decide setup _ _ kin).symm)
  simp only [← run] at moved
  exact moved

end Support

/-! ### `symbolic_lor` on the LQ-F game -/

section Bound
open PqxdhDeploymentLaterHeadlineSymbolic (happens_asClassical gaps_later serverGap_later)
open PqxdhDeploymentHeadlineChain (slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentLaterHeadlineChain (kemLossL slotLossL recLossL)

/-- `symbolic_lor` in event form on the LQ-F game (mode P): the symbolic LOR advantage (eligibility `e_sym` read on the classical projection, the guess read from the post adversary's output) and CE-LOR-L's advantage with the NoBundleFailure filter differ by at most half the probability of the difference event `e_sym ∧ ¬e_CE`, because `e_CE ⊆ e_sym` on the support of the LQ-F game (`lor_inclusion_later`). Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem symbolic_lor_later_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds)
    (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (runtime : A) (guess : Out → Bool) :
    ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal) -
      ((𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal)| ≤
      2⁻¹ * 𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome) &&
          !PqxdhDeploymentLaterServerTransfer.happens
            (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true} := by
  classical
  set run := (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime
  set eCE := fun outcome => PqxdhDeploymentLaterServerTransfer.happens
    (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome
  set wCE := fun outcome => PqxdhDeploymentLaterServerTransfer.happens
    (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) outcome
  have unpackElig : ∀ outcome, eCE outcome = true → ∃ created output final,
      (asClassical outcome).1 = some (created, output, final) ∧
      ∃ g, LorElig setup.source.crypto codec setup.serverKeyId budget nbfFilter g (output, final.1, final.2.produced) := by
    intro outcome held
    simp only [eCE] at held
    rw [← happens_asClassical] at held
    simp only [PqxdhDeploymentKemTransfer.happens] at held
    rcases found : (asClassical outcome).1 with _ | ⟨created, output, final⟩
    · simp [PqxdhDeploymentKemTransfer.observeGame, found] at held
    · simp only [PqxdhDeploymentKemTransfer.observeGame, found, Option.map_some, Option.any_some, lorEligEvent,
        decide_eq_true_eq] at held
      exact ⟨created, output, final, rfl, held⟩
  have splitW := PqxdhDeploymentHeadlineLor.chance_split run
    (fun outcome => lorWinSym setup codec guess (asClassical outcome)) (fun outcome => eCE outcome = true)
  have splitE := PqxdhDeploymentHeadlineLor.chance_split run
    (fun outcome => lorEligSym setup codec (asClassical outcome)) (fun outcome => eCE outcome = true)
  have winSame : 𝒟[(fun outcome => decide (lorWinSym setup codec guess (asClassical outcome) = true ∧
      eCE outcome = true)) <$> run] {true} = 𝒟[wCE <$> run] {true} := by
    refine PqxdhDeploymentHeadlineSymbolicLor.chance_eq_support run _ _ fun outcome member => ?_
    simp only [decide_eq_true_eq, lorWinSym, wCE]
    constructor
    · rintro ⟨⟨_, created, output, final, found, bit⟩, elig⟩
      obtain ⟨created', output', final', found', g, eligible⟩ := unpackElig outcome elig
      rw [found] at found'
      simp only [Option.some.injEq, Prod.mk.injEq] at found'
      obtain ⟨rfl, rfl, rfl⟩ := found'
      rw [← happens_asClassical]
      simp only [PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentKemTransfer.observeGame, found, Option.map_some,
        Option.any_some, lorWinEvent, decide_eq_true_eq]
      exact ⟨g, eligible, bit⟩
    · intro won
      rw [← happens_asClassical] at won
      simp only [PqxdhDeploymentKemTransfer.happens] at won
      rcases found : (asClassical outcome).1 with _ | ⟨created, output, final⟩
      · simp [PqxdhDeploymentKemTransfer.observeGame, found] at won
      · simp only [PqxdhDeploymentKemTransfer.observeGame, found, Option.map_some, Option.any_some, lorWinEvent,
          decide_eq_true_eq] at won
        obtain ⟨g, eligible, bit⟩ := won
        refine ⟨⟨lor_inclusion_later setup codec checks route ensureInit phase1 phase2 bounds .P first second budget
          runtime outcome member created output final found g eligible, created, output, final, found, bit⟩, ?_⟩
        simp only [eCE]
        rw [← happens_asClassical]
        simp only [PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentKemTransfer.observeGame, found, Option.map_some,
          Option.any_some, lorEligEvent, decide_eq_true_eq]
        exact ⟨g, eligible⟩
  have eligSame : 𝒟[(fun outcome => decide (lorEligSym setup codec (asClassical outcome) = true ∧
      eCE outcome = true)) <$> run] {true} = 𝒟[eCE <$> run] {true} := by
    refine PqxdhDeploymentHeadlineSymbolicLor.chance_eq_support run _ _ fun outcome member => ?_
    simp only [decide_eq_true_eq]
    constructor
    · exact fun held => held.2
    · intro elig
      refine ⟨?_, elig⟩
      obtain ⟨created, output, final, found, g, eligible⟩ := unpackElig outcome elig
      simp only [lorEligSym, decide_eq_true_eq]
      exact lor_inclusion_later setup codec checks route ensureInit phase1 phase2 bounds .P first second budget runtime
        outcome member created output final found g eligible
  have dBelow : 𝒟[(fun outcome => decide (lorWinSym setup codec guess (asClassical outcome) = true ∧
      ¬eCE outcome = true)) <$> run] {true} ≤
      𝒟[(fun outcome => decide (lorEligSym setup codec (asClassical outcome) = true ∧ ¬eCE outcome = true)) <$> run]
        {true} := by
    refine chance_le_support run _ _ fun outcome _ held => ?_
    simp only [decide_eq_true_eq, lorWinSym, lorEligSym] at held ⊢
    exact ⟨held.1.1, held.2⟩
  have dSame : 𝒟[(fun outcome => decide (lorEligSym setup codec (asClassical outcome) = true ∧
      ¬eCE outcome = true)) <$> run] {true} =
      𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome) && !eCE outcome) <$> run] {true} := by
    refine PqxdhDeploymentHeadlineSymbolicLor.chance_eq_support run _ _ fun outcome _ => ?_
    simp
  have finite : ∀ f : _ → Bool, 𝒟[f <$> run] {true} ≠ ⊤ := fun f => UniformTargetSelection.chance_ne_top run f
  rw [winSame] at splitW
  rw [eligSame] at splitE
  have core := PqxdhDeploymentHeadlineSymbolicLor.nested_arith _ _ _ _ _ _
    (congrArg ENNReal.toReal splitW |>.trans (ENNReal.toReal_add (finite _) (finite _)))
    (congrArg ENNReal.toReal splitE |>.trans (ENNReal.toReal_add (finite _) (finite _)))
    ENNReal.toReal_nonneg (ENNReal.toReal_mono (finite _) dBelow)
  refine (ENNReal.ofReal_le_ofReal core).trans ?_
  rw [PqxdhDeploymentHeadlineLor.ofReal_half, ENNReal.ofReal_toReal (finite _), dSame]

/-- The difference event of `symbolic_lor_later` is bounded by `ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ctCollTerm`, each a run-phase classical term of `first` (`lor_difference_later`; the gap, identity-collision and ciphertext-collision events are carried to the classical experiment of `first` by `gaps_later` and `collisions_later`, then `sym_gap` and `identity_collision_game`). -/
theorem lor_difference_later_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome) &&
          !PqxdhDeploymentLaterServerTransfer.happens
            (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true} ≤
      a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback ordinaryFallback +
      ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
      ctGapTerm setup codec checks route ensureInit bounds .P first runtime +
      injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P first runtime := by
  classical
  refine (chance_le_add_support _ _
    (fun outcome => serverGap setup codec budget (asClassical outcome) ||
      beaconGap setup codec budget (asClassical outcome))
    (fun outcome => @decide (IdentityCollision setup (asClassical outcome)) (Classical.propDecidable _) ||
      PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto codec) (asClassical outcome))
    fun outcome member held => ?_).trans ?_
  · simp only [Bool.and_eq_true, Bool.not_eq_true', lorEligSym, decide_eq_true_eq] at held
    rcases lor_difference_later setup codec checks route ensureInit phase1 bounds .P first second budget runtime outcome
      member held.1 with elig | gap | gap | collision | coll
    · rw [happens_asClassical, held.2] at elig
      cases elig
    · left
      simp [serverGap, gap]
    · left
      simp [beaconGap, gap]
    · right
      simp [collision]
    · right
      simp [coll]
  · rw [gaps_later setup codec checks route ensureInit bounds .P first second budget runtime,
      collisions_later setup codec checks route ensureInit bounds .P first second runtime]
    have rest : 𝒟[(fun outcome => @decide (IdentityCollision setup outcome) (Classical.propDecidable _) ||
          PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto codec) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P first).run runtime] {true} ≤
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P first runtime := by
      refine (chance_le_add_support _ _ (fun outcome => @decide (IdentityCollision setup outcome)
        (Classical.propDecidable _)) (fun outcome => PqxdhDeploymentKemTransfer.happens (ctCollEvent
          setup.source.crypto codec) outcome) fun outcome _ held => by simpa using held).trans ?_
      exact add_le_add (PqxdhDeploymentHeadlineCollision.identity_collision_game setup codec checks route ensureInit
        phase1 phase2 bounds .P first budget respects runtime) le_rfl
    refine (add_le_add (PqxdhDeploymentHeadlineGap.sym_gap setup codec checks caps bounded shortRejects route ensureInit
      phase1 phase2 frameBack writable law spread correct adapter bounds .P first budget respects runtime
      identityFallback ordinaryFallback a1Fallback signatureFallback) rest).trans (le_of_eq ?_)
    ring

/-- `symbolic_lor` on the LQ-F game (mode P; the later forms of VC rows SSX-b2s, SS-b2s and 173 on symbolic eligibility): the symbolic LOR advantage of the LQ-F game (eligibility `e_sym` read on the classical projection, the guess read from the post adversary's output) differs from CE-LOR-L's advantage with the public NoBundleFailure filter by at most `½(ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ctCollTerm)`, each a run-phase classical term of `first`. Premises: those of CE-12 P2's `symbolic_lor` at `first`. -/
theorem symbolic_lor_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal) -
      ((𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P first runtime +
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P first runtime) :=
  (symbolic_lor_later_le setup codec checks route ensureInit phase1 phase2 bounds first second budget runtime
    guess).trans (mul_le_mul_right (lor_difference_later_bound setup codec checks caps bounded shortRejects route
      ensureInit phase1 phase2 frameBack writable law spread correct adapter bounds first second budget respects runtime
      identityFallback ordinaryFallback a1Fallback signatureFallback) _)

/-- `symbolic_lor_later` with CE-LOR-L's bound (`PqxdhDeploymentLaterHeadlineLor.ce_lor_later` at the NoBundleFailure filter): the symbolic LOR advantage of the LQ-F game is at most CE-LOR-L's bound plus `½(ε_A2pub + ε_A1 + ctGapTerm + ε_inj + ctCollTerm)` of `first`. Premises: those of `ce_lor_later` and of `symbolic_lor_later`. -/
theorem symbolic_lor_later_bound (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal |((𝒟[(fun outcome => lorWinSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
            post (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget post (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
              fallback caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P first budget (g.1, g.2.castSucc) runtime)) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        ENNReal.ofReal (a1Term setup codec checks caps route bounds .P first budget a1Fallback signatureFallback) +
        ctGapTerm setup codec checks route ensureInit bounds .P first runtime +
        injTerm setup budget + ctCollTerm setup codec checks route ensureInit bounds .P first runtime) := by
  have ce := PqxdhDeploymentLaterHeadlineLor.ce_lor_later (Reader := Reader) setup functional codec checks route
    ensureInit phase1 phase2 correct caps bounded qInit initBound bounds first second budget respects post postRespects
    runtime fallback guess nbfFilter
  have sym := symbolic_lor_later setup codec checks caps bounded shortRejects route ensureInit phase1 phase2 frameBack
    writable law spread correct adapter bounds first second budget respects runtime guess identityFallback
    ordinaryFallback a1Fallback signatureFallback
  exact PqxdhDeploymentHeadlineSymbolicLor.ofReal_abs_triangle _ _ _ _ sym ce

/-- `symbolic_lor_server` in event form on the LQ-F game: the Server-side symbolic LOR advantage (eligibility `LorEligPeerSym` on the classical projection, the guess read from the post adversary's output) and the Server-side CE-LOR-L advantage with the NoBundleFailure filter differ by at most half the probability of the Server-side difference event (`lor_inclusion_later` with the same `PeerTests`). Premises: the approved Phase 1 and Phase 2 read-back contracts. -/
theorem symbolic_lor_server_later_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds)
    (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (runtime : A) (guess : Out → Bool) :
    ENNReal.ofReal |((𝒟[(fun outcome => lorWinPeerSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligPeerSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal) -
      ((𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal)| ≤
      2⁻¹ * 𝒟[(fun outcome => lorEligPeerSym setup codec (asClassical outcome) &&
          !PqxdhDeploymentLaterServerTransfer.happens
            (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true} := by
  classical
  set run := (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime
  set eCE := fun outcome => PqxdhDeploymentLaterServerTransfer.happens
    (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome
  set wCE := fun outcome => PqxdhDeploymentLaterServerTransfer.happens
    (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) outcome
  have unpackElig : ∀ outcome, eCE outcome = true → ∃ created output final,
      (asClassical outcome).1 = some (created, output, final) ∧
      (∃ g, LorElig setup.source.crypto codec setup.serverKeyId budget nbfFilter g (output, final.1, final.2.produced)) ∧
      PeerTests setup.source.crypto codec setup.serverKeyId (output, final.1, final.2.produced) := by
    intro outcome held
    simp only [eCE] at held
    rw [← happens_asClassical] at held
    simp only [PqxdhDeploymentKemTransfer.happens] at held
    rcases found : (asClassical outcome).1 with _ | ⟨created, output, final⟩
    · simp [PqxdhDeploymentKemTransfer.observeGame, found] at held
    · simp only [PqxdhDeploymentKemTransfer.observeGame, found, Option.map_some, Option.any_some, lorEligPeerEvent,
        decide_eq_true_eq] at held
      exact ⟨created, output, final, rfl, held⟩
  have symOf : ∀ outcome ∈ support run, ∀ created output final,
      (asClassical outcome).1 = some (created, output, final) →
      (∃ g, LorElig setup.source.crypto codec setup.serverKeyId budget nbfFilter g (output, final.1, final.2.produced)) →
      PeerTests setup.source.crypto codec setup.serverKeyId (output, final.1, final.2.produced) →
      LorEligPeerSym setup codec (asClassical outcome) := by
    intro outcome member created output final found ⟨g, eligible⟩ peers
    exact ⟨lor_inclusion_later setup codec checks route ensureInit phase1 phase2 bounds .P first second budget runtime
      outcome member created output final found g eligible, created, output, final, found, peers⟩
  have splitW := PqxdhDeploymentHeadlineLor.chance_split run
    (fun outcome => lorWinPeerSym setup codec guess (asClassical outcome)) (fun outcome => eCE outcome = true)
  have splitE := PqxdhDeploymentHeadlineLor.chance_split run
    (fun outcome => lorEligPeerSym setup codec (asClassical outcome)) (fun outcome => eCE outcome = true)
  have winSame : 𝒟[(fun outcome => decide (lorWinPeerSym setup codec guess (asClassical outcome) = true ∧
      eCE outcome = true)) <$> run] {true} = 𝒟[wCE <$> run] {true} := by
    refine PqxdhDeploymentHeadlineSymbolicLor.chance_eq_support run _ _ fun outcome member => ?_
    simp only [decide_eq_true_eq, lorWinPeerSym, wCE]
    constructor
    · rintro ⟨⟨_, created, output, final, found, bit⟩, elig⟩
      obtain ⟨created', output', final', found', ⟨g, eligible⟩, peers⟩ := unpackElig outcome elig
      rw [found] at found'
      simp only [Option.some.injEq, Prod.mk.injEq] at found'
      obtain ⟨rfl, rfl, rfl⟩ := found'
      rw [← happens_asClassical]
      simp only [PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentKemTransfer.observeGame, found, Option.map_some,
        Option.any_some, lorWinPeerEvent, decide_eq_true_eq]
      exact ⟨⟨g, eligible, bit⟩, peers⟩
    · intro won
      rw [← happens_asClassical] at won
      simp only [PqxdhDeploymentKemTransfer.happens] at won
      rcases found : (asClassical outcome).1 with _ | ⟨created, output, final⟩
      · simp [PqxdhDeploymentKemTransfer.observeGame, found] at won
      · simp only [PqxdhDeploymentKemTransfer.observeGame, found, Option.map_some, Option.any_some, lorWinPeerEvent,
          decide_eq_true_eq] at won
        obtain ⟨⟨g, eligible, bit⟩, peers⟩ := won
        refine ⟨⟨symOf outcome member created output final found ⟨g, eligible⟩ peers, created, output, final, found,
          bit⟩, ?_⟩
        simp only [eCE]
        rw [← happens_asClassical]
        simp only [PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentKemTransfer.observeGame, found, Option.map_some,
          Option.any_some, lorEligPeerEvent, decide_eq_true_eq]
        exact ⟨⟨g, eligible⟩, peers⟩
  have eligSame : 𝒟[(fun outcome => decide (lorEligPeerSym setup codec (asClassical outcome) = true ∧
      eCE outcome = true)) <$> run] {true} = 𝒟[eCE <$> run] {true} := by
    refine PqxdhDeploymentHeadlineSymbolicLor.chance_eq_support run _ _ fun outcome member => ?_
    simp only [decide_eq_true_eq]
    constructor
    · exact fun held => held.2
    · intro elig
      refine ⟨?_, elig⟩
      obtain ⟨created, output, final, found, eligible, peers⟩ := unpackElig outcome elig
      simp only [lorEligPeerSym, decide_eq_true_eq]
      exact symOf outcome member created output final found eligible peers
  have dBelow : 𝒟[(fun outcome => decide (lorWinPeerSym setup codec guess (asClassical outcome) = true ∧
      ¬eCE outcome = true)) <$> run] {true} ≤
      𝒟[(fun outcome => decide (lorEligPeerSym setup codec (asClassical outcome) = true ∧ ¬eCE outcome = true)) <$>
        run] {true} := by
    refine chance_le_support run _ _ fun outcome _ held => ?_
    simp only [decide_eq_true_eq, lorWinPeerSym, lorEligPeerSym] at held ⊢
    exact ⟨held.1.1, held.2⟩
  have dSame : 𝒟[(fun outcome => decide (lorEligPeerSym setup codec (asClassical outcome) = true ∧
      ¬eCE outcome = true)) <$> run] {true} =
      𝒟[(fun outcome => lorEligPeerSym setup codec (asClassical outcome) && !eCE outcome) <$> run] {true} := by
    refine PqxdhDeploymentHeadlineSymbolicLor.chance_eq_support run _ _ fun outcome _ => ?_
    simp
  have finite : ∀ f : _ → Bool, 𝒟[f <$> run] {true} ≠ ⊤ := fun f => UniformTargetSelection.chance_ne_top run f
  rw [winSame] at splitW
  rw [eligSame] at splitE
  have core := PqxdhDeploymentHeadlineSymbolicLor.nested_arith _ _ _ _ _ _
    (congrArg ENNReal.toReal splitW |>.trans (ENNReal.toReal_add (finite _) (finite _)))
    (congrArg ENNReal.toReal splitE |>.trans (ENNReal.toReal_add (finite _) (finite _)))
    ENNReal.toReal_nonneg (ENNReal.toReal_mono (finite _) dBelow)
  refine (ENNReal.ofReal_le_ofReal core).trans ?_
  rw [PqxdhDeploymentHeadlineLor.ofReal_half, ENNReal.ofReal_toReal (finite _), dSame]

/-- The Server-side difference event of `symbolic_lor_server_later` is bounded by `ε_A2pub + ε_inj` of `first` (`lor_difference_peer_later`; `serverGap_later` and `identity_later`, then `server_gap_bound` and `identity_collision_game`); no `ε_A1`, `ctGapTerm` or `ctCollTerm`. -/
theorem lor_difference_server_later_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => lorEligPeerSym setup codec (asClassical outcome) &&
          !PqxdhDeploymentLaterServerTransfer.happens
            (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true} ≤
      a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback ordinaryFallback +
      injTerm setup budget := by
  classical
  refine (chance_le_add_support _ _ (fun outcome => serverGap setup codec budget (asClassical outcome))
    (fun outcome => @decide (IdentityCollision setup (asClassical outcome)) (Classical.propDecidable _))
    fun outcome member held => ?_).trans ?_
  · simp only [Bool.and_eq_true, Bool.not_eq_true', lorEligPeerSym, decide_eq_true_eq] at held
    rcases lor_difference_peer_later setup codec checks route ensureInit phase1 bounds .P first second budget runtime
      outcome member held.1 with elig | gap | collision
    · rw [happens_asClassical, held.2] at elig
      cases elig
    · left
      simp [serverGap, gap]
    · right
      simp [collision]
  · rw [serverGap_later setup codec checks route ensureInit bounds .P first second budget runtime,
      identity_later setup codec checks route ensureInit bounds .P first second runtime]
    exact add_le_add (PqxdhDeploymentHeadlineGap.server_gap_bound setup codec checks shortRejects route ensureInit
      phase1 phase2 bounds .P first budget respects runtime identityFallback ordinaryFallback)
      (PqxdhDeploymentHeadlineCollision.identity_collision_game setup codec checks route ensureInit phase1 phase2 bounds
        .P first budget respects runtime)

/-- `symbolic_lor_server` on the LQ-F game (mode P; the later forms of VC rows SSX-s2b, SS-s2b on Server-side symbolic eligibility): the Server-side symbolic LOR advantage differs from the Server-side CE-LOR-L advantage with the public NoBundleFailure filter by at most `½(ε_A2pub + ε_inj)` of `first`; no `ε_A1`, `ctGapTerm` or `ctCollTerm`. Premises: the approved Phase 1 and Phase 2 read-back contracts, `shortRejects` and the budget. -/
theorem symbolic_lor_server_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (runtime : A) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[(fun outcome => lorWinPeerSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligPeerSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal) -
      ((𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) outcome) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => PqxdhDeploymentLaterServerTransfer.happens
          (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) outcome) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal)| ≤
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        injTerm setup budget) :=
  (symbolic_lor_server_later_le setup codec checks route ensureInit phase1 phase2 bounds first second budget runtime
    guess).trans (mul_le_mul_right (lor_difference_server_later_bound setup codec checks shortRejects route ensureInit
      phase1 phase2 bounds first second budget respects runtime identityFallback ordinaryFallback) _)

/-- `symbolic_lor_server_later` with CE-LOR-L's Server-side bound (`PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later` at the NoBundleFailure filter, no `β_g`): the Server-side symbolic LOR advantage of the LQ-F game is at most `ce_lor_server_later`'s bound plus `½(ε_A2pub + ε_inj)` of `first`. Premises: those of `ce_lor_server_later` and of `symbolic_lor_server_later`. -/
theorem symbolic_lor_server_later_bound (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (bounds : FreshBounds) (first : OracleComp (ModeSpec .P) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (guess : Out → Bool)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    ENNReal.ofReal |((𝒟[(fun outcome => lorWinPeerSym setup codec guess (asClassical outcome)) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => lorEligPeerSym setup codec (asClassical outcome)) <$>
          (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds .P first second).run runtime] {true}).toReal)| ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
            (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second budget
            post (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
            fallback caps qInit (serverSlotted setup codec budget
              (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess nbfFilter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLossL setup codec checks route ensureInit bounds .P first second budget
              (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            ENNReal.ofReal (slotLossL (Reader := Reader) setup codec checks route ensureInit bounds .P first second
              budget post (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLossL setup codec checks route ensureInit bounds .P first second budget post (g.1, g.2.castSucc) runtime
              fallback caps qInit (serverSlotted setup codec budget
                (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget nbfFilter) lorClaim
                (g.1, g.2.castSucc))))) +
      2⁻¹ * (a2pubTerm setup codec checks route ensureInit bounds .P first budget runtime identityFallback
          ordinaryFallback +
        injTerm setup budget) := by
  have ce := PqxdhDeploymentLaterHeadlineLor.ce_lor_server_later (Reader := Reader) setup functional codec checks
    route ensureInit phase1 phase2 correct caps bounded qInit initBound bounds first second budget respects post
    postRespects runtime fallback guess nbfFilter
  have sym := symbolic_lor_server_later setup codec checks shortRejects route ensureInit phase1 phase2 bounds first
    second budget respects runtime guess identityFallback ordinaryFallback
  exact PqxdhDeploymentHeadlineSymbolicLor.ofReal_abs_triangle _ _ _ _ sym ce

end Bound

end BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.caches_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.caches_refl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_lorEligSym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_lorEligSym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_lorEligPeerSym' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_lorEligPeerSym

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_serverGap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_serverGap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_beaconGap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_beaconGap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_identity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_happens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_happens

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_ctColl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_ctColl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_identity_decide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_identity_decide

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.support_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.support_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.lor_inclusion_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.lor_inclusion_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.lor_difference_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.lor_difference_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.lor_difference_peer_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.lor_difference_peer_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.kin_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.collisions_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.collisions_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.identity_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.identity_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.lor_difference_later_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.lor_difference_later_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_later_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_server_later_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_server_later_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.lor_difference_server_later_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.lor_difference_server_later_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_server_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_server_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_server_later_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterHeadlineSymbolicLor.symbolic_lor_server_later_bound
