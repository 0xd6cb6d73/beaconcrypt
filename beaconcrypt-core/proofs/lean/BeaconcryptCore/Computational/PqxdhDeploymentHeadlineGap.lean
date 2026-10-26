-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame
import BeaconcryptCore.Computational.PqxdhDeploymentTargetRange
import BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch

/-!
# Symbolic eligibility and the gap lemmas (CE-12 P2, design-v2 section 7.1, F-ct2 form)

The symbolic-eligibility predicates of CE-12's symbolic corollaries and the two gap lemmas that relate them to the public designation `PqxdhDeploymentTranscript.designateIn`, on the common deployment experiment (`PqxdhDeploymentSecrecy.game`, Server identity index 0, generated seed, `supplied = none`).

- `SymServer transcript identities keyId` (ProVerif's `L2SelectedIdentity`): Server peer `keyId` was built by a session whose accept bytes give a candidate that the source attached verification accepts with the identity key of an owner `c` (among the final native identity keys `PqxdhDeploymentPublishedTuple.ownerIdentities`), and `c` made no rejected bundle call in Fresh. `SymBeacon transcript pin serverKid c` (ProVerif's `S2bSelectedIdentity` on `(S, serverKid)` pins): owner `c` is Established, was created with the binding `(pin, serverKid)` and made no rejected bundle call in Fresh; the headline forms use the constructed Server's identity (`protectedBinding`) and the protected key ID. Both read the outcome (final native identities, constructed Server), not a public view; they are never fed through the per-target chain.
- `CtGap c j`, `CtGapEvent`, `ctGapEvent` (design-v2 section 7.1, public): owner `c` accepted, session `j` matches it with its created pin before its acceptance (CE-A1's `PinnedMatchAt`), and the ciphertext read with the Phase 2 reader from `c`'s first successful finish input differs from the one read from `j`'s first successful build response.
- A new run invariant `FinishReady` (`ready_game`): every successful finish of the transcript happens while the running summary has its owner created and in InitSent, the native fact that `finish_registration` (`beacon.rs`) rejects outside `InitSent` (`PqxdhDeploymentCompileFootprint.finish_owner`), read through `PqxdhDeploymentEligibility.Agree`. Consequences: `finish_accepted` (the first successful finish of an owner is its accepting finish) and `ready_accepted` (the accepting finish comes after the owner's creation, with its final binding). Positional sessions (`accept_positional`, from `PqxdhDeploymentRegistrationTrace.Traced.positional` and `PqxdhDeploymentServerAuthInjectiveGame.session_unique`).
- `server_gap`: a `SymServer` peer that is not designated inside the budget witnesses CE-A2pub's `OwnerForgery` at the owner whose identity key the accepted candidate carries (that owner has no rejected bundle call in Fresh). `beacon_gap`: a `SymBeacon` owner that is not designated inside the budget is a CE-A1 failure (`A1NoPinnedMatch`) or has a `CtGap`. Both hold on every outcome of a budget-respecting adversary under `Phase1ReadBack` and `Phase2ReadBack`.
- Bounds: `server_gap_le`, `server_gap_bound` (`𝒟[ServerGap] ≤ ε_A2pub`, `a2pubTerm`, from `a2pub_owner_bound`), `beacon_gap_le` (`𝒟[BeaconGap] ≤ 𝒟[∃ c, A1NoPinnedMatch c] + ctGapTerm`), `ce_a1_linked` (`𝒟[BeaconGap] ≤ ε_A1 + ctGapTerm`, `a1Term` at the caps transported from the budget, with the bills of every CE-A1 reduction) and `sym_gap` (`𝒟[ServerGap ∨ BeaconGap] ≤ ε_A2pub + ε_A1 + ctGapTerm`).

F-ct2 (design-v2 section 8): `ctGapTerm`, the probability of the public event `CtGapEvent` in the experiment, stays an explicit term. The closed form with `ε_ct` needs `ctgap_world`, whose 0.5-day spike stopped (stop rule: remaining estimate above 1.5 days); the reasons are recorded in the CE-12 guide. This is weaker than plan section 9's Beacon-side corollary and is reported to the owner before publication. No new assumption or contract; the CE-A1 and CE-A2pub premises are those of `ce_a1_billed` and `a2pub_owner_bound`.
-/

open OracleComp OracleSpec ENNReal


set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens)
open PqxdhDeploymentTranscript (summarize phase linkOf acceptOf buildOf finishOf bundleOf candidateOf acceptedKeys
  publishedPq NoBundleFailureAt designate designateIn Publishes Linked acceptCount)
open PqxdhDeploymentServerAuthEvent (Reg regsOf regOfEntry summarizeReg stepReg accepted acceptedFrom publishedKeys
  keysOfBundle bundleOfReg protectedBinding)
open PqxdhDeploymentServerAuth (PinnedMatchAt PinnedMatch A1NoPinnedMatch)
open PqxdhDeploymentPublishedTuple (OwnerForgery OwnerEvent ownerIdentities publishedTuple candidateTuple)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### Definitions -/

section Definitions
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)

/-- `SymServer` (design-v2 section 7.1, design section 7.1): Server peer `keyId` was built by a session whose accept bytes give a candidate that verifies to the identity key of owner `c` among the given owner identity keys, and owner `c` made no rejected bundle call in Fresh. With the final native identity keys this is the symbolic eligibility of a Server peer (ProVerif's `L2SelectedIdentity`: the accepted identity is an honest Beacon's). -/
def SymServer (transcript : List Entry) (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) (keyId : Aeneas.Std.U64) :
    Prop :=
  ∃ session response raw candidate identity keys c, linkOf transcript keyId = some (session, response) ∧
    acceptOf transcript session = some raw ∧ candidateOf codec raw = some candidate ∧
    acceptedKeys crypto candidate = some (identity, keys) ∧ identities[c]? = some identity ∧
    NoBundleFailureAt transcript c

/-- `SymBeacon` (design-v2 section 7.1, design section 7.2): owner `c` is Established, was created with the binding `(pin, serverKid)` and made no rejected bundle call in Fresh. With the constructed Server's identity as `pin` and the protected key ID this is the symbolic eligibility of a Beacon (ProVerif's `S2bSelectedIdentity` on `(S, serverKid)` pins). -/
def SymBeacon (transcript : List Entry) (pin : PqxdhBeaconPhase2Preparation.Word32) (serverKid : Aeneas.Std.U64) (c : Nat) :
    Prop :=
  phase transcript c = .established ∧ (summarize transcript).owners[c]? = some (pin, serverKid) ∧
    NoBundleFailureAt transcript c

/-- The KEM ciphertext that the Phase 2 reader reads from optional bytes. -/
def ciphertextOf (bytes : Option Pqxdh.Bytes) : Option PqxdhBeaconPhase2Preparation.Ciphertext :=
  (bytes.bind codec.read2).bind codec.ciphertext

/-- `CtGap c j` (design-v2 section 7.1): owner `c` accepted, session `j` matches it before its acceptance with the pin of `c`'s created binding (CE-A1's `PinnedMatchAt`), and the ciphertext read from `c`'s first successful finish input differs from the ciphertext read from session `j`'s first successful build response. It reads public transcript bytes only. -/
def CtGap (transcript : List Entry) (c j : Nat) : Prop :=
  ∃ before raw binding, accepted c (regsOf transcript) = some (before, raw) ∧
    (summarize transcript).owners[c]? = some binding ∧ PinnedMatchAt crypto codec c j binding.1 before raw ∧
    ciphertextOf codec (finishOf transcript c) ≠ ciphertextOf codec ((buildOf transcript j).map (·.serialized))

/-- `CtGapEvent`: some owner has a pinned match whose ciphertext differs from its finish ciphertext. -/
def CtGapEvent (observed : Observed X) : Prop :=
  ∃ c j, CtGap crypto codec observed.2.1.transcript c j

open Classical in
/-- `CtGapEvent` as a Boolean of the observation; `F-ct2`'s explicit term is its probability in the experiment. -/
noncomputable def ctGapEvent (observed : Observed X) : Bool :=
  decide (CtGapEvent crypto codec observed)

end Definitions

/-! ### The registration view: acceptance, first finish, created owners -/

section Registration

/-- The raw input of the first successful finish of an owner in a registration view. -/
def finishReg (regs : List Reg) (owner : Nat) : Option Pqxdh.Bytes :=
  regs.findSome? fun reg => match reg with
    | .finish index raw (some _) => if index = owner then some raw else none
    | _ => none

/-- The first successful finish of an owner in the registration view of a transcript is its first successful finish in the transcript. -/
theorem finishReg_regsOf (transcript : List Entry) (owner : Nat) :
    finishReg (regsOf transcript) owner = finishOf transcript owner := by
  unfold finishReg regsOf finishOf
  rw [PqxdhDeploymentServerAuthInjectiveGame.findSome_filterMap]
  congr 1
  funext entry
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command with
    | create pin keyId =>
        cases reply with
        | none => rfl
        | some index => cases parsed : PqxdhDeploymentInterface.parsePin pin <;> simp [regOfEntry, parsed]
    | finish index raw =>
        cases reply with
        | none => rfl
        | some bytes => rfl
    | _ => rfl
  · rfl

/-- An owner whose summary phase is Established has an accepting finish in the registration view. -/
theorem established_accepted (c : Nat) (regs : List Reg) (established : (summarizeReg regs).phases c = .established) :
    ∃ before raw, accepted c regs = some (before, raw) := by
  induction regs using List.reverseRecOn with
  | nil => simp [summarizeReg, PqxdhDeploymentTranscript.Summary.empty] at established
  | append_singleton regs reg ih =>
      rw [PqxdhDeploymentServerAuthEvent.accepted_snoc]
      by_cases earlier : (summarizeReg regs).phases c = .established
      · obtain ⟨before, raw, found⟩ := ih earlier
        exact ⟨before, raw, by rw [found]; rfl⟩
      · rw [PqxdhDeploymentServerAuthEvent.summarizeReg_snoc] at established
        cases reg with
        | create pin keyId owner =>
            simp only [stepReg] at established
            by_cases same : c = owner
            · subst same
              simp at established
            · rw [Function.update_of_ne same] at established
              exact absurd established earlier
        | bundle owner reply =>
            cases reply with
            | none =>
                simp only [stepReg] at established
                split at established <;> exact absurd established earlier
            | some bytes =>
                simp only [stepReg] at established
                split at established
                · by_cases same : c = owner
                  · subst same
                    simp at established
                  · simp only [Function.update_of_ne same] at established
                    exact absurd established earlier
                · exact absurd established earlier
        | finish owner raw reply =>
            cases reply with
            | none =>
                simp only [stepReg] at established
                split at established
                · by_cases same : c = owner
                  · subst same
                    simp at established
                  · simp only [Function.update_of_ne same] at established
                    exact absurd established earlier
                · exact absurd established earlier
            | some payload =>
                simp only [stepReg] at established
                split at established
                · rename_i ready
                  by_cases same : c = owner
                  · subst same
                    cases prior : accepted c regs with
                    | some value => exact ⟨value.1, value.2, rfl⟩
                    | none =>
                        refine ⟨regs, raw, ?_⟩
                        simp [PqxdhDeploymentServerAuthEvent.acceptCheck, ready]
                  · simp only [Function.update_of_ne same] at established
                    exact absurd established earlier
                · exact absurd established earlier
        | accept raw reply => exact absurd established earlier
        | build session payload reply => exact absurd established earlier

/-- If every successful finish of `c` in a scanned list happens while the running summary has `c` in InitSent, the scan's acceptance is the list's first successful finish of `c`. -/
theorem acceptedFrom_first (c : Nat) :
    ∀ (regs : List Reg) (summary : PqxdhDeploymentTranscript.Summary) (passed before : List Reg) (raw : Pqxdh.Bytes),
      (∀ pre raw' payload rest, regs = pre ++ Reg.finish c raw' (some payload) :: rest →
        (pre.foldl stepReg summary).phases c = .initSent) →
      acceptedFrom c summary passed regs = some (before, raw) → finishReg regs c = some raw
  | [], _, _, _, _, _, found => by simp [acceptedFrom] at found
  | reg :: rest, summary, passed, before, raw, ready, found => by
      have shifted : ∀ pre raw' payload tail, rest = pre ++ Reg.finish c raw' (some payload) :: tail →
          (pre.foldl stepReg (stepReg summary reg)).phases c = .initSent := by
        intro pre raw' payload tail split
        have := ready (reg :: pre) raw' payload tail (by rw [split]; rfl)
        simpa using this
      cases reg with
      | finish owner input reply =>
          cases reply with
          | some payload =>
              simp only [acceptedFrom] at found
              split at found
              · rename_i hit
                obtain ⟨rfl, _⟩ := hit
                cases found
                simp [finishReg]
              · rename_i miss
                have other : owner ≠ c := by
                  intro same
                  subst same
                  exact miss ⟨rfl, by simpa using ready [] input payload rest rfl⟩
                have recursive := acceptedFrom_first c rest _ _ before raw shifted found
                simp only [finishReg, List.findSome?_cons, other, ite_false] at recursive ⊢
                exact recursive
          | none =>
              have recursive := acceptedFrom_first c rest _ _ before raw shifted found
              simp only [finishReg, List.findSome?_cons] at recursive ⊢
              exact recursive
      | create pin keyId owner =>
          have recursive := acceptedFrom_first c rest _ _ before raw shifted found
          simp only [finishReg, List.findSome?_cons] at recursive ⊢
          exact recursive
      | bundle owner reply =>
          have recursive := acceptedFrom_first c rest _ _ before raw shifted found
          simp only [finishReg, List.findSome?_cons] at recursive ⊢
          exact recursive
      | accept input reply =>
          have recursive := acceptedFrom_first c rest _ _ before raw shifted found
          simp only [finishReg, List.findSome?_cons] at recursive ⊢
          exact recursive
      | build session payload reply =>
          have recursive := acceptedFrom_first c rest _ _ before raw shifted found
          simp only [finishReg, List.findSome?_cons] at recursive ⊢
          exact recursive

/-- The created owners of a summary only grow, by appending. -/
theorem owners_foldl_prefix (summary : PqxdhDeploymentTranscript.Summary) (regs : List Reg) :
    summary.owners <+: (regs.foldl stepReg summary).owners := by
  induction regs generalizing summary with
  | nil => exact List.prefix_refl _
  | cons reg rest ih =>
      refine List.IsPrefix.trans ?_ (ih (stepReg summary reg))
      cases reg with
      | create pin keyId owner => exact List.prefix_append _ _
      | bundle owner reply =>
          cases reply <;> simp only [stepReg] <;> split <;> exact List.prefix_refl _
      | finish owner raw reply =>
          cases reply <;> simp only [stepReg] <;> split <;> exact List.prefix_refl _
      | accept raw reply => exact List.prefix_refl _
      | build session payload reply => exact List.prefix_refl _

/-- A created binding of a prefix of the registration view is the created binding of the whole view. -/
theorem owners_prefix_get (before regs : List Reg) (prefixed : before <+: regs) (c : Nat)
    (binding : PqxdhBeaconPhase2Preparation.Word32 × Aeneas.Std.U64)
    (found : (summarizeReg before).owners[c]? = some binding) : (summarizeReg regs).owners[c]? = some binding := by
  obtain ⟨rest, rfl⟩ := prefixed
  rw [PqxdhDeploymentServerAuthEvent.summarizeReg_append]
  obtain ⟨extra, same⟩ := owners_foldl_prefix (summarizeReg before) rest
  rw [← same, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

end Registration

/-! ### Successful finishes happen in InitSent (the native finish of `beacon.rs`) -/

section Finish

/-- Every successful finish of the registration view of the transcript happens while the running summary has its owner in InitSent, at a created owner. On the experiment this is the native fact that a finish outside `InitSent` is rejected (`beacon.rs`, `finish_registration`; `PqxdhDeploymentCompileFootprint.finish_owner`), read through the run invariant `PqxdhDeploymentEligibility.Agree`. -/
def FinishReady (transcript : List Entry) : Prop :=
  ∀ before owner raw payload rest, regsOf transcript = before ++ Reg.finish owner raw (some payload) :: rest →
    (summarizeReg before).phases owner = .initSent ∧ owner < (summarizeReg before).owners.length

/-- The registration view of a transcript extended by one entry. -/
theorem regsOf_snoc (transcript : List Entry) (entry : Entry) :
    regsOf (transcript ++ [entry]) = regsOf transcript ++ (regOfEntry entry).toList := by
  simp only [regsOf, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases regOfEntry entry <;> rfl

/-- `FinishReady` survives one more entry when a successful finish entry finds its owner created and in InitSent. -/
theorem finishReady_snoc (transcript : List Entry) (entry : Entry) (ready : FinishReady transcript)
    (fresh : ∀ owner raw payload, regOfEntry entry = some (.finish owner raw (some payload)) →
      (summarize transcript).phases owner = .initSent ∧ owner < (summarize transcript).owners.length) :
    FinishReady (transcript ++ [entry]) := by
  intro before owner raw payload rest split
  rw [regsOf_snoc] at split
  cases found : regOfEntry entry with
  | none =>
      rw [found, Option.toList_none, List.append_nil] at split
      exact ready before owner raw payload rest split
  | some reg =>
      rw [found, Option.toList_some] at split
      rcases List.eq_nil_or_concat rest with rfl | ⟨rest', last, rfl⟩
      · obtain ⟨same, single⟩ := List.append_inj' split.symm rfl
        simp only [List.cons.injEq, and_true] at single
        subst same
        rw [← single] at found
        have holds := fresh owner raw payload found
        rwa [PqxdhDeploymentServerAuthEvent.summarize_regs] at holds
      · have reshaped : before ++ Reg.finish owner raw (some payload) :: (rest' ++ [last]) =
            (before ++ Reg.finish owner raw (some payload) :: rest') ++ [last] := by simp
        rw [List.concat_eq_append, reshaped] at split
        obtain ⟨same, _⟩ := List.append_inj' split rfl
        exact ready before owner raw payload rest' same

/-- One query of the experiment keeps `FinishReady`, given the run invariant `Agree` before the query. -/
theorem ready_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (server : RawCtxServerRouting.Identity) (query : PqxdhDeploymentInterface.Query)
    (state : PqxdhDeploymentSecrecy.State KemSK)
    (agree : PqxdhDeploymentEligibility.Agree setup codec server state.1.transcript state.2.native)
    (ready : FinishReady state.1.transcript)
    (result : PqxdhDeploymentInterface.FullSpec.Range query × PqxdhDeploymentSecrecy.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds query).run
      state)) :
    FinishReady result.2.1.transcript := by
  rcases state with ⟨ledger, native⟩
  rw [PqxdhDeploymentEligibility.handler_run, support_map] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at member
    obtain ⟨answer, answerMember, rfl⟩ := member
    refine finishReady_snoc ledger.transcript _ ready fun owner raw payload hreg => ?_
    rcases request with coin | command
    · simp [regOfEntry] at hreg
    · cases command with
      | create pin keyId =>
          revert hreg
          rcases answer with ⟨reply, _⟩
          cases reply with
          | none => simp [regOfEntry]
          | some index => cases PqxdhDeploymentInterface.parsePin pin <;> simp [regOfEntry]
      | finish index input =>
          simp only [regOfEntry, Option.some.injEq, Reg.finish.injEq] at hreg
          obtain ⟨rfl, rfl, replied⟩ := hreg
          simp only [PqxdhDeploymentNative.handler] at answerMember
          obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ native answer answerMember
          simp only at replied
          cases found : native.native.owners[index]? with
          | none =>
              change inner ∈ support ((PqxdhRegistrationSchedule.finish setup codec index input).run native.native)
                at innerMember
              rw [PqxdhRegistrationSchedule.finish_missing setup codec index input native.native found, support_pure,
                Set.mem_singleton_iff] at innerMember
              subst innerMember
              cases replied
          | some ownerState =>
              change inner ∈ support (PqxdhRegistrationSchedule.finish setup codec index input native.native)
                at innerMember
              rw [PqxdhRegistrationSchedule.finish_source setup codec index input native.native ownerState found,
                support_map] at innerMember
              obtain ⟨reached, reachedMember, rfl⟩ := innerMember
              obtain ⟨control, prekey, oneTime, kem, _, _, ownerPhase, _, _⟩ :=
                (PqxdhDeploymentCompileFootprint.finish_owner setup codec input ownerState native.native.shared reached
                  reachedMember).2 payload replied
              have phases := agree.phases index
              simp only [PqxdhDeploymentEligibility.nativePhase, found, ownerPhase,
                PqxdhDeploymentEligibility.phaseClass] at phases
              refine ⟨phases, ?_⟩
              rw [agree.count]
              exact (List.getElem?_eq_some_iff.mp found).1
      | _ =>
          revert hreg
          rcases answer with ⟨reply, _⟩
          cases reply <;> simp [regOfEntry]
  · have value : reached.1 ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId
        bounds (.inr secrecy)).run ledger) := by
      apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
        _ native
      rw [StateT.run'_eq, support_map]
      exact ⟨reached, member, rfl⟩
    have recorded := PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy
      ledger reached.1 value
    show FinishReady reached.1.2.transcript
    rw [recorded]
    exact finishReady_snoc ledger.transcript _ ready fun owner raw payload hreg => by simp [regOfEntry] at hreg

/-- The empty transcript is `FinishReady`. -/
theorem ready_empty : FinishReady [] := by
  intro before owner raw payload rest split
  simp [regsOf] at split

/-- On every outcome of the experiment, every successful finish of the final transcript happened while the running summary had its owner created and in InitSent: the invariant `Agree ∧ FinishReady` holds along the run (`PqxdhDeploymentEligibility.experiment_step`, `ready_step`). -/
theorem ready_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) :
    FinishReady final.1.transcript := by
  simp only [PqxdhDeploymentSecrecy.game, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, _, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    cases reached
    have invariant := OracleComp.simulateQ_run_preserves_inv_of_query
      (PqxdhDeploymentSecrecy.handler setup codec checks route constructed.seed bounds)
      (fun state => PqxdhDeploymentEligibility.Agree setup codec
        (PqxdhDeploymentNative.initial (KemSK := KemSK) constructed).native.shared.2.server.server.identity
        state.1.transcript state.2.native ∧ FinishReady state.1.transcript)
      (fun query state holds result member => ⟨PqxdhDeploymentEligibility.experiment_step setup codec checks route
        constructed.seed bounds _ query state holds.1 result member,
        ready_step setup codec checks route constructed.seed bounds _ query state holds.1 holds.2 result member⟩)
      (PqxdhDeploymentInterface.asModeO mode adversary)
      (PqxdhDeploymentSecrecy.Ledger.empty, PqxdhDeploymentNative.initial constructed)
      ⟨PqxdhDeploymentEligibility.agree_initial setup codec constructed, ready_empty⟩ _ executedMember
    exact invariant.2

/-- The scan's acceptance splits the scanned entries at the accepting finish. -/
theorem acceptedFrom_split (c : Nat) :
    ∀ (regs passed : List Reg) (before : List Reg) (raw : Pqxdh.Bytes),
      acceptedFrom c (summarizeReg passed) passed regs = some (before, raw) →
        ∃ payload rest, passed ++ regs = before ++ Reg.finish c raw (some payload) :: rest
  | [], _, _, _, found => by simp [acceptedFrom] at found
  | reg :: rest, passed, before, raw, found => by
      have step : stepReg (summarizeReg passed) reg = summarizeReg (passed ++ [reg]) :=
        (PqxdhDeploymentServerAuthEvent.summarizeReg_snoc passed reg).symm
      have recurse : acceptedFrom c (stepReg (summarizeReg passed) reg) (passed ++ [reg]) rest = some (before, raw) →
          ∃ payload tail, passed ++ reg :: rest = before ++ Reg.finish c raw (some payload) :: tail := by
        intro inner
        rw [step] at inner
        obtain ⟨payload, tail, split⟩ := acceptedFrom_split c rest (passed ++ [reg]) before raw inner
        exact ⟨payload, tail, by simpa using split⟩
      cases reg with
      | finish owner input reply =>
          cases reply with
          | some payload =>
              simp only [acceptedFrom] at found
              split at found
              · rename_i hit
                obtain ⟨rfl, _⟩ := hit
                cases found
                exact ⟨payload, rest, rfl⟩
              · exact recurse found
          | none => exact recurse found
      | create pin keyId owner => exact recurse found
      | bundle owner reply => exact recurse found
      | accept input reply => exact recurse found
      | build session payload reply => exact recurse found

/-- The acceptance of a registration view splits it at the accepting finish. -/
theorem accepted_split (c : Nat) (regs before : List Reg) (raw : Pqxdh.Bytes)
    (found : accepted c regs = some (before, raw)) :
    ∃ payload rest, regs = before ++ Reg.finish c raw (some payload) :: rest := by
  simpa using acceptedFrom_split c regs [] before raw found

/-- Under `FinishReady`, an accepting finish is the first successful finish of its owner, and the owner was created before it, with the binding it has at the end. -/
theorem ready_accepted (transcript : List Entry) (ready : FinishReady transcript) (c : Nat) (before : List Reg)
    (raw : Pqxdh.Bytes) (found : accepted c (regsOf transcript) = some (before, raw)) :
    finishOf transcript c = some raw ∧ ∀ binding, (summarize transcript).owners[c]? = some binding →
      (summarizeReg before).owners[c]? = some binding := by
  refine ⟨?_, fun binding bound => ?_⟩
  · rw [← finishReg_regsOf]
    exact acceptedFrom_first c (regsOf transcript) _ [] before raw
      (fun pre raw' payload rest split => (ready pre c raw' payload rest split).1) found
  · obtain ⟨payload, rest, split⟩ := accepted_split c _ before raw found
    have created := (ready before c raw payload rest split).2
    have valueFound : (summarizeReg before).owners[c]? = some (summarizeReg before).owners[c] :=
      List.getElem?_eq_getElem created
    set value := (summarizeReg before).owners[c]
    have whole := owners_prefix_get before (regsOf transcript) ⟨_, split.symm⟩ c value valueFound
    rw [← PqxdhDeploymentServerAuthEvent.summarize_regs, bound, Option.some.injEq] at whole
    rw [valueFound, whole]

/-- Conversely, if every successful finish of `c` in a scanned list happens while the running summary has `c` in InitSent, the list's first successful finish of `c` is the scan's acceptance. -/
theorem first_acceptedFrom (c : Nat) :
    ∀ (regs : List Reg) (summary : PqxdhDeploymentTranscript.Summary) (passed : List Reg) (raw : Pqxdh.Bytes),
      (∀ pre raw' payload rest, regs = pre ++ Reg.finish c raw' (some payload) :: rest →
        (pre.foldl stepReg summary).phases c = .initSent) →
      finishReg regs c = some raw → ∃ before, acceptedFrom c summary passed regs = some (before, raw)
  | [], _, _, _, _, found => by simp [finishReg] at found
  | reg :: rest, summary, passed, raw, ready, found => by
      have shifted : ∀ pre raw' payload tail, rest = pre ++ Reg.finish c raw' (some payload) :: tail →
          (pre.foldl stepReg (stepReg summary reg)).phases c = .initSent := by
        intro pre raw' payload tail split
        have := ready (reg :: pre) raw' payload tail (by rw [split]; rfl)
        simpa using this
      have recurse : finishReg rest c = some raw →
          ∃ before, acceptedFrom c (stepReg summary reg) (passed ++ [reg]) rest = some (before, raw) :=
        first_acceptedFrom c rest _ _ raw shifted
      cases reg with
      | finish owner input reply =>
          cases reply with
          | some payload =>
              by_cases same : owner = c
              · subst same
                simp only [finishReg, List.findSome?_cons, ite_true, Option.some.injEq] at found
                subst found
                have phaseReady : summary.phases owner = .initSent := by simpa using ready [] input payload rest rfl
                exact ⟨passed, by simp [acceptedFrom, phaseReady]⟩
              · simp only [finishReg, List.findSome?_cons, same, ite_false] at found
                obtain ⟨before, inner⟩ := recurse found
                exact ⟨before, by simp only [acceptedFrom, same, false_and, ite_false]; exact inner⟩
          | none =>
              simp only [finishReg, List.findSome?_cons] at found
              exact recurse found
      | create pin keyId owner =>
          simp only [finishReg, List.findSome?_cons] at found
          exact recurse found
      | bundle owner reply =>
          simp only [finishReg, List.findSome?_cons] at found
          exact recurse found
      | accept input reply =>
          simp only [finishReg, List.findSome?_cons] at found
          exact recurse found
      | build session payload reply =>
          simp only [finishReg, List.findSome?_cons] at found
          exact recurse found

/-- `finish_accepted` (design-v2 section 7.1): on every outcome of the experiment, the first successful finish of an owner is its accepting finish: `finishOf` names raw input `raw` exactly when owner `c` accepted with input `raw` (a native finish succeeds only in `InitSent`, `beacon.rs` `finish_registration`). -/
theorem finish_accepted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) (c : Nat)
    (raw : Pqxdh.Bytes) :
    finishOf final.1.transcript c = some raw ↔ ∃ before, accepted c (regsOf final.1.transcript) = some (before, raw) := by
  have ready := ready_game setup codec checks route ensureInit identityIndex bounds mode adversary runtime outcome
    supported created output final reached
  constructor
  · intro found
    rw [← finishReg_regsOf] at found
    exact first_acceptedFrom c _ _ [] raw (fun pre raw' payload rest split => (ready pre c raw' payload rest split).1)
      found
  · rintro ⟨before, found⟩
    exact (ready_accepted _ ready c before raw found).1

end Finish

/-! ### Positional sessions -/

section Sessions
open PqxdhDeploymentKemTransfer (registrations)
open PqxdhDeploymentRegistrationTrace (acceptsOf)

/-- An accept entry of a transcript is a logged raw accept of its registrations. -/
theorem accept_logged (transcript : List Entry) (raw : Pqxdh.Bytes) (reply : Option Nat)
    (member : (⟨.inl (.inr (.accept raw)), reply⟩ : Entry) ∈ transcript) :
    (raw, reply) ∈ acceptsOf (registrations transcript) := by
  apply PqxdhDeploymentServerAuthInjectiveGame.accept_registrations
  simp only [regsOf, List.mem_filterMap]
  exact ⟨_, member, rfl⟩

/-- The number of accept attempts is the number of logged raw accepts. -/
theorem acceptCount_logged (transcript : List Entry) :
    acceptCount transcript = (acceptsOf (registrations transcript)).length := by
  rw [PqxdhDeploymentTargetRange.accepts_count]
  unfold acceptCount PqxdhDeploymentTargetRange.classCount
  congr 1
  funext entry
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · rfl
  · cases command <;> rfl
  · rcases secrecy with ⟨_, _, _⟩ | ⟨_, _⟩ <;> rfl

/-- Session handles are positional on every outcome of the experiment (identity index zero): a session handle that an accept returned is below the number of accept attempts, and it is the first accept returning it that `acceptOf` reads, with the same bytes. -/
theorem accept_positional (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (raw : Pqxdh.Bytes) (session : Nat)
    (accepted : (⟨.inl (.inr (.accept raw)), some session⟩ : Entry) ∈ final.1.transcript) :
    session < acceptCount final.1.transcript ∧ acceptOf final.1.transcript session = some raw := by
  have logged := accept_logged _ raw (some session) accepted
  have first : (acceptOf final.1.transcript session).isSome := by
    unfold acceptOf
    rw [List.findSome?_isSome_iff]
    exact ⟨_, accepted, by simp⟩
  obtain ⟨other, otherFound⟩ := Option.isSome_iff_exists.mp first
  have same := PqxdhDeploymentServerAuthInjectiveGame.session_unique setup codec checks route ensureInit phase1 phase2
    bounds mode adversary runtime outcome member created output final found other raw session
    (accept_logged _ other (some session) (PqxdhDeploymentKemTransfer.acceptOf_mem _ session other otherFound)) logged
  refine ⟨?_, by rw [otherFound, same]⟩
  have game := PqxdhDeploymentCompileSecrecy.compile_full_source setup codec checks route ensureInit phase1 phase2 bounds
    mode adversary ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  change _ = (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime at game
  have traced := PqxdhDeploymentRegistrationTrace.source_map setup codec checks ensureInit none Prod.fst
    (PqxdhDeploymentRegistrationTrace.traceFrom (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode
      adversary) []) ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  rw [PqxdhDeploymentRegistrationTrace.traceFrom_erase] at traced
  rw [← game, traced, Functor.map_map, support_map] at member
  obtain ⟨⟨_ | source, after⟩, sourceMember, rfl⟩ := member
  · simp [PqxdhDeploymentCompileSecrecy.mergeFull] at found
  · simp only [PqxdhDeploymentCompileSecrecy.mergeFull, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨_, _, rfl⟩ := found
    have result := PqxdhDeploymentRegistrationTrace.source_support setup codec checks ensureInit none _ _ _ source
      sourceMember
    have logEq := PqxdhDeploymentKemTransfer.compiled_trace setup codec route bounds mode adversary source.2.1 result
    obtain ⟨tracedState, _⟩ := PqxdhDeploymentRegistrationTrace.traced_source setup codec checks ensureInit none _ _ rfl
      after source sourceMember
    simp only [PqxdhRegistrationJointInitializedSchedule.eraseOutcome] at logged ⊢
    rw [acceptCount_logged]
    rw [← logEq] at logged ⊢
    obtain ⟨position, positionFound⟩ := List.mem_iff_getElem?.mp logged
    have samePosition := tracedState.positional position raw session positionFound
    rw [samePosition]
    exact (List.getElem?_eq_some_iff.mp positionFound).1

end Sessions

/-! ### The gap lemmas on the support of the experiment -/

section Gaps

/-- The source attached verification accepts a candidate with an identity key only when its identity field is that key's encoding. -/
theorem acceptedKeys_identity (crypto : Pqxdh.Crypto) (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (identity : PqxdhEd25519EufCma.Ed25519PublicKey) (keys : PqxdhEd25519EufCma.Phase1KeyTuple)
    (found : acceptedKeys crypto candidate = some (identity, keys)) :
    candidate.identityKey = PqxdhEd25519EufCma.encodedIdentity identity := by
  unfold acceptedKeys PqxdhJointPhase1Reports.sourceAccept at found
  obtain ⟨publicKey, parsed, rest⟩ := Option.bind_eq_some_iff.mp found
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at rest
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := rest
  rw [← (Prod.mk.injEq _ _ _ _ |>.mp same).1]
  exact (PqxdhEd25519EufCma.parseIdentity_eq_some_iff _ _).mp parsed

/-- The key tuple read from a candidate carries the PQ key that `publishedPq` reads. -/
theorem candidateTuple_pq (candidate : PqxdhEd25519EufCma.Phase1Candidate) (keys : PqxdhEd25519EufCma.Phase1KeyTuple)
    (found : candidateTuple candidate = some keys) : publishedPq candidate = some keys.pqKey := by
  unfold candidateTuple at found
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
  obtain ⟨_, _, _, _, pq, pqFound, _, _, _, _, pqKey, pqKeyFound, rfl⟩ := found
  simp [publishedPq, pqFound, pqKeyFound]

/-- `server_gap` (design-v2 section 7.1): on every outcome of the experiment of a budget-respecting adversary, a Server peer that is symbolically eligible (`SymServer` with the final native identity keys) and not designated inside the budget witnesses a published-tuple forgery at the owner whose identity key the accepted candidate carries, and that owner made no rejected bundle call in Fresh (CE-A2pub's `OwnerForgery`). If the owner's published tuple were the accepted one, the owner's honest bundle (read back with `Phase1ReadBack`) would carry the accepted identity field and PQ key, so `designate` would name the session and an owner (`designate_peer_complete`), inside the budget (`PqxdhDeploymentTargetRange.range_game`). -/
theorem server_gap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (keyId : Aeneas.Std.U64)
    (sym : SymServer setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native) keyId)
    (undesignated : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript (.peer keyId) =
      none) :
    ∃ c, OwnerForgery setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native) c ∧
      NoBundleFailureAt final.1.transcript c := by
  obtain ⟨session, response, raw, candidate, identity, keys, c, linked, rawFound, candidateFound, keysFound, identityFound,
    clean⟩ := sym
  refine ⟨c, ?_, clean⟩
  by_contra notForged
  have tuple : publishedTuple codec final.1.transcript c = some keys := by
    by_contra other
    exact notForged ⟨raw, session, PqxdhDeploymentKemTransfer.acceptOf_mem _ session raw rawFound, candidate, identity,
      keys, candidateFound, keysFound, identityFound, other⟩
  unfold publishedTuple at tuple
  obtain ⟨published, publishedFound, tupleFound⟩ := Option.bind_eq_some_iff.mp tuple
  obtain ⟨bytes, bytesFound, readFound⟩ := Option.bind_eq_some_iff.mp publishedFound
  have agree := PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit 0 bounds mode adversary
    runtime outcome member created output final found
  obtain ⟨entry, honest, preSignature, oneSignature, pqSignature, entryFound, written, _⟩ :=
    agree.bundles _ (PqxdhDeploymentKeyMatch.bundleOf_mem _ c bytes bytesFound)
  rw [PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at readFound
  have identityEq : identity = (setup.joint.publicKeys entry.beacon.identity).ed25519 := by
    simp only [ownerIdentities, List.getElem?_map, entryFound, Option.map_some, Option.some.injEq] at identityFound
    exact identityFound.symm
  have publishes : Publishes codec final.1.transcript candidate keys.pqKey c := by
    refine ⟨published, publishedFound, ?_, candidateTuple_pq published keys tupleFound⟩
    rw [← readFound, acceptedKeys_identity _ candidate identity keys keysFound, identityEq]
    rfl
  have createdBound : c < (summarize final.1.transcript).owners.length := by
    rw [agree.count]
    exact (List.getElem?_eq_some_iff.mp entryFound).1
  obtain ⟨first, _, designated⟩ := PqxdhDeploymentTranscript.designate_peer_complete setup.source.crypto codec
    setup.serverKeyId keyId final.1.transcript session response raw candidate (identity, keys) c linked rawFound
    candidateFound keysFound createdBound publishes
  have observed : PqxdhDeploymentKemTransfer.observeGame outcome.1 = some (output, final.1, final.2.produced) := by
    rw [found]
    rfl
  obtain ⟨sessionBound, kBound⟩ := PqxdhDeploymentTargetRange.range_game setup codec checks route ensureInit phase1
    phase2 bounds mode adversary budget respects runtime outcome member _ observed (.peer keyId) session first designated
  rw [PqxdhDeploymentTargetRange.designateIn_range _ codec _ budget _ (.peer keyId) session first designated sessionBound
    kBound] at undesignated
  cases undesignated

/-- An accept of the registration view of a transcript is an accept entry of the transcript. -/
theorem accept_entry (transcript : List Entry) (raw : Pqxdh.Bytes) (reply : Option Nat)
    (member : Reg.accept raw reply ∈ regsOf transcript) :
    (⟨.inl (.inr (.accept raw)), reply⟩ : Entry) ∈ transcript := by
  simp only [regsOf, List.mem_filterMap] at member
  obtain ⟨entry, entryMember, found⟩ := member
  rcases entry with ⟨(coin | command) | secrecy, entryReply⟩
  · cases found
  · cases command with
    | create pin keyId =>
        cases entryReply with
        | none => cases found
        | some index =>
            cases parsed : PqxdhDeploymentInterface.parsePin pin <;> simp [regOfEntry, parsed] at found
    | accept other =>
        simp only [regOfEntry, Option.some.injEq, Reg.accept.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        exact entryMember
    | _ => simp [regOfEntry] at found
  · cases found

/-- `beacon_gap` (design-v2 section 7.1): on every outcome of the experiment of a budget-respecting adversary, an owner that is symbolically eligible (`SymBeacon` with the constructed Server's identity as pin and the protected key ID) and not designated inside the budget either is a CE-A1 failure (`A1NoPinnedMatch`: no session matches it with the pin before its acceptance) or has a pinned match whose build ciphertext differs from its finish ciphertext (`CtGap`). Native ingredients: an Established owner has an accepting finish (`established_accepted`), which is its first successful finish and comes after its creation (`ready_game`, the native finish of `beacon.rs` that rejects outside `InitSent`); session handles are positional (`accept_positional`); every build response carries the constructed Server's identity (`PqxdhDeploymentServerAuth.build_pin`) and a ciphertext (`Phase2ReadBack`). With equal ciphertexts the pinned match is `Linked`, so `designate` would name the owner (`designate_owner_complete`), inside the budget. -/
theorem beacon_gap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X) (final : PqxdhDeploymentSecrecy.State KemSK)
    (found : outcome.1 = some (created, output, final)) (c : Nat)
    (sym : SymBeacon final.1.transcript (protectedBinding setup created).1 setup.serverKeyId c)
    (undesignated : designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript (.owner c) =
      none) :
    A1NoPinnedMatch setup codec c outcome ∨ ∃ j, CtGap setup.source.crypto codec final.1.transcript c j := by
  obtain ⟨established, binding, clean⟩ := sym
  have ready := ready_game setup codec checks route ensureInit 0 bounds mode adversary runtime outcome member created
    output final found
  obtain ⟨before, raw, acceptedFound⟩ := established_accepted c (regsOf final.1.transcript) (by
    rw [← PqxdhDeploymentServerAuthEvent.summarize_regs]
    exact established)
  obtain ⟨finished, owners⟩ := ready_accepted final.1.transcript ready c before raw acceptedFound
  have bindingBefore := owners _ binding
  have prefixed := PqxdhDeploymentServerAuthEvent.accepted_prefix c _ before raw acceptedFound
  by_cases pinned : PinnedMatch setup.source.crypto codec c (protectedBinding setup created).1 before raw
  · right
    obtain ⟨j, pin⟩ := pinned
    refine ⟨j, ?_⟩
    by_contra noGap
    have sameCt : ciphertextOf codec (finishOf final.1.transcript c) =
        ciphertextOf codec ((buildOf final.1.transcript j).map (·.serialized)) := by
      by_contra different
      exact noGap ⟨before, raw, _, acceptedFound, binding, pin, different⟩
    obtain ⟨acceptRaw, candidate, keys, payload, reply, _, acceptMember, candidateFound, keysFound, publishedFound,
      buildMember, _, _, _⟩ := pin
    have agree := PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit 0 bounds mode adversary
      runtime outcome member created output final found
    have buildEntry := PqxdhDeploymentServerAuth.build_entry final.1.transcript j payload reply
      (prefixed.subset buildMember)
    have buildSome : (buildOf final.1.transcript j).isSome := by
      unfold buildOf
      rw [List.findSome?_isSome_iff]
      exact ⟨_, buildEntry, by simp⟩
    obtain ⟨response, responseFound⟩ := Option.isSome_iff_exists.mp buildSome
    obtain ⟨responsePayload, responseMember⟩ := PqxdhDeploymentKeyMatch.buildOf_mem _ j response responseFound
    obtain ⟨fields, written, _⟩ := id (agree.builds _ responseMember)
    obtain ⟨read, readFound, ciphertextFound, _, _, _, _⟩ := phase2 fields _ written
    have pinFound := PqxdhDeploymentServerAuth.build_pin setup codec checks route ensureInit 0 phase2 bounds mode
      adversary runtime outcome member created output final found j responsePayload response responseMember
    have finishCt : (codec.read2 raw).bind codec.ciphertext = some fields.kemCiphertext := by
      have := sameCt
      simp only [ciphertextOf, finished, responseFound, Option.map_some, Option.bind_some, readFound,
        ciphertextFound] at this
      exact this
    obtain ⟨sessionBound, acceptFound⟩ := accept_positional setup codec checks route ensureInit phase1 phase2 bounds mode
      adversary runtime outcome member created output final found acceptRaw j
      (accept_entry _ acceptRaw (some j) (prefixed.subset acceptMember))
    unfold publishedKeys keysOfBundle at publishedFound
    obtain ⟨bytes, bytesFound, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedFound
    obtain ⟨published, candidateRead, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedRest
    obtain ⟨identityKey, _, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedRest
    obtain ⟨tuple, tupleFound, publishedRest⟩ := Option.bind_eq_some_iff.mp publishedRest
    simp only [Option.pure_def, Option.some.injEq] at publishedRest
    have bundleFound : PqxdhDeploymentTranscript.bundleOf final.1.transcript c = some bytes := by
      rw [← PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_regsOf]
      exact PqxdhDeploymentServerAuthInjectiveGame.bundleOfReg_prefix _ _ prefixed c bytes bytesFound
    have linked : Linked setup.source.crypto codec final.1.transcript fields.kemCiphertext
        (protectedBinding setup created).1 tuple.pqKey j := by
      refine ⟨response, candidate, keys, responseFound, by rw [readFound, Option.bind_some, ciphertextFound], pinFound,
        by rw [acceptFound, Option.bind_some, candidateFound], keysFound, ?_⟩
      rw [← publishedRest]
    obtain ⟨first, _, designated⟩ := PqxdhDeploymentTranscript.designate_owner_complete setup.source.crypto codec
      setup.serverKeyId final.1.transcript c (protectedBinding setup created).1 raw fields.kemCiphertext published
      tuple.pqKey j established binding finished finishCt (by rw [bundleFound, Option.bind_some, candidateRead])
      (candidateTuple_pq published tuple tupleFound) sessionBound linked
    have observed : PqxdhDeploymentKemTransfer.observeGame outcome.1 = some (output, final.1, final.2.produced) := by
      rw [found]
      rfl
    obtain ⟨firstBound, kBound⟩ := PqxdhDeploymentTargetRange.range_game setup codec checks route ensureInit phase1
      phase2 bounds mode adversary budget respects runtime outcome member _ observed (.owner c) first c designated
    rw [PqxdhDeploymentTargetRange.designateIn_range _ codec _ budget _ (.owner c) first c designated firstBound
      kBound] at undesignated
    cases undesignated
  · left
    exact ⟨created, output, final, found, clean, before, raw, acceptedFound, bindingBefore, pinned⟩

end Gaps

/-! ### The gap events and their bounds -/

section Bounds

/-- The Server-side gap on an outcome of the experiment: a Server was constructed and some symbolically eligible Server peer (`SymServer` with the final native identity keys) is not designated inside the budget. -/
def ServerGap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧ ∃ keyId,
    SymServer setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native) keyId ∧
    designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript (.peer keyId) = none

/-- The Beacon-side gap on an outcome of the experiment: a Server was constructed and some symbolically eligible owner (`SymBeacon` with the constructed Server's identity as pin and the protected key ID) is not designated inside the budget. It is the CE-A1 failure whose matching carries the ciphertext, the pin and the PQ key (`ce_a1_linked`): designation of an owner is its smallest linked session. -/
def BeaconGap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧ ∃ c,
    SymBeacon final.1.transcript (protectedBinding setup created).1 setup.serverKeyId c ∧
    designateIn setup.source.crypto codec setup.serverKeyId budget final.1.transcript (.owner c) = none

open Classical in
/-- `ServerGap` as a Boolean of the outcome. -/
noncomputable def serverGap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (ServerGap setup codec budget outcome)

open Classical in
/-- `BeaconGap` as a Boolean of the outcome. -/
noncomputable def beaconGap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (BeaconGap setup codec budget outcome)

/-- `ε_A2pub` (design-v2 section 2): the per-owner CE-A2pub bound, the sum over the `qCreate + 1` generated identity positions of the joint-use weak-EUF advantages of the A2 client's reductions (`PqxdhDeploymentPublishedTuple.a2pub_owner_bound`). -/
noncomputable def a2pubTerm (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) : ℝ≥0∞ :=
  ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
    (PqxdhDeploymentProvenance.reduction setup codec checks route ensureInit bounds mode adversary budget.create runtime
      fallback ordinaryFallback target)

/-- `ε_A1` (design-v2 section 2): the CE-A1 bound at the caps transported from the budget, the sum over the `qCreate` creation indices of the Server-authentication bound of `R_c` (`PqxdhDeploymentServerAuthBills.ce_a1_billed`). -/
noncomputable def a1Term (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) : ℝ :=
  ∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup codec checks caps
    (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
    (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
    (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget) fallback
    signatureFallback

/-- The explicit public ciphertext-gap term of the F-ct2 form (design-v2 section 8): the probability that the experiment ends with `CtGapEvent`, some owner with a pinned match whose build ciphertext differs from its finish ciphertext. -/
noncomputable def ctGapTerm (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) : ℝ≥0∞ :=
  𝒟[(fun outcome => happens (ctGapEvent setup.source.crypto codec) outcome) <$>
    (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true}

/-- Support monotonicity of the probability of a Boolean event. -/
theorem chance_le_support {α : Type} (run : ProbComp α) (first second : α → Bool)
    (implies : ∀ a ∈ support run, first a = true → second a = true) :
    𝒟[first <$> run] {true} ≤ 𝒟[second <$> run] {true} := by
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun a member held => implies a member held

/-- The union bound on the support for Boolean events. -/
theorem chance_le_add_support {α : Type} (run : ProbComp α) (first second third : α → Bool)
    (implies : ∀ a ∈ support run, first a = true → second a = true ∨ third a = true) :
    𝒟[first <$> run] {true} ≤ 𝒟[second <$> run] {true} + 𝒟[third <$> run] {true} := by
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true,
    ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map, prEvent_map]
  refine le_trans (prEvent_mono_of_support _ _ _ fun a member held => implies a member held) ?_
  exact prEvent_or_le run _ _

/-- The Server-side gap is contained in the per-owner CE-A2pub event on every outcome of the experiment (`server_gap`). Premises: the approved Phase 1 and Phase 2 read-back contracts and the budget. -/
theorem server_gap_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[serverGap setup codec budget <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => @decide (OwnerEvent setup codec outcome) (Classical.propDecidable _)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} := by
  refine chance_le_support _ _ _ fun outcome member held => ?_
  simp only [serverGap, decide_eq_true_eq] at held ⊢
  obtain ⟨created, output, final, found, keyId, sym, undesignated⟩ := held
  obtain ⟨c, forged, clean⟩ := server_gap setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget
    respects runtime outcome member created output final found keyId sym undesignated
  exact ⟨created, output, final, found, c, forged, clean⟩

/-- The Server-side gap term: the probability of `ServerGap` is at most `ε_A2pub` (`server_gap_le` and `PqxdhDeploymentPublishedTuple.a2pub_owner_bound`). Premises: `shortRejects` with `setup.wiring`, the approved Phase 1 and Phase 2 read-back contracts and the budget. -/
theorem server_gap_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[serverGap setup codec budget <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      a2pubTerm setup codec checks route ensureInit bounds mode adversary budget runtime fallback ordinaryFallback :=
  (server_gap_le setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects runtime).trans
    (PqxdhDeploymentPublishedTuple.a2pub_owner_bound setup codec checks shortRejects phase1 phase2 route ensureInit bounds
      mode adversary budget respects runtime fallback ordinaryFallback)

/-- The Beacon-side gap is contained in the union of CE-A1's event and the public ciphertext-gap event on every outcome of the experiment (`beacon_gap`). Premises: the approved Phase 1 and Phase 2 read-back contracts and the budget. -/
theorem beacon_gap_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[beaconGap setup codec budget <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => @decide (∃ c, A1NoPinnedMatch setup codec c outcome) (Classical.propDecidable _)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  refine chance_le_add_support _ _ _ _ fun outcome member held => ?_
  simp only [beaconGap, decide_eq_true_eq] at held
  obtain ⟨created, output, final, found, c, sym, undesignated⟩ := held
  rcases beacon_gap setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects runtime
    outcome member created output final found c sym undesignated with failure | ⟨j, gap⟩
  · left
    simp only [decide_eq_true_eq]
    exact ⟨c, failure⟩
  · right
    simp only [happens, PqxdhDeploymentKemTransfer.observeGame, found, Option.map_some, Option.any_some, ctGapEvent,
      decide_eq_true_eq]
    exact ⟨c, j, gap⟩

/-- `ce_a1_linked` in the F-ct2 form (design-v2 sections 7.1 and 8): the probability that some owner pinned to the constructed Server and the protected key ID is Established with no rejected bundle call in Fresh and is not designated inside the budget (no linked session: none whose build carries its finish ciphertext and its pin and whose accept carries its published PQ key) is at most `ε_A1` (`ce_a1_billed`, at the caps transported from the budget) plus the explicit public term `ctGapTerm`, with the bills of every CE-A1 reduction. Premises: those of CE-A1 (`FrameReadBack`, `ReadWritable`, `X25519ClassLaw`, `X25519ScalarSpread`, `SourceFullCorrect`, `HasAttachedVerificationAdapter`, `KemBound`, the read-back contracts and the budget). The closed form with `ε_ct` (design-v2 section 8, `ctgap_world`) is not proved (the D-ct spike's stop rule fired); `ctGapTerm` stays explicit. -/
theorem ce_a1_linked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[beaconGap setup codec budget <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget fallback signatureFallback) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
      (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
      (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget)
      (PqxdhDeploymentServerAuthBills.totalCap caps bounds budget) budget.finish fallback signatureFallback := by
  have a1 := PqxdhDeploymentServerAuthBills.ce_a1_billed setup codec checks caps bounded route ensureInit 0 phase1 phase2
    frameBack writable law spread correct adapter bounds mode adversary budget respects runtime fallback
    signatureFallback
  refine ⟨(beacon_gap_le setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects
    runtime).trans (add_le_add ?_ le_rfl), a1.2⟩
  rw [← ENNReal.ofReal_toReal (UniformTargetSelection.chance_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal a1.1

/-- `sym_gap` in the F-ct2 form (design-v2 sections 7.1 and 8): the probability that some symbolically eligible handle (a Server peer with `SymServer` or an owner with `SymBeacon`) is not designated inside the budget is at most `ε_A2pub + ε_A1` plus the explicit public term `ctGapTerm`. The premises are the union of those of `server_gap_bound` and `ce_a1_linked`. -/
theorem sym_gap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
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
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[(fun outcome => serverGap setup codec budget outcome || beaconGap setup codec budget outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      a2pubTerm setup codec checks route ensureInit bounds mode adversary budget runtime identityFallback
        ordinaryFallback +
      ENNReal.ofReal (a1Term setup codec checks caps route bounds mode adversary budget fallback signatureFallback) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  refine (chance_le_add_support _ _ (serverGap setup codec budget) (beaconGap setup codec budget)
    fun outcome _ held => by simpa using held).trans ?_
  rw [add_assoc]
  exact add_le_add (server_gap_bound setup codec checks shortRejects route ensureInit phase1 phase2 bounds mode adversary
    budget respects runtime identityFallback ordinaryFallback)
    (ce_a1_linked setup codec checks caps bounded route ensureInit phase1 phase2 frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime fallback signatureFallback).1

end Bounds

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.finishReg_regsOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.finishReg_regsOf

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.established_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.established_accepted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.acceptedFrom_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.acceptedFrom_first

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.owners_foldl_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.owners_foldl_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.owners_prefix_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.owners_prefix_get

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.regsOf_snoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.regsOf_snoc

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.finishReady_snoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.finishReady_snoc

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.ready_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.ready_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.ready_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.ready_empty

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.ready_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.ready_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.acceptedFrom_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.acceptedFrom_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.accepted_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.accepted_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.ready_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.ready_accepted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.first_acceptedFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.first_acceptedFrom

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.finish_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.finish_accepted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.accept_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.accept_logged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.acceptCount_logged' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.acceptCount_logged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.accept_positional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.accept_positional

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.acceptedKeys_identity' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.acceptedKeys_identity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.candidateTuple_pq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.candidateTuple_pq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.server_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.server_gap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.accept_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.accept_entry

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.beacon_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.beacon_gap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.chance_le_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.chance_le_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.chance_le_add_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.chance_le_add_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.server_gap_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.server_gap_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.server_gap_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.server_gap_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.beacon_gap_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.beacon_gap_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.ce_a1_linked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.ce_a1_linked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.sym_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap.sym_gap
