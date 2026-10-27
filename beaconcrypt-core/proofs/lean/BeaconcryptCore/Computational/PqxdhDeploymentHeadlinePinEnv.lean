-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish

/-!
# The pin lift, environment side: Server identity, pins, build responses and Beacon installs of the ideal environment (CE-12 P4 step 2, AG lift R1)

Support facts of the ideal environment of a target (`PqxdhDeploymentIdealEnv.idealStep` and `PqxdhDeploymentIdealEnv.envGD`) for every reply of every coin, BLAKE2b request and capability request (supports of the environment's `OracleComp (EnvEffects 2)` programs, which leave every reply free), as the lift of the b2s Server-pin row of design-v2 section 7.6 (R1) needs them:

- Every step keeps the environment's Server identity (`serverId`); the environment's pins (`pins`: every owner's pinned Server identity, in index order) follow the public transcript summary's owner update for the step's command and reply (a create appends the parsed pin, every other command keeps them); and a successful build reply is the Phase 2 writer output of fields carrying the Server identity (`PqxdhDeploymentEligibility.BuildShaped`). This is `PinMove`, proved for every command of the ideal step (`idealStep_move`) and of `envGD` (`envGD_move`) from the per-command facts `createPoolStep_pin`, `bundleStep_pin`, `acceptStep_pin`, `acceptSelectedEnv_pin` (the active selected accept's marker tail installs only games with the Server's identity: `tailCE_keeps`, `tail_keeps`, `acceptExposed_server`), `buildStep_pin` and `buildCachedEnv_pin` (the Phase 2 writer callback answers with the codec's writer: `build_wrote` for the native build, `genericBuild_wrote` and `freeBuild_wrote` for the factored hidden build of the marked session), `finishStep_pin`, `finishChallengeEnv_pin` and `hmacStep_pin`.
- Every Beacon install that a step issues carries the extracted associated data of the addressed owner's pinned Server identity and some Beacon identity (`InstallOk`). A finish establishes an owner only after the outer pin check of the source commit `PqxdhBeaconPhase2Publication.finish` (Rust `beacon_prepare_finish` and `finish_registration`, `beaconcrypt-core/src/pqxdh.rs`), with the associated data `build_associated_data(expected Server identity, Beacon identity)` of the `InitSent` control (`associatedData_array`, `finish_pin`, `owner_pin`, `finishSplitFwd_for`, `groupEnv_ok`). Stated as the query bound `IsQueryBoundP (badInstall e) 0` of every step (`idealStep_ok`, `envGD_ok`).
- `envGD_start`: every startup outcome of `envGD` holds the constructed Server's identity and no owner.

These are support facts of the environment program; they use no codec law, charge nothing and make no security claim. No `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhDeploymentEnvironment (EnvState strip stripOwner coins)
open PqxdhRecordLiftInterface (EnvEffects Capability)

variable {KemSK : Type}

/-! ### Pins and associated data -/

/-- The extracted associated-data builder on an `InitSent` control's expected Server identity and Beacon identity is `RawCtxServerRouting.associatedArray` of the two. -/
theorem associatedData_array (control : pqxdh.BeaconInitSent) :
    PqxdhBeaconPhase2Shared.associatedData control = RawCtxServerRouting.associatedArray
      control.expected_server_binding.identity_public_key control.beacon_identity_public_key :=
  RustM.ok.inj ((BeaconcryptCore.PanicFreedom.build_associated_data_ok control.expected_server_binding.identity_public_key
    control.beacon_identity_public_key).choose_spec.symm.trans (RawCtxServerRouting.associatedArray_exact _ _))

/-- An owner that ends established from a phase that was not established carries the extracted associated data of its pinned Server identity and some Beacon identity. -/
def InstallPin (before after : PqxdhRegistrationSchedule.Owner KemSK) : Prop :=
  ∀ control associatedData kernel, after.beacon.phase = .established control associatedData kernel →
    ¬ RawCtxBeaconLifecycle.Established before.beacon.phase →
      ∃ beacon, associatedData = RawCtxServerRouting.associatedArray before.beacon.serverIdentity beacon

/-- An owner left unchanged satisfies the install pin. -/
theorem installPin_refl (owner : PqxdhRegistrationSchedule.Owner KemSK) : InstallPin owner owner := by
  intro control associatedData kernel established inactive
  exact absurd (by rw [established]; trivial) inactive

/-- An owner that does not end established satisfies the install pin. -/
theorem installPin_inactive (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (inactive : ¬ RawCtxBeaconLifecycle.Established after.beacon.phase) : InstallPin before after := by
  intro control associatedData kernel established
  exact absurd (by rw [established]; trivial) inactive

/-- A staged registration that carries an `InitSent` control's expected Server binding and associated data. -/
def StagedFor (control : pqxdh.BeaconInitSent) (staged : Option PqxdhBeaconPhase2Publication.Staged) : Prop :=
  ∀ value, staged = some value → value.authenticated.candidate.server_binding = control.expected_server_binding ∧
    value.associatedData = PqxdhBeaconPhase2Shared.associatedData control

/-- The source commit of a Beacon finish keeps the pinned Server identity and, on a staged registration for the control, satisfies the install pin: a success passed the outer pin check, so the expected Server identity is the pin, and the associated data is the builder's output on it. -/
theorem finish_pin (control : pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) (stagedFor : StagedFor control staged) :
    (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.serverIdentity = before.beacon.serverIdentity ∧
      InstallPin before (PqxdhBeaconPhase2Publication.finish control before staged).2 := by
  rcases staged with _ | value
  · exact ⟨rfl, installPin_inactive _ _ (by simp [PqxdhBeaconPhase2Publication.finish,
      PqxdhBeaconPhase2Preparation.abort, RawCtxBeaconLifecycle.Established])⟩
  · obtain ⟨binding, adEq⟩ := stagedFor value rfl
    unfold PqxdhBeaconPhase2Publication.finish
    dsimp only
    split_ifs with keyDiffer identityDiffer
    · exact ⟨rfl, installPin_inactive _ _ (by simp [PqxdhBeaconPhase2Preparation.abort,
        RawCtxBeaconLifecycle.Established])⟩
    · exact ⟨rfl, installPin_inactive _ _ (by simp [PqxdhBeaconPhase2Preparation.abort,
        RawCtxBeaconLifecycle.Established])⟩
    · refine ⟨rfl, fun control' associatedData kernel established _ => ?_⟩
      simp only [PqxdhBeaconPhase2Publication.publish, RawCtxBeaconLifecycle.Phase.established.injEq] at established
      obtain ⟨_, rfl, _⟩ := established
      have pinned : before.beacon.serverIdentity = control.expected_server_binding.identity_public_key := by
        rw [← binding]
        exact Subtype.ext ((absBytes_inj_iff _ _).mp (not_ne_iff.mp identityDiffer))
      exact ⟨control.beacon_identity_public_key, by rw [adEq, associatedData_array, pinned]⟩


/-- The source commit of a Beacon finish keeps the pinned Server identity, on every staged result. -/
theorem finish_serverIdentity (control : pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.serverIdentity = before.beacon.serverIdentity := by
  rcases staged with _ | value
  · rfl
  · unfold PqxdhBeaconPhase2Publication.finish
    dsimp only
    split_ifs <;> rfl

/-- The candidate of every successful source preparation, for any callback replies, carries the control's expected Server binding and associated data. -/
theorem prepare_candidate {I D K X Response : Type} (control : pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D)
    (kem : K) (raw : Pqxdh.Bytes) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (member : some prepared ∈ support (PqxdhBeaconPhase2Preparation.prepare (X := X) control identity prekey oneTime kem
      raw)) :
    prepared.candidate.server_binding = control.expected_server_binding ∧
      prepared.candidate.associated_data = PqxdhBeaconPhase2Shared.associatedData control := by
  unfold PqxdhBeaconPhase2Preparation.prepare at member
  rw [mem_support_bind_iff] at member
  obtain ⟨inputs, -, member⟩ := member
  rcases inputs with _ | inputs
  · simp at member
  · unfold PqxdhBeaconPhase2Preparation.afterInputs at member
    rw [mem_support_bind_iff] at member
    obtain ⟨_, -, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    cases actual : PqxdhBeaconPhase2Preparation.normalPrepare control inputs.finishInputs with
    | Err _ =>
        rw [actual] at member
        cases member
    | Ok candidate =>
        rw [actual] at member
        simp only [Option.some.injEq] at member
        subst member
        obtain ⟨binding, _, ad⟩ := PqxdhDeploymentCompileFootprint.prepare_finish_fields control inputs.finishInputs
          candidate ((PqxdhBeaconPhase2Preparation.normalPrepare_exact _ _).trans (congrArg ok actual))
        exact ⟨binding, ad⟩

/-- Every staged outcome of the native root continuation, for any replies, is an opening of the cleared prepared candidate. -/
theorem tail_staged {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (staged : PqxdhBeaconPhase2Publication.Staged)
    (member : some staged ∈ support (PqxdhBeaconPhase2Publication.tail decode prepared)) :
    ∃ kernel reply, PqxdhBeaconPhase2Publication.afterOpening
      (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate) kernel reply = some staged := by
  unfold PqxdhBeaconPhase2Publication.tail at member
  rw [mem_support_bind_iff] at member
  obtain ⟨root, -, member⟩ := member
  rcases root with _ | root
  · simp at member
  · unfold PqxdhBeaconPhase2Publication.afterRoot at member
    rw [mem_support_bind_iff] at member
    obtain ⟨_, -, member⟩ := member
    rw [mem_support_bind_iff] at member
    obtain ⟨raw, -, member⟩ := member
    rcases raw with _ | raw
    · simp at member
    · rw [mem_support_bind_iff] at member
      obtain ⟨result, -, member⟩ := member
      rw [support_pure, Set.mem_singleton_iff] at member
      exact ⟨_, _, member.symm⟩

/-- An opening of a candidate that carries the control's expected binding and associated data is a staged registration for the control. -/
theorem opened_for (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (binding : candidate.server_binding = control.expected_server_binding)
    (ad : candidate.associated_data = PqxdhBeaconPhase2Shared.associatedData control)
    (kernel : ConcreteRatchetKernel) (reply : core.option.Option RawCtxWholeOwner.Decrypted)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (opened : PqxdhBeaconPhase2Publication.afterOpening candidate kernel reply = some staged) :
    staged.authenticated.candidate.server_binding = control.expected_server_binding ∧
      staged.associatedData = PqxdhBeaconPhase2Shared.associatedData control := by
  obtain ⟨candidateEq, adEq⟩ := PqxdhDeploymentIdealPostGoodFinish.staged_opening _ kernel reply staged opened
  exact ⟨by rw [candidateEq]; exact binding, by rw [adEq]; exact ad⟩

/-- Every outcome of the original Phase 2 API, for any callback replies, keeps the pinned Server identity and satisfies the install pin. -/
theorem owner_pin {Response : Type} (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (before : PqxdhRegistrationSchedule.Owner KemSK) :
    ∀ result ∈ support (PqxdhBeaconPhase2Publication.owner (X := PqxdhJointIdentity.IdentitySeed) (Response := Response)
      decode raw before),
      result.2.beacon.serverIdentity = before.beacon.serverIdentity ∧ InstallPin before result.2 := by
  intro result member
  unfold PqxdhBeaconPhase2Publication.owner at member
  split at member
  · rename_i control prekey oneTime kem phase
    rw [mem_support_bind_iff] at member
    obtain ⟨prepared, preparedMember, rest⟩ := member
    have sourced := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ preparedMember
    cases prepared with
    | none =>
        rw [support_pure, Set.mem_singleton_iff] at rest
        subst rest
        exact finish_pin control before none (fun _ found => by cases found)
    | some prepared =>
        rw [mem_support_bind_iff] at rest
        obtain ⟨staged, stagedMember, final⟩ := rest
        rw [support_pure, Set.mem_singleton_iff] at final
        subst final
        refine finish_pin control before staged fun value found => ?_
        subst found
        obtain ⟨kernel, reply, opened⟩ := tail_staged decode prepared value
          (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ stagedMember)
        obtain ⟨binding, ad⟩ := prepare_candidate control _ _ _ _ raw prepared sourced
        exact opened_for control _ ((PqxdhBeaconPhase2Publication.clearedCandidate_fields _).1.trans binding)
          ((PqxdhBeaconPhase2Publication.clearedCandidate_fields _).2.2.1.trans ad) kernel reply value opened
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, installPin_refl _⟩

/-- Every outcome of the native-shaped Phase 2 program, for any callback replies, keeps the pinned Server identity and satisfies the install pin. -/
theorem nativeOwner_pin {Response : Type} (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (before : PqxdhRegistrationSchedule.Owner KemSK) :
    ∀ result ∈ support (PqxdhBeaconPhase2Publication.nativeOwner (X := PqxdhJointIdentity.IdentitySeed)
      (Response := Response) decode raw before),
      result.2.beacon.serverIdentity = before.beacon.serverIdentity ∧ InstallPin before result.2 :=
  fun result member => owner_pin decode raw before result
    (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member)


/-! ### Environment states -/

section Env
variable {Bk : Type} {n : ℕ}

/-- The pins of an environment state: every owner's pinned Server identity, in index order. -/
def pins (e : EnvState KemSK Bk) : List PqxdhBeaconPhase2Preparation.Word32 :=
  e.native.owners.map fun owner => owner.beacon.serverIdentity

/-- The Server identity of an environment state. -/
def serverId (e : EnvState KemSK Bk) : RawCtxServerRouting.Identity := e.native.shared.2.server.server.identity

/-- A capability request is admissible at an environment state: a Beacon install carries the extracted associated data of the addressed owner's pinned Server identity and some Beacon identity; every other request is admissible. -/
def InstallOk (e : EnvState KemSK Bk) : (EnvEffects n).Domain → Prop
  | .inr (.installBeacon owner shell _) => ∃ before, e.native.owners[owner]? = some before ∧
      ∃ beacon, shell.associatedData = RawCtxServerRouting.associatedArray before.beacon.serverIdentity beacon
  | _ => True

open Classical in
/-- An inadmissible request, as a Boolean. -/
noncomputable def badInstall (e : EnvState KemSK Bk) (query : (EnvEffects n).Domain) : Bool :=
  decide (¬ InstallOk e query)

open Classical in
/-- A request is inadmissible exactly when it is not admissible. -/
theorem badInstall_iff (e : EnvState KemSK Bk) (query : (EnvEffects n).Domain) :
    badInstall e query = true ↔ ¬ InstallOk e query := by
  unfold badInstall
  exact decide_eq_true_iff

/-- An inadmissible request is an administrative effect. -/
theorem badInstall_admin (e : EnvState KemSK Bk) (query : (EnvEffects n).Domain) (bad : badInstall e query = true) :
    PqxdhRecordLiftInterface.effectKind query = .administrative := by
  rcases query with coin | capability
  · simp [badInstall, InstallOk] at bad
  · cases capability with
    | hash bytes => simp [badInstall, InstallOk] at bad
    | _ => rfl

/-- A program without administrative effect has no inadmissible request. -/
theorem ok_of_noAdmin {α : Type} (e : EnvState KemSK Bk) (work : OracleComp (EnvEffects n) α)
    (noAdmin : work.IsQueryBoundP (fun effect => PqxdhRecordLiftInterface.effectKind effect = .administrative) 0) :
    work.IsQueryBoundP (fun effect => badInstall e effect = true) 0 :=
  IsQueryBoundP.of_imp (fun query bad => badInstall_admin e query bad) noAdmin

/-- Coins have no inadmissible request. -/
theorem coins_ok {α : Type} (e : EnvState KemSK Bk) (work : ProbComp α) :
    (coins (n := n) work).IsQueryBoundP (fun effect => badInstall e effect = true) 0 :=
  ok_of_noAdmin e _ (PqxdhDeploymentEnvironmentReal.coins_noAdmin work)

/-- An admissible capability request issues no inadmissible request. -/
theorem issue_ok (e : EnvState KemSK Bk) (capability : Capability n) (ok : InstallOk e (.inr capability)) :
    (PqxdhDeploymentEnvironment.issue capability).IsQueryBoundP (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.issue PqxdhDeploymentEnvironment.request
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl fun bad => ?_, fun _ => trivial⟩
  simp only [badInstall, decide_eq_true_eq] at bad
  exact bad ok

/-- Publishing an owner's change with the install pin issues no inadmissible request. -/
theorem ownerEffect_ok (e : EnvState KemSK Bk) (index : ℕ) (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (found : e.native.owners[index]? = some before) (pinned : InstallPin before after) :
    (PqxdhDeploymentEnvironment.ownerEffect (n := n) index before after).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.ownerEffect
  split
  · trivial
  · rename_i previous control associatedData kernel afterPhase notEstablished
    refine issue_ok e _ ⟨before, found, pinned control associatedData kernel afterPhase fun established => ?_⟩
    cases phase : before.beacon.phase with
    | established c a k => exact notEstablished c a k phase
    | _ => simp [phase, RawCtxBeaconLifecycle.Established] at established
  · split
    · split
      · trivial
      · exact issue_ok e _ trivial
    · trivial

/-- Publishing a hidden owner's change with the install pin issues no inadmissible request. -/
theorem hiddenOwnerEffect_ok (e : EnvState KemSK Bk) (slot : PqxdhRecordLiftInterface.Slot n) (index : ℕ)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) (found : e.native.owners[index]? = some before)
    (pinned : InstallPin before after) :
    (PqxdhDeploymentEnvironment.hiddenOwnerEffect slot index before after).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.hiddenOwnerEffect
  split
  · trivial
  · rename_i previous control associatedData kernel afterPhase notEstablished
    refine issue_ok e _ ⟨before, found, pinned control associatedData kernel afterPhase fun established => ?_⟩
    cases phase : before.beacon.phase with
    | established c a k => exact notEstablished c a k phase
    | _ => simp [phase, RawCtxBeaconLifecycle.Established] at established
  · split
    · split
      · trivial
      · exact issue_ok e _ trivial
    · trivial

/-- Stripping keeps every owner's pin. -/
theorem strip_pins (state : PqxdhRegistrationSchedule.State KemSK) :
    (strip state).owners.map (fun owner => owner.beacon.serverIdentity) =
      state.owners.map fun owner => owner.beacon.serverIdentity := by
  simp only [strip, List.map_map]
  congr 1
  funext owner
  show (stripOwner owner).beacon.serverIdentity = owner.beacon.serverIdentity
  unfold stripOwner
  split <;> rfl

/-- Replacing an owner by one with the same pin keeps the pins. -/
theorem pins_set (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) (found : owners[index]? = some before)
    (same : after.beacon.serverIdentity = before.beacon.serverIdentity) :
    (owners.set index after).map (fun owner => owner.beacon.serverIdentity) =
      owners.map fun owner => owner.beacon.serverIdentity := by
  rw [List.map_set, same]
  have below := (List.getElem?_eq_some_iff.mp found).1
  have value := (List.getElem?_eq_some_iff.mp found).2
  apply List.ext_getElem (by simp)
  intro i first second
  by_cases equal : i = index
  · subst equal
    simp [value]
  · simp [Ne.symm equal]

end Env


/-! ### The finish steps -/

section Finish
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {Bk : Type} {n : ℕ}

/-- The real finish keeps the Server identity and the pins. -/
theorem finishStep_pin (owner : ℕ) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.finishStep (n := n) setup codec owner raw).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  unfold PqxdhDeploymentEnvironment.finishStep at member
  simp only [StateT.run] at member
  split at member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩
  · rename_i before owned
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨result, resultMember, _, _, rfl⟩ := member
    have game := PqxdhDeploymentEnvironmentReal.finishFwd_game setup codec _ _ result resultMember
    have pinned := nativeOwner_pin codec.frameRead raw before result.1
      (PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ resultMember)
    refine ⟨?_, ?_⟩
    · show result.2.2.server.server.identity = e.native.shared.2.server.server.identity
      rw [game]
    · unfold pins
      rw [strip_pins]
      exact pins_set _ owner before _ owned pinned.1

/-- The real finish issues no inadmissible request. -/
theorem finishStep_ok (owner : ℕ) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ((PqxdhDeploymentEnvironment.finishStep (n := n) setup codec owner raw).run e).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.finishStep
  simp only [StateT.run]
  split
  · trivial
  · rename_i before owned
    rw [show (0 : ℕ) = 0 + 0 from rfl]
    refine isQueryBoundP_bind (ok_of_noAdmin e _ (PqxdhDeploymentEnvironmentReal.finishFwd_noAdmin setup codec _ _))
      fun result member => ?_
    rw [show (0 : ℕ) = 0 + 0 from rfl]
    exact isQueryBoundP_bind (ownerEffect_ok e owner before result.1.2 owned
      (nativeOwner_pin codec.frameRead raw before result.1
        (PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member)).2) fun _ _ => trivial

end Finish


/-! ### Owner k's challenge finish -/

section Challenge
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count n : ℕ}
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentIdealEnvFinish (commitEnv groupEnv finishedEnv finishChallengeEnv)

/-- The environment state after a challenge finish keeps the Server identity when the Server's game is kept, and the pins when the owner keeps its pin. -/
theorem finishedEnv_pin (e : EnvState KemSK SplitBk) (owner : ℕ) (shared : PqxdhServerAuthNative.NativeState KemSK)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) (backend : SplitBk) (owned : e.native.owners[owner]? = some before)
    (same : after.beacon.serverIdentity = before.beacon.serverIdentity) (game : shared.2 = e.native.shared.2) :
    serverId (finishedEnv e owner shared after backend) = serverId e ∧
      pins (finishedEnv e owner shared after backend) = pins e := by
  refine ⟨?_, ?_⟩
  · show shared.2.server.server.identity = e.native.shared.2.server.server.identity
    rw [game]
  · unfold pins finishedEnv
    dsimp only
    rw [strip_pins]
    exact pins_set _ owner before after owned same

/-- Every outcome of the source commit is the finished environment state. -/
theorem commitEnv_member (e : EnvState KemSK SplitBk) (owner : ℕ) (control : pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (shared : PqxdhServerAuthNative.NativeState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    ∀ v ∈ support (commitEnv e owner control before shared staged),
      v.2 = finishedEnv e owner shared (PqxdhBeaconPhase2Publication.finish control before staged).2 e.backend := by
  intro v member
  unfold commitEnv at member
  rw [mem_support_bind_iff] at member
  obtain ⟨_, _, member⟩ := member
  rw [support_pure, Set.mem_singleton_iff] at member
  subst member
  rfl

/-- The source commit of a staged registration for the control issues no inadmissible request. -/
theorem commitEnv_ok (e : EnvState KemSK SplitBk) (owner : ℕ) (control : pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (owned : e.native.owners[owner]? = some before)
    (shared : PqxdhServerAuthNative.NativeState KemSK) (staged : Option PqxdhBeaconPhase2Publication.Staged)
    (stagedFor : StagedFor control staged) :
    (commitEnv e owner control before shared staged).IsQueryBoundP (fun effect => badInstall e effect = true) 0 := by
  unfold commitEnv
  rw [show (0 : ℕ) = 0 + 0 from rfl]
  exact isQueryBoundP_bind (ownerEffect_ok e owner before _ owned (finish_pin control before staged stagedFor).2)
    fun _ _ => trivial

/-- The cleared metadata candidate carries the metadata's binding and associated data. -/
theorem clearedMetadata_fields (metadata : PqxdhBeaconPhase2Shared.Metadata) :
    (PqxdhBeaconPhase2Publication.clearedCandidate (PqxdhBeaconPhase2Shared.clearedMetadata metadata)).server_binding =
        metadata.binding ∧
      (PqxdhBeaconPhase2Publication.clearedCandidate (PqxdhBeaconPhase2Shared.clearedMetadata metadata)).associated_data =
        metadata.associatedData :=
  ⟨rfl, rfl⟩

/-- Every staged outcome of the forwarded split hidden finish of a pending finish whose metadata is the control's expected binding and associated data is a staged registration for the control. -/
theorem finishSplitFwd_for (material : PqxdhDeploymentHiddenLayout.Material) (control : pqxdh.BeaconInitSent)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (binding : pending.metadata.binding = control.expected_server_binding)
    (ad : pending.metadata.associatedData = PqxdhBeaconPhase2Shared.associatedData control) :
    ∀ staged ∈ support (PqxdhDeploymentEnvironment.finishSplitFwd (n := n) setup codec material pending),
      StagedFor control staged := by
  intro staged member value found
  unfold PqxdhDeploymentEnvironment.finishSplitFwd at member
  have inner := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member
  rw [support_map] at inner
  obtain ⟨y, yMember, rfl⟩ := inner
  rw [support_map] at yMember
  obtain ⟨z, zMember, rfl⟩ := yMember
  obtain ⟨value0, found0, rfl⟩ := Option.map_eq_some_iff.mp found
  unfold PqxdhDeploymentHiddenKernels.finishErased at zMember
  rw [mem_support_bind_iff] at zMember
  obtain ⟨raw, -, zMember⟩ := zMember
  rcases raw with _ | raw
  · simp only [support_pure, Set.mem_singleton_iff] at zMember
    subst zMember
    cases found0
  · dsimp only at zMember
    split_ifs at zMember
    · rw [support_map] at zMember
      obtain ⟨w, wMember, rfl⟩ := zMember
      unfold PqxdhDeploymentHiddenKernels.factoredBody at wMember
      rw [mem_support_bind_iff] at wMember
      obtain ⟨result, -, wMember⟩ := wMember
      rw [support_pure, Set.mem_singleton_iff] at wMember
      subst wMember
      have opened := opened_for control _
        ((clearedMetadata_fields pending.metadata).1.trans binding)
        ((clearedMetadata_fields pending.metadata).2.trans ad) _ _ value0 found0
      exact opened
    · simp only [support_pure, Set.mem_singleton_iff] at zMember
      subst zMember
      cases found0

/-- The private root of a marked finish keeps the Server's game. -/
theorem markedRoot_game (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (secrets : PqxdhRegistrationJointBeaconOpaqueFinish.Secrets) (s : PqxdhServerAuthNative.NativeState KemSK) :
    ∀ r ∈ support ((PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot (KemSK := KemSK) hmac candidate secrets).run s),
      r.2.2 = s.2 := by
  intro r member
  unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot at member
  split at member
  · simp only [PqxdhServerAuthNative.sourceRoot, StateT.run, support_map, Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl

/-- Every outcome of the grouped finish request is a finished environment state with the Server's game kept. -/
theorem groupEnv_member (owner : ℕ) (control : pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (e : EnvState KemSK SplitBk) (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response) :
    ∀ v ∈ support (groupEnv setup codec owner control before e pending),
      ∃ shared staged backend, shared.2 = e.native.shared.2 ∧
        v.2 = finishedEnv e owner shared (PqxdhBeaconPhase2Publication.finish control before staged).2 backend := by
  intro v member
  unfold groupEnv at member
  split at member
  · split_ifs at member
    · rw [mem_support_bind_iff] at member
      obtain ⟨read, -, member⟩ := member
      split at member
      · rw [support_map] at member
        obtain ⟨committed, committedMember, rfl⟩ := member
        unfold PqxdhDeploymentEnvironment.finishSplitEnv at committedMember
        rw [mem_support_bind_iff] at committedMember
        obtain ⟨staged, -, committedMember⟩ := committedMember
        rw [mem_support_bind_iff] at committedMember
        obtain ⟨_, -, committedMember⟩ := committedMember
        rw [support_pure, Set.mem_singleton_iff] at committedMember
        subst committedMember
        exact ⟨e.native.shared, staged, _, rfl, rfl⟩
      · exact ⟨e.native.shared, none, e.backend, rfl, commitEnv_member e owner control before _ none v member⟩
    · exact ⟨e.native.shared, none, e.backend, rfl, commitEnv_member e owner control before _ none v member⟩
  · rw [mem_support_bind_iff] at member
    obtain ⟨r, rMember, member⟩ := member
    have game := markedRoot_game setup.hmac _ pending.root e.native.shared r
      (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember)
    split at member
    · exact ⟨r.2, none, e.backend, game, commitEnv_member e owner control before _ none v member⟩
    · rw [mem_support_bind_iff] at member
      obtain ⟨staged, -, member⟩ := member
      exact ⟨r.2, staged, e.backend, game, commitEnv_member e owner control before _ staged v member⟩

/-- The grouped finish request of a pending finish whose metadata is the control's expected binding and associated data issues no inadmissible request. -/
theorem groupEnv_ok (owner : ℕ) (control : pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (e : EnvState KemSK SplitBk) (owned : e.native.owners[owner]? = some before)
    (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (binding : pending.metadata.binding = control.expected_server_binding)
    (ad : pending.metadata.associatedData = PqxdhBeaconPhase2Shared.associatedData control) :
    (groupEnv setup codec owner control before e pending).IsQueryBoundP (fun effect => badInstall e effect = true) 0 := by
  unfold groupEnv
  split
  · split_ifs
    · rw [show (0 : ℕ) = 0 + 0 from rfl]
      refine isQueryBoundP_bind (coins_ok e _) fun read _ => ?_
      split
      · rw [isQueryBoundP_map_iff]
        unfold PqxdhDeploymentEnvironment.finishSplitEnv
        rw [show (0 : ℕ) = 0 + 0 from rfl]
        refine isQueryBoundP_bind (ok_of_noAdmin e _ (PqxdhDeploymentIdealEnvFinish.finishSplitFwd_noAdmin setup codec _ _))
          fun staged stagedMember => ?_
        rw [show (0 : ℕ) = 0 + 0 from rfl]
        exact isQueryBoundP_bind (hiddenOwnerEffect_ok e _ owner before _ owned (finish_pin control before staged
          (finishSplitFwd_for setup codec _ control _ binding ad staged stagedMember)).2) fun _ _ => trivial
      · exact commitEnv_ok e owner control before owned _ none fun _ found => by cases found
    · exact commitEnv_ok e owner control before owned _ none fun _ found => by cases found
  · rw [show (0 : ℕ) = 0 + 0 from rfl]
    refine isQueryBoundP_bind (coins_ok e _) fun r _ => ?_
    split
    · exact commitEnv_ok e owner control before owned _ none fun _ found => by cases found
    · rename_i root _
      rw [show (0 : ℕ) = 0 + 0 from rfl]
      refine isQueryBoundP_bind (ok_of_noAdmin e _ (PqxdhDeploymentIdealEnvFinish.knownFwd_noAdmin setup codec _))
        fun staged stagedMember => ?_
      refine commitEnv_ok e owner control before owned _ staged fun value found => ?_
      obtain ⟨kernel, reply, opened⟩ := PqxdhDeploymentIdealPostGoodFinish.afterRoot_opening codec.frameRead pending root
        staged (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ stagedMember) value found
      exact opened_for control _ ((clearedMetadata_fields pending.metadata).1.trans binding)
        ((clearedMetadata_fields pending.metadata).2.trans ad) kernel reply value opened

/-- Owner k's challenge finish keeps the Server identity and the pins. -/
theorem finishChallengeEnv_pin (p : PqxdhDeploymentIdealParams.Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes)
    (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((finishChallengeEnv setup codec p owner raw).run e), serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  change v ∈ support (finishChallengeEnv setup codec p owner raw e) at member
  unfold finishChallengeEnv at member
  split at member
  · rename_i before owned
    split at member
    · rename_i control prekey oneTime kem phase
      rw [mem_support_bind_iff] at member
      obtain ⟨prepared, -, member⟩ := member
      split at member
      · rw [commitEnv_member e owner control before _ none v member]
        exact finishedEnv_pin e owner _ before _ _ owned (finish_serverIdentity control before none) rfl
      · rename_i pending
        obtain ⟨shared, staged, backend, game, same⟩ := groupEnv_member setup codec owner control before e pending v member
        rw [same]
        exact finishedEnv_pin e owner shared before _ backend owned (finish_serverIdentity control before staged) game
    · simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩

/-- Owner k's challenge finish issues no inadmissible request. -/
theorem finishChallengeEnv_ok (p : PqxdhDeploymentIdealParams.Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes)
    (e : EnvState KemSK SplitBk) :
    ((finishChallengeEnv setup codec p owner raw).run e).IsQueryBoundP (fun effect => badInstall e effect = true) 0 := by
  change (finishChallengeEnv setup codec p owner raw e).IsQueryBoundP _ 0
  unfold finishChallengeEnv
  split
  · rename_i before owned
    split
    · rename_i control prekey oneTime kem phase
      rw [show (0 : ℕ) = 0 + 0 from rfl]
      refine isQueryBoundP_bind (coins_ok e _) fun prepared preparedMember => ?_
      split
      · exact commitEnv_ok e owner control before owned _ none fun _ found => by cases found
      · rename_i pending
        obtain ⟨_, _, metadata⟩ := PqxdhDeploymentIdealPostGoodFinish.prepareCE_facts setup codec p.challenge control
          before.beacon.identity prekey oneTime kem raw pending
          (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ preparedMember)
        exact groupEnv_ok setup codec owner control before e owned pending (by rw [metadata]) (by rw [metadata])
    · trivial
  · trivial

end Challenge


/-! ### The other registration steps -/

section Steps
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {Bk : Type} {n : ℕ}

/-- A Phase 1 bundle keeps the owner's pin and satisfies the install pin. -/
theorem bundled_pin (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (shape : PqxdhDeploymentEnvironmentReal.Bundled before after) :
    after.beacon.serverIdentity = before.beacon.serverIdentity ∧ InstallPin before after := by
  rcases shape with rfl | ⟨⟨control, prekey, oneTime, kem, rfl⟩, _⟩
  · exact ⟨rfl, installPin_refl _⟩
  · exact ⟨rfl, installPin_inactive _ _ (by simp [RawCtxBeaconLifecycle.Established])⟩

/-- The real bundle keeps the Server identity and the pins. -/
theorem bundleStep_pin (owner : ℕ) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.bundleStep (n := n) setup codec owner).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  unfold PqxdhDeploymentEnvironment.bundleStep at member
  simp only [StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨r, rMember, _, _, rfl⟩ := member
  have inner : r ∈ support ((PqxdhRegistrationSchedule.bundle setup codec owner).run e.native) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  cases owned : e.native.owners[owner]? with
  | none =>
      rw [PqxdhDeploymentEnvironmentReal.bundle_run_missing setup codec owner _ owned, support_pure,
        Set.mem_singleton_iff] at inner
      subst inner
      exact ⟨rfl, by unfold pins; exact strip_pins _⟩
  | some current =>
      rw [PqxdhDeploymentEnvironmentReal.bundle_run_found setup codec owner _ current owned, support_map] at inner
      obtain ⟨b, bMember, rfl⟩ := inner
      have shape := PqxdhDeploymentEnvironmentReal.bundle_shape _ current b
        (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ bMember)
      refine ⟨rfl, ?_⟩
      unfold pins
      rw [strip_pins]
      exact pins_set _ owner current b.2 owned (bundled_pin current b.2 shape).1

/-- The real bundle issues no inadmissible request. -/
theorem bundleStep_ok (owner : ℕ) (e : EnvState KemSK Bk) :
    ((PqxdhDeploymentEnvironment.bundleStep (n := n) setup codec owner).run e).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.bundleStep
  simp only [StateT.run]
  rw [show (0 : ℕ) = 0 + 0 from rfl]
  refine isQueryBoundP_bind (coins_ok e _) fun r rMember => ?_
  rw [show (0 : ℕ) = 0 + 0 from rfl]
  refine isQueryBoundP_bind ?_ fun _ _ => trivial
  have inner : r ∈ support ((PqxdhRegistrationSchedule.bundle setup codec owner).run e.native) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  unfold PqxdhDeploymentEnvironment.ownerChange
  cases owned : e.native.owners[owner]? with
  | none => trivial
  | some current =>
      rw [PqxdhDeploymentEnvironmentReal.bundle_run_found setup codec owner _ current owned, support_map] at inner
      obtain ⟨b, bMember, rfl⟩ := inner
      have shape := PqxdhDeploymentEnvironmentReal.bundle_shape _ current b
        (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ bMember)
      have below := (List.getElem?_eq_some_iff.mp owned).1
      simp only [List.getElem?_set_self below]
      exact ownerEffect_ok e owner current b.2 owned (bundled_pin current b.2 shape).2

/-- The native logged accept keeps the Server's peer map, identity and metadata. -/
theorem acceptLogged_server (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes)
    (shared : PqxdhServerAuthNative.NativeState KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run shared),
      result.2.2.server.server = shared.2.server.server := by
  intro result supported
  have native : ((result.1.1, result.2) : Option ℕ × PqxdhServerAuthNative.NativeState KemSK) ∈ support
      ((PqxdhServerAuthNative.nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run
        shared) := by
    rw [← PqxdhDeploymentLaterServerNative.acceptLogged_fst, support_map]
    exact ⟨result, supported, rfl⟩
  rw [← PqxdhServerAuthNative.accept_native] at native
  have inner := PqxdhServerAuthNative.evaluate_support setup seed _ _ shared _ native
  exact (PqxdhDeploymentCompileFootprint.accept_footprint setup codec checks _ raw shared.2 _ inner).1

/-- The real accept keeps the Server identity and the pins and issues no inadmissible request. -/
theorem acceptStep_pin (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.acceptStep (n := n) setup codec checks raw).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  unfold PqxdhDeploymentEnvironment.acceptStep at member
  simp only [StateT.run, support_map, Set.mem_image] at member
  obtain ⟨r, rMember, rfl⟩ := member
  have inner : r ∈ support ((PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup
      codec checks e.created.seed raw)).run e.native) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  rw [PqxdhDeploymentEnvironmentReal.onShared_run, support_map] at inner
  obtain ⟨x, xMember, rfl⟩ := inner
  refine ⟨?_, by unfold pins; exact strip_pins _⟩
  show x.2.2.server.server.identity = e.native.shared.2.server.server.identity
  rw [acceptLogged_server setup codec checks e.created.seed raw e.native.shared x xMember]

/-- The real accept issues no inadmissible request. -/
theorem acceptStep_ok (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ((PqxdhDeploymentEnvironment.acceptStep (n := n) setup codec checks raw).run e).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.acceptStep
  change (_ <$> coins _).IsQueryBoundP _ 0
  rw [isQueryBoundP_map_iff]
  exact coins_ok e _

/-- The real public HMAC keeps the Server identity and the pins. -/
theorem hmacStep_pin (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.hmacStep (n := n) setup key message).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  unfold PqxdhDeploymentEnvironment.hmacStep PqxdhDeploymentEnvironment.onEnv at member
  simp only [StateT.run, support_map, Set.mem_image] at member
  obtain ⟨r, rMember, rfl⟩ := member
  have inner : r ∈ support ((PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeHmac setup e.created.seed
      PqxdhRegistrationSchedule.observationScalar key message)).run e.native) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  rw [PqxdhDeploymentEnvironmentReal.onShared_run, support_map] at inner
  obtain ⟨x, xMember, rfl⟩ := inner
  rw [← PqxdhServerAuthNative.hmac_native] at xMember
  have evaluated := PqxdhServerAuthNative.evaluate_support setup e.created.seed _ _ e.native.shared x xMember
  have fixed := PqxdhDeploymentCompileFootprint.hmac_fixed key message e.native.shared.2 _ evaluated
  refine ⟨?_, by unfold pins; exact strip_pins _⟩
  show x.2.2.server.server.identity = e.native.shared.2.server.server.identity
  rw [fixed.1]

/-- The real public HMAC issues no inadmissible request. -/
theorem hmacStep_ok (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ((PqxdhDeploymentEnvironment.hmacStep (n := n) setup key message).run e).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.hmacStep PqxdhDeploymentEnvironment.onEnv
  change (_ <$> coins _).IsQueryBoundP _ 0
  rw [isQueryBoundP_map_iff]
  exact coins_ok e _

end Steps


/-! ### The pool create and the selected accept -/

section Ideal
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ} {Bk : Type} {n : ℕ}
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentIdealSlots (SlotSpec Coord)

/-- The pool create keeps the Server identity; it either returns nothing and keeps the pins, or parses the pin and appends it to the pins. -/
theorem createPoolStep_pin (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := n) setup pool pin keyId).run e),
      serverId v.2 = serverId e ∧ ((v.1 = none ∧ pins v.2 = pins e) ∨
        ∃ word index, PqxdhDeploymentInterface.parsePin pin = some word ∧ v.1 = some index ∧
          pins v.2 = pins e ++ [word]) := by
  intro v member
  unfold PqxdhDeploymentIdealEnvReal.createPoolStep at member
  split at member
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rename_i word parsed
    rw [StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨r, rMember, member⟩ := member
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    simp only [PqxdhDeploymentEnvironment.onEnv, StateT.run, support_map, Set.mem_image] at rMember
    obtain ⟨x, xMember, rfl⟩ := rMember
    have inner : x ∈ support ((PqxdhDeploymentIdealSteps.createPool setup pool word keyId).run e.native) :=
      PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ xMember
    rw [PqxdhDeploymentIdealEnvReal.createPool_run setup pool word keyId e.native] at inner
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at inner
    obtain ⟨_, _, _, _, _, _, rfl⟩ := inner
    refine ⟨rfl, Or.inr ⟨word, _, parsed, rfl, ?_⟩⟩
    unfold pins
    dsimp only
    rw [strip_pins]
    simp

/-- The pool create issues no inadmissible request. -/
theorem createPoolStep_ok (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (e : EnvState KemSK Bk) :
    ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := n) setup pool pin keyId).run e).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentIdealEnvReal.createPoolStep
  split
  · trivial
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
    rw [show (0 : ℕ) = 0 + 0 from rfl]
    refine isQueryBoundP_bind ?_ fun _ _ => ?_
    · change (_ <$> coins _).IsQueryBoundP _ 0
      rw [isQueryBoundP_map_iff]
      exact coins_ok e _
    · rw [show (0 : ℕ) = 0 + 0 from rfl]
      exact isQueryBoundP_bind (issue_ok e _ trivial) fun _ _ => trivial

/-- A marker-tail request other than an install of a game with another Server identity. -/
def TailKeeps (identity : RawCtxServerRouting.Identity) :
    (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain → Prop
  | .inr (.install game) => game.server.server.identity = identity
  | _ => True

open Classical in
/-- A marker-tail request that installs a game with another Server identity, as a Boolean. -/
noncomputable def tailBad (identity : RawCtxServerRouting.Identity)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain) : Bool :=
  decide (¬ TailKeeps identity query)

open Classical in
/-- A tail request is bad exactly when it installs a game with another Server identity. -/
theorem tailBad_iff (identity : RawCtxServerRouting.Identity)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain) :
    tailBad identity query = true ↔ ¬ TailKeeps identity query := by
  unfold tailBad
  exact decide_eq_true_iff

/-- Every step of the marker tail at an admissible request keeps the Server identity of the native state. -/
theorem tailCE_keeps (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (identity : RawCtxServerRouting.Identity)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain)
    (z : PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord)) (good : ¬ tailBad identity query = true)
    (holds : z.1.2.server.server.identity = identity) :
    ∀ r ∈ support ((PqxdhDeploymentIdealSteps.tailCE hmac index query).run z),
      r.2.1.2.server.server.identity = identity := by
  obtain ⟨s, mark⟩ := z
  intro r member
  rcases query with (input | aux) | mutation
  · cases shared : input.shared with
    | challenge =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared] at member
        rw [mem_support_bind_iff] at member
        obtain ⟨_, _, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact holds
    | known secret =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared] at member
        rw [support_map, PqxdhDeploymentIdealSteps.liftS, support_liftComp] at member
        obtain ⟨x, xMember, rfl⟩ := member
        change x ∈ support ((PqxdhRegistrationJointKemOpaqueClient.romRoot KemSK hmac index (List.Vector.replicate 32 0)
          input).run s) at xMember
        simp only [PqxdhRegistrationJointKemOpaqueClient.romRoot, PqxdhServerAuthNative.nativeTouch, StateT.run_bind,
          StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at xMember
        obtain ⟨root, rootMember, _, touched, rfl⟩ := xMember
        unfold PqxdhServerAuthNative.romRootBytes at rootMember
        simp only [StateT.run, support_map, Set.mem_image] at rootMember
        obtain ⟨_, _, rfl⟩ := rootMember
        simp only [PqxdhServerAuthNative.localState, StateT.run, support_pure, Set.mem_singleton_iff] at touched
        subst touched
        exact holds
  · simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run] at member
    rw [support_map, PqxdhDeploymentIdealSteps.liftS, support_liftComp] at member
    obtain ⟨x, xMember, rfl⟩ := member
    cases aux <;>
      simp [PqxdhRegistrationJointKemOpaqueClient.auxiliary, PqxdhServerAuthNative.nativeConsume,
        PqxdhServerAuthNative.localState] at xMember <;>
      subst xMember <;> exact holds
  · simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run] at member
    rw [support_map, PqxdhDeploymentIdealSteps.liftS, support_liftComp] at member
    obtain ⟨x, xMember, rfl⟩ := member
    cases mutation with
    | install game =>
        simp [PqxdhRegistrationJointKemOpaqueTail.mutation, PqxdhServerAuthNative.nativeSet,
          PqxdhServerAuthNative.localState] at xMember
        subst xMember
        by_contra differ
        exact good ((tailBad_iff _ _).2 differ)
    | publish at_ token =>
        simp [PqxdhRegistrationJointKemOpaqueTail.mutation, PqxdhServerAuthNative.nativeModify,
          PqxdhServerAuthNative.localState] at xMember
        subst xMember
        exact holds

/-- The marker tail on a game installs only games with that game's Server identity. -/
theorem tail_keeps (serverKeyId : Std.U64) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes) :
    (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected).IsQueryBoundP
      (fun query => tailBad state.server.server.identity query = true) 0 := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [tailBad, TailKeeps]), fun _ => ?_⟩
  simp only [tailBad, TailKeeps, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  split
  · trivial
  · rw [show (0 : ℕ) = 0 + 0 from rfl]
    refine isQueryBoundP_bind (IsQueryBoundP.simulateQ_of_step (p := fun _ => False)
      (isQueryBoundP_false _ _) (fun _ wrong => absurd wrong id) (fun query _ => ?_)) fun returned _ => ?_
    · exact (isQueryBoundP_query_iff _ _ _).2 (fun bad => by simp at bad)
    · split
      · rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp), fun _ => trivial⟩
      · trivial

/-- The selected accept with its encapsulation exposed keeps the Server identity, for any slot replies. -/
theorem acceptExposed_server (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (shared : PqxdhServerAuthNative.NativeState KemSK) :
    ∀ r ∈ support ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed chosen challenge raw).run shared),
      r.2.2.server.server.identity = shared.2.server.server.identity := by
  have inactive : ∀ r ∈ support ((PqxdhDeploymentIdealSteps.acceptInactive setup codec checks seed raw).run shared),
      r.2.2.server.server.identity = shared.2.server.server.identity := by
    intro r member
    change r ∈ support ((fun r : (Option ℕ × Option PqxdhJointGapDh.ScalarBytes) ×
      PqxdhServerAuthNative.NativeState KemSK => ((r.1, (false, none)), r.2)) <$>
      PqxdhDeploymentIdealSteps.liftS ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed
        raw).run shared)) at member
    rw [support_map, PqxdhDeploymentIdealSteps.liftS, support_liftComp] at member
    obtain ⟨x, xMember, rfl⟩ := member
    rw [acceptLogged_server setup codec checks seed raw shared x xMember]
  intro r member
  unfold PqxdhDeploymentIdealSteps.acceptExposed at member
  split at member
  · split_ifs at member
    · rename_i verified _ _
      change r ∈ support (PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified shared) at member
      unfold PqxdhDeploymentIdealSteps.acceptActive at member
      rw [mem_support_bind_iff] at member
      obtain ⟨pre, -, member⟩ := member
      split at member
      · rw [mem_support_bind_iff] at member
        obtain ⟨x, xMember, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        rw [PqxdhDeploymentIdealSteps.liftS, support_liftComp] at xMember
        simp [PqxdhRegistrationJointServerAccept.tail, PqxdhServerAuthNative.nativeSet, StateT.run] at xMember
        subst xMember
        rfl
      · rw [mem_support_bind_iff] at member
        obtain ⟨prepared, -, member⟩ := member
        rw [mem_support_bind_iff] at member
        obtain ⟨answer, answerMember, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact PqxdhDeploymentIdealEnvFacts.run_keepsGood (PqxdhDeploymentIdealSteps.tailCE setup.hmac shared.2.sessions)
          (fun query => tailBad shared.2.server.server.identity query = true)
          (fun z => z.1.2.server.server.identity = shared.2.server.server.identity)
          (fun query z good holds result resultMember =>
            tailCE_keeps setup.hmac shared.2.sessions _ query z good holds result resultMember)
          _ (tail_keeps _ _ shared.2 _) (shared, none) rfl answer answerMember
    · exact inactive r member
  · exact inactive r member

/-- The selected accept keeps the Server identity and the pins and issues no inadmissible request. -/
theorem acceptSelectedEnv_pin (p : PqxdhDeploymentIdealParams.Params KemSK count) (raw : Pqxdh.Bytes)
    (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  change v ∈ support ((fun r => (r.1.1.1.1, PqxdhDeploymentIdealEnvStep.acceptedEnv e r)) <$> coins (n := 2)
    ((PqxdhDeploymentIdealEnvStep.acceptGame setup codec checks p e.created.seed raw
      (e.backend.2.1, (e.backend.1, ∅))).run e.native.shared)) at member
  rw [support_map] at member
  obtain ⟨r, rMember, rfl⟩ := member
  have inner : r ∈ support ((fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      (PqxdhDeploymentIdealKernel.lazyDummy (n := 2)))
      ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks e.created.seed p.chosen p.challenge raw).run
        e.native.shared)).run (e.backend.2.1, (e.backend.1, ∅))) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  rw [support_map] at inner
  obtain ⟨x, xMember, rfl⟩ := inner
  have kept := acceptExposed_server setup codec checks e.created.seed p.chosen p.challenge raw e.native.shared x.1
    (PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ xMember)
  refine ⟨kept, ?_⟩
  unfold pins PqxdhDeploymentIdealEnvStep.acceptedEnv
  exact strip_pins _

/-- The selected accept issues no inadmissible request. -/
theorem acceptSelectedEnv_ok (p : PqxdhDeploymentIdealParams.Params KemSK count) (raw : Pqxdh.Bytes)
    (e : EnvState KemSK SplitBk) :
    ((PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  change (_ <$> coins _).IsQueryBoundP _ 0
  rw [isQueryBoundP_map_iff]
  exact coins_ok e _

end Ideal


/-! ### Build responses -/

section Wrote
variable {Reader Response : Type} (codec : Codec Reader Response)

/-- A build result that published a response carries the Phase 2 writer output of fields with the given Server identity. -/
def Wrote {S : Type} (identity : RawCtxServerRouting.Identity) :
    RustM (Option PqxdhServerRegistrationPublication.Response × S) → Prop
  | .ok (some response, _) => ∃ fields, codec.write2 fields = some response.serialized ∧ fields.identity = identity
  | _ => True

/-- A published result with its state mapped writes the same response. -/
theorem wrote_map {S T : Type} (identity : RawCtxServerRouting.Identity) (f : S → T)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × S)) (wrote : Wrote codec identity result) :
    Wrote codec identity (Functor.map (Prod.map id f) result) := by
  rcases result with ⟨_ | response, after⟩ | error | _
  · trivial
  · exact wrote
  · trivial
  · trivial

section Native
variable {Metadata PeerMetadata Consumed σ ι' : Type} {base : OracleSpec ι'}
open PqxdhServerRegistrationPublication (TailSpec State build candidateTail afterInitialization responseFields)

/-- A registration tail whose Phase 2 writer callback answers every request with the codec's writer. -/
def WriteDet (impl : QueryImpl TailSpec (StateT σ (OracleComp base))) : Prop :=
  ∀ fields state, ∀ result ∈ support ((impl (.inr (.write fields))).run state), result.1 = codec.write2 fields

/-- The first send and Phase 2 writing under a deterministic writer: a published response is the writer output of the candidate's response fields. -/
theorem after_wrote (impl : QueryImpl TailSpec (StateT σ (OracleComp base))) (det : WriteDet codec impl)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : σ) :
    ∀ result ∈ support ((simulateQ impl (afterInitialization candidate authenticated kernel metadata state)).run primitive),
      Wrote codec candidate.server_identity_public_key (.ok result.1) := by
  intro result supported
  obtain ⟨sent, afterSend, afterErase, _, _, rest⟩ :=
    PqxdhServerRegistrationPublication.afterInitialization_support impl candidate authenticated kernel metadata state
      primitive result supported
  cases hs : sent.2 with
  | none =>
      rw [hs] at rest
      rw [rest]
      trivial
  | some encrypted =>
      rw [hs] at rest
      obtain ⟨written, afterWrite, writtenMember, same⟩ := rest
      rw [same]
      have value := det _ _ _ writtenMember
      cases written with
      | none => trivial
      | some bytes => exact ⟨responseFields candidate encrypted, value.symm, rfl⟩

/-- The candidate tail under a deterministic writer: a published response is the writer output of fields carrying the candidate's Server identity. -/
theorem candidate_wrote (impl : QueryImpl TailSpec (StateT σ (OracleComp base))) (det : WriteDet codec impl)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : pqxdh.ServerRegistrationCandidate)
    (root : PqxdhSecretInputKdf.RootOutput) (payload : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : σ) :
    ∀ result ∈ support ((simulateQ impl (candidateTail source candidate root payload metadata state)).run primitive),
      Wrote codec candidate.server_identity_public_key result.1 := by
  intro result supported
  obtain ⟨kernel, hrun, _, _, _⟩ := PqxdhRootTableInitialization.initialize_refines source
    PqxdhServerAuthExperiment.unitRatchet false root
  have hinit := (PqxdhServerRegistrationPublication.candidate_initialization source candidate root).trans hrun
  obtain ⟨binding, hbinding, _⟩ := PqxdhServerRegistrationPublication.candidate_binding candidate
  simp only [candidateTail, hinit, hbinding, PqxdhServerRegistrationPublication.continueRust, simulateQ_bind,
    simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨valid, afterIdentity⟩, _, supported⟩ := supported
  cases valid
  · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at supported
    rw [supported]
    trivial
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reserved, afterReserve⟩, _, supported⟩ := supported
  cases reserved
  · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at supported
    rw [supported]
    trivial
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at supported
  split_ifs at supported with empty fits
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
    trivial
  · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨allocated, afterAllocate⟩, _, supported⟩ := supported
    cases allocated
    · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      rw [supported]
      trivial
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_map, StateT.run_map,
      support_map, Set.mem_image] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact after_wrote codec impl det candidate _ kernel metadata state afterAllocate inner reached
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
    trivial

/-- The native Server build under a deterministic writer: a published response is the writer output of fields carrying the Server's identity. -/
theorem build_wrote (impl : QueryImpl TailSpec (StateT σ (OracleComp base))) (det : WriteDet codec impl)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (payload : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : σ) :
    ∀ result ∈ support ((simulateQ impl (build source pending root payload metadata state)).run primitive),
      Wrote codec state.server.identity result.1 := by
  intro result supported
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state.control
  simp only [build, hnext, PqxdhServerRegistrationPublication.continueRust] at supported
  cases next with
  | Err error =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
      trivial
  | Ok next =>
      obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
        state.control pending ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers next).isSome then .Occupied else .Available)
      simp only [hprepared] at supported
      cases prepared with
      | Err error =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          rw [supported]
          trivial
      | Ok candidate =>
          have identity := (PqxdhServerAuthNegativeControl.prepare_commit_fields _ _ _ _ candidate hprepared).2.1
          have wrote := candidate_wrote codec impl det source candidate root payload metadata state primitive result
            supported
          rw [identity] at wrote
          exact wrote

end Native

section Generic
variable {Kernel Metadata PeerMetadata Consumed ι' : Type} {spec' : OracleSpec ι'}
open PqxdhInitialGenericPublication (State)

/-- A Phase 2 writer callback that answers every request with the codec's writer. -/
def AuxWriteDet (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec')) : Prop :=
  ∀ fields, ∀ x ∈ support (aux (.write fields)), x = codec.write2 fields

/-- The generic first send and Phase 2 writing under a deterministic writer, for any other replies. -/
theorem afterInitializationG_wrote (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec')) (det : AuxWriteDet codec aux)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Kernel)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel
      metadata state), Wrote codec candidate.server_identity_public_key (.ok result) := by
  intro result supported
  unfold PqxdhInitialGenericPublication.afterInitialization at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨⟨advanced, encrypted⟩, _, member⟩ := supported
  rw [mem_support_bind_iff] at member
  obtain ⟨_, _, member⟩ := member
  cases encrypted with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      trivial
  | some encrypted =>
      dsimp only at member
      rw [mem_support_bind_iff] at member
      obtain ⟨serialized, serializedMember, member⟩ := member
      cases serialized with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          trivial
      | some serialized =>
          simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          exact ⟨_, (det _ _ serializedMember).symm, rfl⟩

/-- A written response of every continuation of the actual Rust value is a written response of the continued result. -/
theorem continueRust_wrote {α : Type} (value : RustM α)
    (next : α → OracleComp spec' (RustM (Option PqxdhServerRegistrationPublication.Response × State Kernel Metadata
      PeerMetadata Consumed))) (identity : RawCtxServerRouting.Identity)
    (continued : ∀ inner, value = ok inner → ∀ result ∈ support (next inner), Wrote codec identity result) :
    ∀ result ∈ support (PqxdhInitialGenericBuilder.continueRust value next), Wrote codec identity result := by
  intro result supported
  cases value with
  | ok inner => exact continued inner rfl result supported
  | fail error =>
      simp only [PqxdhInitialGenericBuilder.continueRust, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      trivial
  | div =>
      simp only [PqxdhInitialGenericBuilder.continueRust, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      trivial

/-- The generic candidate admission and first send under a deterministic writer, for any other replies. -/
theorem candidateG_wrote (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec')) (det : AuxWriteDet codec aux)
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state),
      Wrote codec candidate.server_identity_public_key result := by
  intro result supported
  unfold PqxdhInitialGenericBuilder.candidate at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨valid, _, member⟩ := supported
  by_cases invalid : (!valid) = true
  · simp only [invalid, ite_true, support_pure, Set.mem_singleton_iff] at member
    subst member
    trivial
  · simp only [invalid, Bool.false_eq_true, ite_false, mem_support_bind_iff] at member
    obtain ⟨reserved, _, member⟩ := member
    by_cases unreserved : (!reserved) = true
    · simp only [unreserved, ite_true, support_pure, Set.mem_singleton_iff] at member
      subst member
      trivial
    · simp only [unreserved, Bool.false_eq_true, ite_false] at member
      refine continueRust_wrote codec _ _ _ (fun kernel _ inner innerMember => ?_) result member
      split_ifs at innerMember with empty bounded
      · simp only [support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        trivial
      · rw [mem_support_bind_iff] at innerMember
        obtain ⟨allocated, _, innerMember⟩ := innerMember
        by_cases unallocated : (!allocated) = true
        · simp only [unallocated, ite_true, support_pure, Set.mem_singleton_iff] at innerMember
          subst innerMember
          trivial
        · simp only [unallocated, Bool.false_eq_true, ite_false] at innerMember
          refine continueRust_wrote codec _ _ _ (fun binding _ final finalMember => ?_) inner innerMember
          rw [support_map] at finalMember
          obtain ⟨published, publishedMember, rfl⟩ := finalMember
          exact afterInitializationG_wrote codec calls aux det candidate _ _ metadata state published publishedMember
      · simp only [support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        trivial

/-- The generic Server build under a deterministic writer: a published response is the writer output of fields carrying the Server's identity, for any other replies. -/
theorem genericBuild_wrote (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec')) (det : AuxWriteDet codec aux)
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata state),
      Wrote codec state.server.identity result := by
  intro result supported
  unfold PqxdhServerAuthSendFactor.genericBuild at supported
  refine continueRust_wrote codec _ _ _ (fun next _ inner innerMember => ?_) result supported
  rcases next with key | error
  · dsimp only at innerMember
    refine continueRust_wrote codec _ _ _ (fun prepared preparedEq final finalMember => ?_) inner innerMember
    rcases prepared with candidate | error
    · have identity := (PqxdhServerAuthNegativeControl.prepare_commit_fields _ _ _ _ candidate preparedEq).2.1
      have wrote := candidateG_wrote codec calls aux det initial candidate data metadata state final finalMember
      rw [identity] at wrote
      exact wrote
    · simp only [support_pure, Set.mem_singleton_iff] at finalMember
      subst finalMember
      trivial
  · simp only [support_pure, Set.mem_singleton_iff] at innerMember
    subst innerMember
    trivial

end Generic

end Wrote


/-! ### The build steps -/

section BuildSteps
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {Bk : Type} {n : ℕ}
open PqxdhServerRegistrationPublication (TailSpec)

/-- The registration tail with its Phase 2 writer answered by the codec's writer and every other request forwarded. -/
def writeImpl : QueryImpl TailSpec (OracleComp TailSpec)
  | .inl query => liftM (TailSpec.query (.inl query))
  | .inr (.write fields) => pure (codec.write2 fields)
  | .inr query => liftM (TailSpec.query (.inr query))

/-- The forwarded native registration tail answers its Phase 2 writer as `writeImpl` does. -/
theorem nativeTailFwd_writeImpl :
    (PqxdhDeploymentEnvironment.nativeTailFwd (n := n) setup codec checks) ∘ₛ writeImpl codec =
      PqxdhDeploymentEnvironment.nativeTailFwd setup codec checks := by
  funext query
  rcases query with query | query
  · simp only [QueryImpl.apply_compose, writeImpl, simulateQ_spec_query]
  · cases query with
    | write fields =>
        simp only [QueryImpl.apply_compose, writeImpl, simulateQ_pure]
        rfl
    | _ => simp only [QueryImpl.apply_compose, writeImpl, simulateQ_spec_query]

/-- The forwarded registration tail answers its Phase 2 writer with the codec's writer. -/
theorem tailFwd_det : WriteDet codec (PqxdhDeploymentEnvironment.tailFwd (n := n) setup codec checks) := by
  intro fields state result member
  have same : (PqxdhDeploymentEnvironment.tailFwd (n := n) setup codec checks (.inr (.write fields))).run state =
      pure (codec.write2 fields, state) := rfl
  rw [same, support_pure, Set.mem_singleton_iff] at member
  rw [member]

/-- The free factored build with the Phase 2 writer answered by the codec's writer: a published response is the writer output of fields carrying the Server's identity, for any other replies. -/
theorem freeBuild_wrote (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (value : PqxdhServerAuthSendFactor.Factor) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    ∀ result ∈ support (simulateQ (writeImpl codec) (PqxdhDeploymentSplitFactor.freeBuild source value pending data
      server)), Wrote codec server.server.identity result := by
  intro result supported
  rw [← PqxdhDeploymentSplitFactor.factored_free (writeImpl codec)] at supported
  unfold PqxdhServerAuthLoggedSendFactor.factored at supported
  rw [support_map] at supported
  obtain ⟨g, gMember, rfl⟩ := supported
  exact wrote_map codec _ _ g (genericBuild_wrote codec _ _ (fun fields x member => by
    simpa only [writeImpl, support_pure, Set.mem_singleton_iff] using member) _ _ _ _ _ g gMember)

/-- A build reply that is a response carries the Phase 2 writer output of fields with the Server identity. -/
def ReplyWrote (identity : RawCtxServerRouting.Identity)
    (reply : Option PqxdhServerRegistrationPublication.Response) : Prop :=
  ∀ response, reply = some response →
    ∃ fields, codec.write2 fields = some response.serialized ∧ fields.identity = identity

/-- Settling a build result that keeps the Server identity and writes its response keeps both. -/
theorem settle_wrote (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)))
    (kept : ∀ value, result = ok value → value.2.server.identity = server.server.identity)
    (wrote : Wrote codec server.server.identity result) :
    (PqxdhServerAuthExperiment.settle server result).2.server.identity = server.server.identity ∧
      ReplyWrote codec server.server.identity (PqxdhServerAuthExperiment.settle server result).1 := by
  rcases result with ⟨_ | response, after⟩ | error | _
  · exact ⟨kept _ rfl, fun _ found => by cases found⟩
  · refine ⟨kept _ rfl, fun other found => ?_⟩
    simp only [PqxdhServerAuthExperiment.settle, Option.some.injEq] at found
    subst found
    exact wrote
  · exact ⟨rfl, fun _ found => by cases found⟩
  · exact ⟨rfl, fun _ found => by cases found⟩

/-- The real build keeps the Server identity and the pins, and a reply carries the Phase 2 writer output of fields with the Server identity. -/
theorem buildStep_pin (session : ℕ) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.buildStep (n := n) setup codec checks session payload).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e ∧ ReplyWrote codec (serverId e) v.1 := by
  intro v member
  unfold PqxdhDeploymentEnvironment.buildStep at member
  simp only [StateT.run] at member
  split at member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl, fun _ found => by cases found⟩
  · rename_i token _
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨result, resultMember, _, _, rfl⟩ := member
    have wrote := build_wrote codec _ (tailFwd_det setup codec checks) setup.source token.pending token.root payload ()
      e.native.shared.2.server [] result resultMember
    have kept : ∀ value, result.1 = ok value → value.2.server.identity = e.native.shared.2.server.server.identity := by
      intro value found
      rcases PqxdhRegistrationResponse.build_publication _ setup.source token.pending token.root payload ()
          e.native.shared.2.server [] result resultMember with same | ⟨_, candidate, kernel, bytes, _, _, same⟩
      · rw [same] at found
        cases found
        rfl
      · rw [same] at found
        cases found
        rfl
    obtain ⟨identity, replied⟩ := settle_wrote codec _ _ kept wrote
    exact ⟨identity, by unfold pins; exact strip_pins _, replied⟩

/-- Publishing a Server build issues no inadmissible request. -/
theorem serverEffect_ok (e : EnvState KemSK Bk) (settled : Option PqxdhServerRegistrationPublication.Response ×
    PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :
    (PqxdhDeploymentEnvironment.serverEffect (n := n) settled).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.serverEffect
  split
  · trivial
  · split
    · trivial
    · exact issue_ok e _ trivial

/-- The real build issues no inadmissible request. -/
theorem buildStep_ok (session : ℕ) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ((PqxdhDeploymentEnvironment.buildStep (n := n) setup codec checks session payload).run e).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.buildStep
  simp only [StateT.run]
  split
  · trivial
  · rename_i token _
    rw [show (0 : ℕ) = 0 + 0 from rfl]
    refine isQueryBoundP_bind (ok_of_noAdmin e _ ?_) fun _ _ => ?_
    · have bound := PqxdhDeploymentEnvironment.build_fwd_bound (n := n) setup codec checks token.pending token.root
        payload e.native.shared.2.server [] .administrative
      simp only [reduceCtorEq, ite_false] at bound
      exact bound
    · rw [show (0 : ℕ) = 0 + 0 from rfl]
      exact isQueryBoundP_bind (serverEffect_ok e _) fun _ _ => trivial

/-- The forwarded split build keeps the Server identity and writes its response, for any other replies. -/
theorem buildSplitFwd_wrote (material : PqxdhDeploymentHiddenLayout.Material)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    ∀ p ∈ support ((PqxdhDeploymentEnvironment.buildSplitFwd (n := n) setup codec checks material token payload
      server).run []),
      (∀ value, p.1 = ok value → value.2.server.identity = server.server.identity) ∧
        Wrote codec server.server.identity p.1 := by
  intro p member
  rw [PqxdhDeploymentSplitFactor.buildSplitFwd_free, StateT.run_map, support_map] at member
  obtain ⟨y, yMember, rfl⟩ := member
  have free := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ yMember
  have built := PqxdhDeploymentIdealEnvBuild.freeBuild_shape _ _ _ _ _ y.1 free
  have forwarded : y.1 ∈ support (simulateQ (PqxdhDeploymentEnvironment.nativeTailFwd (n := n) setup codec checks)
      (PqxdhDeploymentSplitFactor.freeBuild setup.source (PqxdhServerAuthCtxMaterial.factor
        (PqxdhDeploymentHiddenLayout.joinOutput material PqxdhDeploymentHiddenSplit.dummySeed)) token.pending payload
        server)) := by
    rw [← PqxdhDeploymentEnvironment.tailFwd_forget setup codec checks _ [], support_map]
    exact ⟨y, yMember, rfl⟩
  rw [← nativeTailFwd_writeImpl setup codec checks, QueryImpl.simulateQ_compose] at forwarded
  have wrote := freeBuild_wrote codec _ _ _ _ server y.1
    (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ forwarded)
  dsimp only
  rcases hy : y.1 with ⟨_ | response, after⟩ | error | _
  · rw [hy] at built
    refine ⟨fun value found => ?_, trivial⟩
    change ok (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel (none, after)) =
      ok value at found
    cases found
    change after.server.identity = server.server.identity
    rw [built]
  · rw [hy] at built wrote
    obtain ⟨candidate, kernel, _, _, published⟩ := built
    refine ⟨fun value found => ?_, wrote⟩
    change ok (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel
      (some response, after)) = ok value at found
    cases found
    rw [published]
    rfl
  · exact ⟨fun value found => (by cases found), trivial⟩
  · exact ⟨fun value found => (by cases found), trivial⟩

open PqxdhDeploymentIdealSteps (SplitBk) in
/-- The marked build keeps the Server identity and the pins, and a reply carries the Phase 2 writer output of fields with the Server identity. -/
theorem buildCachedEnv_pin (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : PqxdhDeploymentIdealSlots.Coord)
    (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e ∧ ReplyWrote codec (serverId e) v.1 := by
  intro v member
  change v ∈ support (PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords e) at member
  unfold PqxdhDeploymentIdealEnv.buildCachedEnv at member
  split at member
  · split at member
    · rename_i j token _ _ _ material _
      rw [mem_support_bind_iff] at member
      obtain ⟨result, resultMember, member⟩ := member
      rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      unfold PqxdhDeploymentEnvironment.buildSplitEnv at resultMember
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at resultMember
      obtain ⟨p, pMember, _, _, rfl⟩ := resultMember
      obtain ⟨kept, wrote⟩ := buildSplitFwd_wrote setup codec checks material token payload e.native.shared.2.server p
        pMember
      obtain ⟨identity, replied⟩ := settle_wrote codec _ _ kept wrote
      exact ⟨identity, by unfold pins; exact strip_pins _, replied⟩
    · simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl, fun _ found => by cases found⟩
  · simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl, fun _ found => by cases found⟩

/-- Publishing a hidden Server build issues no inadmissible request. -/
theorem hiddenServerEffect_ok (e : EnvState KemSK Bk) (slot : PqxdhRecordLiftInterface.Slot n)
    (settled : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState) :
    (PqxdhDeploymentEnvironment.hiddenServerEffect slot settled).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.hiddenServerEffect
  split
  · trivial
  · split
    · trivial
    · exact issue_ok e _ trivial

open PqxdhDeploymentIdealSteps (SplitBk) in
/-- The marked build issues no inadmissible request. -/
theorem buildCachedEnv_ok (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : PqxdhDeploymentIdealSlots.Coord)
    (e : EnvState KemSK SplitBk) :
    ((PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  change (PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords e).IsQueryBoundP _ 0
  unfold PqxdhDeploymentIdealEnv.buildCachedEnv
  split
  · split
    · rw [show (0 : ℕ) = 0 + 0 from rfl]
      refine isQueryBoundP_bind ?_ fun _ _ => trivial
      unfold PqxdhDeploymentEnvironment.buildSplitEnv
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
      rw [show (0 : ℕ) = 0 + 0 from rfl]
      refine isQueryBoundP_bind (ok_of_noAdmin e _ (PqxdhDeploymentIdealEnvBuild.buildSplitFwd_noAdmin setup codec checks
        _ _ _ _ [])) fun _ _ => ?_
      rw [show (0 : ℕ) = 0 + 0 from rfl]
      exact isQueryBoundP_bind (hiddenServerEffect_ok e _ _) fun _ _ => trivial
    · trivial
  · trivial

end BuildSteps


/-! ### The ideal environment step -/

section Combined
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ} {Bk : Type}
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentInterface (Command CommandSpec)

/-- An environment step's move with its command and reply: the Server identity is kept, the pins follow the public summary's owner update for the command and its reply, and the entry is shaped as a build of the Server identity. -/
def PinMove (command : Command) (reply : CommandSpec command) (e e' : EnvState KemSK Bk) : Prop :=
  serverId e' = serverId e ∧
    (∀ summary : PqxdhDeploymentTranscript.Summary, summary.owners.map Prod.fst = pins e →
      (PqxdhDeploymentTranscript.stepCommand summary command reply).owners.map Prod.fst = pins e') ∧
    PqxdhDeploymentEligibility.BuildShaped codec (serverId e) ⟨.inl (.inr command), reply⟩

/-- A command other than create leaves the summary's owners unchanged. -/
theorem stepCommand_owners (summary : PqxdhDeploymentTranscript.Summary) (command : Command)
    (reply : CommandSpec command) (notCreate : ∀ pin keyId, command ≠ .create pin keyId) :
    (PqxdhDeploymentTranscript.stepCommand summary command reply).owners = summary.owners := by
  cases command with
  | create pin keyId => exact absurd rfl (notCreate pin keyId)
  | bundle owner =>
      cases reply <;> simp only [PqxdhDeploymentTranscript.stepCommand] <;> split_ifs <;> rfl
  | finish owner raw =>
      cases reply <;> simp only [PqxdhDeploymentTranscript.stepCommand] <;> split_ifs <;> rfl
  | _ => rfl

/-- A move of a command other than create and build: the Server identity and the pins are kept. -/
theorem pinMove_quiet (command : Command) (reply : CommandSpec command) (e e' : EnvState KemSK Bk)
    (notCreate : ∀ pin keyId, command ≠ .create pin keyId)
    (notBuild : ∀ session payload, command ≠ .build session payload)
    (identity : serverId e' = serverId e) (same : pins e' = pins e) : PinMove codec command reply e e' := by
  refine ⟨identity, fun summary agree => ?_, ?_⟩
  · rw [stepCommand_owners summary command reply notCreate, agree, same]
  · cases command with
    | build session payload => exact absurd rfl (notBuild session payload)
    | _ => trivial

/-- A build move: the Server identity and the pins are kept and a response is written with the Server identity. -/
theorem pinMove_build (session : ℕ) (payload : Option Pqxdh.Bytes)
    (reply : Option PqxdhServerRegistrationPublication.Response) (e e' : EnvState KemSK Bk)
    (identity : serverId e' = serverId e) (same : pins e' = pins e) (wrote : ReplyWrote codec (serverId e) reply) :
    PinMove codec (.build session payload) reply e e' := by
  refine ⟨identity, fun summary agree => ?_, ?_⟩
  · rw [stepCommand_owners summary (Command.build session payload) reply (fun _ _ wrong => by cases wrong), agree, same]
  · rcases reply with _ | response
    · simp [PqxdhDeploymentEligibility.BuildShaped]
    · exact wrote response rfl

/-- Every outcome of the ideal environment step moves the state with its command and reply. -/
theorem idealStep_move (t : PqxdhDeploymentIdealParams.Target count) (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (query : PqxdhRecordLiftInterface.EnvQuery) (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnv.idealStep setup codec checks t p query).run e),
      PinMove codec query.val v.1 e v.2 := by
  intro v member
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      change v ∈ support ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := 2) setup (p.pool t) pin keyId).run e)
        at member
      obtain ⟨identity, (⟨noReply, same⟩ | ⟨word, index, parsed, replied, appended⟩)⟩ :=
        createPoolStep_pin setup (p.pool t) pin keyId e v member
      · refine ⟨identity, fun summary agree => ?_, trivial⟩
        rw [show v.1 = Option.none from noReply]
        simp only [PqxdhDeploymentTranscript.stepCommand]
        rw [agree, same]
      · refine ⟨identity, fun summary agree => ?_, trivial⟩
        rw [replied]
        simp only [PqxdhDeploymentTranscript.stepCommand, parsed, List.map_append, List.map_cons, List.map_nil]
        rw [agree, appended]
  | bundle owner =>
      change v ∈ support ((PqxdhDeploymentEnvironment.bundleStep (n := 2) setup codec owner).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      obtain ⟨identity, same⟩ := bundleStep_pin setup codec owner _ v member
      exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong) identity
        same
  | accept raw =>
      change v ∈ support (if e.backend.2.2.accepts = t.accept then _ else _) at member
      split at member
      · obtain ⟨identity, same⟩ := acceptSelectedEnv_pin setup codec checks p raw e v member
        exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong)
          identity same
      · change v ∈ support ((PqxdhDeploymentEnvironment.acceptStep (n := 2) setup codec checks raw).run
          (PqxdhDeploymentEnvironment.snapped _ _)) at member
        obtain ⟨identity, same⟩ := acceptStep_pin setup codec checks raw _ v member
        exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong)
          identity same
  | build session payload =>
      change v ∈ support (match e.backend.2.2.marks with
        | some (index, coords) => if index = session ∧ (e.native.shared.2.pending session).isSome then
            (PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e
          else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e
        | none => (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e)
        at member
      split at member
      · split at member
        · obtain ⟨identity, same, wrote⟩ := buildCachedEnv_pin setup codec checks session payload _ e v member
          exact pinMove_build codec session payload v.1 e v.2 identity same wrote
        · change v ∈ support ((PqxdhDeploymentEnvironment.buildStep (n := 2) setup codec checks session payload).run
            (PqxdhDeploymentEnvironment.snapped _ e)) at member
          obtain ⟨identity, same, wrote⟩ := buildStep_pin setup codec checks session payload _ v member
          exact pinMove_build codec session payload v.1 e v.2 identity same wrote
      · change v ∈ support ((PqxdhDeploymentEnvironment.buildStep (n := 2) setup codec checks session payload).run
          (PqxdhDeploymentEnvironment.snapped _ e)) at member
        obtain ⟨identity, same, wrote⟩ := buildStep_pin setup codec checks session payload _ v member
        exact pinMove_build codec session payload v.1 e v.2 identity same wrote
  | finish owner raw =>
      change v ∈ support (if e.backend.2.2.active = true ∧ owner = t.kem.val ∧
        PqxdhDeploymentIdealSteps.initSentAt e.native.owners owner = true then _ else _) at member
      split at member
      · obtain ⟨identity, same⟩ := finishChallengeEnv_pin setup codec p owner raw e v member
        exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong)
          identity same
      · change v ∈ support ((PqxdhDeploymentEnvironment.finishStep (n := 2) setup codec owner raw).run
          (PqxdhDeploymentEnvironment.snapped _ e)) at member
        obtain ⟨identity, same⟩ := finishStep_pin setup codec owner raw _ v member
        exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong)
          identity same
  | hmac key message =>
      change v ∈ support ((PqxdhDeploymentEnvironment.hmacStep (n := 2) setup key message).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      obtain ⟨identity, same⟩ := hmacStep_pin setup key message _ v member
      exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong) identity
        same
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

/-- Inadmissibility reads only the registration owners of the environment state. -/
theorem badInstall_congr {Bk' : Type} {n : ℕ} (e : EnvState KemSK Bk) (e' : EnvState KemSK Bk')
    (same : e.native.owners = e'.native.owners) : badInstall (n := n) e = badInstall e' := by
  funext query
  unfold badInstall InstallOk
  rw [same]

/-- The ideal environment step issues no inadmissible request. -/
theorem idealStep_ok (t : PqxdhDeploymentIdealParams.Target count) (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (query : PqxdhRecordLiftInterface.EnvQuery) (e : EnvState KemSK SplitBk) :
    ((PqxdhDeploymentIdealEnv.idealStep setup codec checks t p query).run e).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId => exact createPoolStep_ok setup (p.pool t) pin keyId e
  | bundle owner =>
      have ok := bundleStep_ok (n := 2) setup codec owner (PqxdhDeploymentEnvironment.snapped ⟨.bundle owner, allowed⟩ e)
      rw [badInstall_congr (PqxdhDeploymentEnvironment.snapped ⟨.bundle owner, allowed⟩ e) e rfl] at ok
      exact ok
  | accept raw =>
      show OracleComp.IsQueryBoundP (if e.backend.2.2.accepts = t.accept then
          (PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e
        else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.accept raw, allowed⟩).run
          { e with backend := PqxdhDeploymentIdealEnvStep.bump e.backend })
        (fun effect => badInstall e effect = true) 0
      split
      · exact acceptSelectedEnv_ok setup codec checks p raw e
      · have ok := acceptStep_ok (n := 2) setup codec checks raw (PqxdhDeploymentEnvironment.snapped ⟨.accept raw, allowed⟩
          { e with backend := PqxdhDeploymentIdealEnvStep.bump e.backend })
        rw [badInstall_congr (PqxdhDeploymentEnvironment.snapped ⟨.accept raw, allowed⟩
          { e with backend := PqxdhDeploymentIdealEnvStep.bump e.backend }) e rfl] at ok
        exact ok
  | build session payload =>
      show OracleComp.IsQueryBoundP (match e.backend.2.2.marks with
        | some (index, coords) => if index = session ∧ (e.native.shared.2.pending session).isSome then
            (PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e
          else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e
        | none => (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e)
        (fun effect => badInstall e effect = true) 0
      have real := buildStep_ok (n := 2) setup codec checks session payload
        (PqxdhDeploymentEnvironment.snapped ⟨.build session payload, allowed⟩ e)
      rw [badInstall_congr (PqxdhDeploymentEnvironment.snapped ⟨.build session payload, allowed⟩ e) e rfl] at real
      split
      · split
        · exact buildCachedEnv_ok setup codec checks session payload _ e
        · exact real
      · exact real
  | finish owner raw =>
      show OracleComp.IsQueryBoundP (if e.backend.2.2.active = true ∧ owner = t.kem.val ∧
          PqxdhDeploymentIdealSteps.initSentAt e.native.owners owner = true then
          (PqxdhDeploymentIdealEnvFinish.finishChallengeEnv setup codec p owner raw).run e
        else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.finish owner raw, allowed⟩).run e)
        (fun effect => badInstall e effect = true) 0
      split
      · exact finishChallengeEnv_ok setup codec p owner raw e
      · have ok := finishStep_ok (n := 2) setup codec owner raw (PqxdhDeploymentEnvironment.snapped ⟨.finish owner raw, allowed⟩ e)
        rw [badInstall_congr (PqxdhDeploymentEnvironment.snapped ⟨.finish owner raw, allowed⟩ e) e rfl] at ok
        exact ok
  | hmac key message =>
      have ok := hmacStep_ok (n := 2) setup key message (PqxdhDeploymentEnvironment.snapped ⟨.hmac key message, allowed⟩ e)
      rw [badInstall_congr (PqxdhDeploymentEnvironment.snapped ⟨.hmac key message, allowed⟩ e) e rfl] at ok
      exact ok
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

/-- Every outcome of the ideal environment of a target's step moves the state with its command and reply. -/
theorem envGD_move {A : Type} (t : PqxdhDeploymentIdealParams.Target count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (query : PqxdhRecordLiftInterface.EnvQuery)
    (e : EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count × SplitBk)) :
    ∀ v ∈ support (((PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime).step query).run e),
      PinMove codec query.val v.1 e v.2 := by
  intro v member
  change v ∈ support (Prod.map id (PqxdhDeploymentEnvironmentDraw.withE e.backend.1) <$>
    (PqxdhDeploymentIdealEnv.idealStep setup codec checks t e.backend.1 query).run
      (PqxdhDeploymentEnvironmentDraw.dropE e)) at member
  rw [support_map] at member
  obtain ⟨u, uMember, rfl⟩ := member
  exact idealStep_move setup codec checks t e.backend.1 query _ u uMember

/-- The ideal environment of a target issues no inadmissible request. -/
theorem envGD_ok {A : Type} (t : PqxdhDeploymentIdealParams.Target count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (query : PqxdhRecordLiftInterface.EnvQuery)
    (e : EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count × SplitBk)) :
    (((PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime).step query).run e).IsQueryBoundP
      (fun effect => badInstall e effect = true) 0 := by
  change (Prod.map id (PqxdhDeploymentEnvironmentDraw.withE e.backend.1) <$>
    (PqxdhDeploymentIdealEnv.idealStep setup codec checks t e.backend.1 query).run
      (PqxdhDeploymentEnvironmentDraw.dropE e)).IsQueryBoundP _ 0
  rw [isQueryBoundP_map_iff, badInstall_congr e (PqxdhDeploymentEnvironmentDraw.dropE e) rfl]
  exact idealStep_ok setup codec checks t e.backend.1 query _

/-- Every startup outcome of the ideal environment of a target is a constructed Server's initial environment state: no owner and the constructed Server's identity. -/
theorem envGD_start {A : Type} (t : PqxdhDeploymentIdealParams.Target count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (created : PqxdhLiveServerConstruction.Created Unit)
    (initial : EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count × SplitBk))
    (started : some (created, initial) ∈ support
      (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime).start) :
    serverId initial = created.server.server.identity ∧ pins initial = [] := by
  change some (created, initial) ∈ support (PqxdhDeploymentIdealParams.drawParams setup count >>= fun p =>
    PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime
      (fun created => (p, PqxdhDeploymentIdealSteps.splitInit created))) at started
  rw [mem_support_bind_iff] at started
  obtain ⟨p, _, startedAt⟩ := started
  have same := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime _ created initial startedAt
  subst same
  exact ⟨rfl, rfl⟩

end Combined

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.associatedData_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.associatedData_array

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.installPin_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.installPin_refl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.installPin_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.installPin_inactive

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finish_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finish_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finish_serverIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finish_serverIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.prepare_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.prepare_candidate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tail_staged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tail_staged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.opened_for' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.opened_for

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.owner_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.owner_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwner_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwner_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_admin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_admin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.ok_of_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.ok_of_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.coins_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.coins_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.issue_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.issue_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.ownerEffect_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.ownerEffect_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hiddenOwnerEffect_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hiddenOwnerEffect_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.strip_pins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.strip_pins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pins_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pins_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishStep_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishStep_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishedEnv_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishedEnv_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.commitEnv_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.commitEnv_member

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.commitEnv_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.commitEnv_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.clearedMetadata_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.clearedMetadata_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishSplitFwd_for' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishSplitFwd_for

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.markedRoot_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.markedRoot_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.groupEnv_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.groupEnv_member

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.groupEnv_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.groupEnv_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishChallengeEnv_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishChallengeEnv_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishChallengeEnv_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishChallengeEnv_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundled_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundled_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundleStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundleStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundleStep_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundleStep_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptLogged_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptLogged_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptStep_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptStep_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hmacStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hmacStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hmacStep_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hmacStep_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.createPoolStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.createPoolStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.createPoolStep_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.createPoolStep_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailBad_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailBad_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailCE_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailCE_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tail_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tail_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptExposed_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptExposed_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptSelectedEnv_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptSelectedEnv_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptSelectedEnv_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptSelectedEnv_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.wrote_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.wrote_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.after_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.after_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.candidate_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.candidate_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.build_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.build_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.afterInitializationG_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.afterInitializationG_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.continueRust_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.continueRust_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.candidateG_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.candidateG_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.genericBuild_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.genericBuild_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeTailFwd_writeImpl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeTailFwd_writeImpl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailFwd_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailFwd_det

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.freeBuild_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.freeBuild_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.settle_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.settle_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.serverEffect_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.serverEffect_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildStep_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildStep_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildSplitFwd_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildSplitFwd_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildCachedEnv_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildCachedEnv_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hiddenServerEffect_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hiddenServerEffect_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildCachedEnv_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildCachedEnv_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.stepCommand_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.stepCommand_owners

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pinMove_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pinMove_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pinMove_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pinMove_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.idealStep_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.idealStep_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_congr

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.idealStep_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.idealStep_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_start
