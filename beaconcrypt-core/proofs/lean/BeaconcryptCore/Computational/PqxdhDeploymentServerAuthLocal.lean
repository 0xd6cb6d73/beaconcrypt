-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable
import BeaconcryptCore.Computational.PqxdhDeploymentEligibility

/-! One step of the localization of the deployment experiment at creation index `c` (CE-8). The multi-owner side is `eager`: the source14 native handler with field reads (`base`), except that the target's material is drawn before the run (`Pre`: the created owner, the reply of its first bundle and the bundled owner): the `c`-th create, when its binding is the protected one, installs the drawn owner, and the first bundle of `c` after that answers with the drawn reply and installs the drawn bundled owner. The singleton side is the embedding of `PqxdhDeploymentServerAuthEmbed` routed into the source14 handler on the singleton state whose owner zero is the ServerAuth target (`singleStep`). `multiOf` reassembles the multi-owner state from the embedding's state and the singleton state: the shared state of the singleton, and the local owners with the target's owner at `c` (the drawn created owner before the first bundle, the singleton's owner zero after it); `phaseOf` gives the eager phase. `step_commute` is the one-step simulation: under `Ready` (one target slot at `c` at most, the singleton's owner zero is the drawn bundled owner until the first bundle and afterwards neither Fresh nor established, the first bundle not rejected) and for every query other than an identity, KEM, prekey or one-time read, one singleton step mapped by `multiOf` is one eager step on the reassembled state, up to the analysis histories. `base_stable` shows that the native handler reads no analysis history. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhSecretInputKdf
open PqxdhJointGapDh (ScalarBytes)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhDeploymentServerAuthEmbed (SourceSpec Owner Slot Emb embed coins forward localCreate localBundle localCallbacks
  inputBinding)
open PqxdhDeploymentServerAuthStable (Stable onShared_stable callbacks_program)
open PqxdhRegistrationR1Restriction (eraseShared route)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The source14 state. -/
abbrev State (KemSK : Type) := PqxdhRegistrationSchedule.State KemSK

/-- The source14 native handler with field reads. -/
noncomputable def base (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) : QueryImpl (SourceSpec KemSK) (StateT (State KemSK) ProbComp) :=
  PqxdhRegistrationJointRevealSchedule.native setup codec checks seed

/-- The eager phase of the target: not yet created, created and not yet bundled, or no longer special. -/
inductive Phase where
  | waiting
  | created
  | done
  deriving DecidableEq

/-- The target's material drawn before the run: the created owner, the reply of its first bundle, the bundled owner and the Phase 1 bundle that first bundle retained (design §4.6). -/
structure Pre (KemSK : Type) where
  created : Owner KemSK
  reply : Option Pqxdh.Bytes
  bundled : Owner KemSK
  init : Option PqxdhEd25519EufCma.Phase1Candidate

/-- Run a base step and keep the phase. -/
noncomputable def keep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (query : (SourceSpec KemSK).Domain) :
    StateT (State KemSK × Phase) ProbComp ((SourceSpec KemSK).Range query) := fun state =>
  (fun result => (result.1, (result.2, state.2))) <$> (base setup codec checks seed query).run state.1

/-- A kept base step runs the base step on the source14 state and keeps the phase. -/
theorem keep_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (query : (SourceSpec KemSK).Domain) (state : State KemSK × Phase) :
    (keep setup codec checks seed query).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (base setup codec checks seed query).run state.1 := rfl

open Classical in
/-- The multi-owner handler with the target's material drawn before the run. -/
noncomputable def eager (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) :
    QueryImpl (SourceSpec KemSK) (StateT (State KemSK × Phase) ProbComp)
  | .inl (.inl coin) => keep setup codec checks seed (.inl (.inl coin))
  | .inl (.inr (.create pin keyId)) => fun state =>
      if state.2 = .waiting ∧ state.1.owners.length = c then
        if (pin, keyId) = binding then pure (c, ({ state.1 with owners := state.1.owners ++ [pre.created] }, .created))
        else (fun result => (result.1, (result.2, Phase.done))) <$>
          (base setup codec checks seed (.inl (.inr (.create pin keyId)))).run state.1
      else keep setup codec checks seed (.inl (.inr (.create pin keyId))) state
  | .inl (.inr (.bundle index)) => fun state =>
      if state.2 = .created ∧ index = c then
        pure (pre.reply, ({ state.1 with
          owners := state.1.owners.set c pre.bundled
          inits := Function.update state.1.inits c pre.init }, .done))
      else keep setup codec checks seed (.inl (.inr (.bundle index))) state
  | .inl (.inr (.accept raw)) => keep setup codec checks seed (.inl (.inr (.accept raw)))
  | .inl (.inr (.build session payload)) => keep setup codec checks seed (.inl (.inr (.build session payload)))
  | .inl (.inr (.finish index raw)) => keep setup codec checks seed (.inl (.inr (.finish index raw)))
  | .inl (.inr (.hmac key message)) => keep setup codec checks seed (.inl (.inr (.hmac key message)))
  | .inl (.inr (.hash bytes)) => keep setup codec checks seed (.inl (.inr (.hash bytes)))
  | .inl (.inr (.reveal keyId)) => keep setup codec checks seed (.inl (.inr (.reveal keyId)))
  | .inr request => keep setup codec checks seed (.inr request)

/-- The singleton side of one step: the embedding routed into the source14 handler on the singleton state. -/
noncomputable def singleStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (query : (SourceSpec KemSK).Domain)
    (emb : Emb KemSK) (single : State KemSK) : ProbComp (((SourceSpec KemSK).Range query × Emb KemSK) × State KemSK) :=
  (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
    (simulateQ route ((embed setup codec c input query).run emb))).run single

/-- The target's owner in the reassembled state: the drawn created owner before the first bundle, the singleton's owner zero after it. -/
def targetOwner (pre : Pre KemSK) (emb : Emb KemSK) (single : State KemSK) : Owner KemSK :=
  if emb.slot = .fresh then pre.created else single.owners.headD pre.created

open Classical in
/-- The retained Phase 1 bundles in the reassembled state: the embedding's for local owners and for the target before its first bundle, the singleton's owner zero's after it. -/
noncomputable def initsOf (emb : Emb KemSK) (single : State KemSK) (index : Nat) :
    Option PqxdhEd25519EufCma.Phase1Candidate :=
  if emb.owners[index]? = some none ∧ emb.slot ≠ .fresh then single.inits 0 else emb.inits index

/-- The reassembled multi-owner state: the singleton's shared state, the local owners and the target's owner at its slot, and the retained bundles (`initsOf`). -/
noncomputable def multiOf (pre : Pre KemSK) (emb : Emb KemSK) (single : State KemSK) : State KemSK :=
  ⟨single.shared, emb.owners.map fun slot => slot.getD (targetOwner pre emb single), initsOf emb single⟩

/-- The eager phase of a slot. -/
def phaseOf : Slot → Phase
  | .waiting => .waiting
  | .fresh => .created
  | _ => .done

/-- An identity, KEM, prekey or one-time read: the reads a compiled program never issues. -/
def Bad : (SourceSpec KemSK).Domain → Prop
  | .inr (_, field) => field ≠ .kernel
  | _ => False

instance : DecidablePred (Bad (KemSK := KemSK)) := fun query => by
  rcases query with query | ⟨index, field⟩
  · exact isFalse id
  · exact inferInstanceAs (Decidable (field ≠ _))

/-! ## The native handler reads no analysis history -/

/-- A bundle on an absent owner answers nothing and changes nothing. -/
theorem bundle_missing (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat) (state : State KemSK)
    (missing : state.owners[index]? = none) :
    (PqxdhRegistrationSchedule.bundle setup codec index).run state = pure (none, state) := by
  simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind, missing, StateT.run_pure]

/-- Every native step, with field reads, reads neither analysis history. -/
theorem base_stable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (query : (SourceSpec KemSK).Domain) (state : State KemSK) :
    Prod.map id eraseShared <$> (base setup codec checks seed query).run state =
      Prod.map id eraseShared <$> (base setup codec checks seed query).run (eraseShared state) := by
  rcases query with (coin | request) | ⟨index, field⟩
  · simp only [base, PqxdhRegistrationJointRevealSchedule.native, PqxdhRegistrationSchedule.handler, StateT.run_lift,
      map_bind, map_pure]
    rfl
  · cases request with
    | create pin keyId =>
        simp only [base, PqxdhRegistrationJointRevealSchedule.native, PqxdhRegistrationSchedule.handler]
        change Prod.map id eraseShared <$> PqxdhRegistrationSchedule.create setup pin keyId state =
          Prod.map id eraseShared <$> PqxdhRegistrationSchedule.create setup pin keyId (eraseShared state)
        rw [PqxdhRegistrationSchedule.create_source, PqxdhRegistrationSchedule.create_source]
        simp only [map_bind, map_pure]
        rfl
    | bundle index =>
        simp only [base, PqxdhRegistrationJointRevealSchedule.native, PqxdhRegistrationSchedule.handler]
        cases found : state.owners[index]? with
        | none =>
            have erased : (eraseShared state).owners[index]? = none := found
            rw [bundle_missing setup codec index state found, bundle_missing setup codec index _ erased]
            rfl
        | some owner =>
            have erased : (eraseShared state).owners[index]? = some owner := found
            change Prod.map id eraseShared <$> PqxdhRegistrationSchedule.bundle setup codec index state =
              Prod.map id eraseShared <$> PqxdhRegistrationSchedule.bundle setup codec index (eraseShared state)
            rw [PqxdhRegistrationSchedule.bundle_source setup codec index state owner found,
              PqxdhRegistrationSchedule.bundle_source setup codec index _ owner erased, Functor.map_map, Functor.map_map]
            rfl
    | accept raw =>
        exact onShared_stable _ (PqxdhDeploymentServerAuthStable.accept_stable _ _ _ _ _ _) state
    | build session payload =>
        exact onShared_stable _ (PqxdhDeploymentServerAuthStable.build_stable _ _ _ _ _) state
    | finish index raw =>
        simp only [base, PqxdhRegistrationJointRevealSchedule.native, PqxdhRegistrationSchedule.handler]
        cases found : state.owners[index]? with
        | none =>
            have erased : (eraseShared state).owners[index]? = none := found
            rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw state found,
              PqxdhRegistrationSchedule.finish_missing setup codec index raw _ erased]
            rfl
        | some owner =>
            have erased : (eraseShared state).owners[index]? = some owner := found
            change Prod.map id eraseShared <$> PqxdhRegistrationSchedule.finish setup codec index raw state =
              Prod.map id eraseShared <$> PqxdhRegistrationSchedule.finish setup codec index raw (eraseShared state)
            rw [PqxdhRegistrationSchedule.finish_source setup codec index raw state owner found,
              PqxdhRegistrationSchedule.finish_source setup codec index raw _ owner erased, Functor.map_map, Functor.map_map]
            have stable := PqxdhDeploymentServerAuthStable.ownerFinish_stable setup codec (state.inits index) raw owner
              state.shared
            have mapped := congrArg (fun computation => (fun result : (Option Pqxdh.Bytes × Owner KemSK) × NativeState KemSK =>
              (result.1.1, eraseShared ({ shared := result.2, owners := state.owners.set index result.1.2, inits := state.inits } :
                State KemSK))) <$> computation) stable
            simp only [Functor.map_map] at mapped
            exact mapped
    | hmac key message =>
        exact onShared_stable _ (PqxdhDeploymentServerAuthStable.hmac_stable _ _ _ _ _) state
    | hash bytes =>
        exact onShared_stable _ (PqxdhDeploymentServerAuthStable.hash_stable _) state
    | reveal keyId =>
        exact onShared_stable _ (PqxdhDeploymentServerAuthStable.reveal_stable _) state
  · simp only [base, PqxdhRegistrationJointRevealSchedule.native, StateT.run, map_pure]
    rfl

/-! ## One step -/

/-- A stable shared operation, on the singleton state and on the reassembled state, gives the same reassembled result up to the histories. -/
theorem shared_commute {α : Type} (op : NativeGame KemSK α) (stable : Stable op) (pre : Pre KemSK) (emb : Emb KemSK)
    (single : State KemSK) (phase : Phase) :
    (fun result => (result.1, (eraseShared (multiOf pre emb result.2), phase))) <$>
        (PqxdhRegistrationSchedule.onShared op).run single =
      (fun result => (result.1, (eraseShared result.2, phase))) <$>
        (PqxdhRegistrationSchedule.onShared op).run (eraseShared (multiOf pre emb single)) := by
  rw [PqxdhRegistrationSchedule.onShared_run, PqxdhRegistrationSchedule.onShared_run]
  simp only [Functor.map_map]
  let owners := (multiOf pre emb single).owners
  let inits := (multiOf pre emb single).inits
  have same := congrArg (fun computation => (fun result => (result.1,
    ((⟨result.2, owners, inits⟩ : State KemSK)), phase)) <$> computation) (stable single.shared)
  simp only [Functor.map_map] at same
  exact same

/-- A forwarded ServerAuth query: the embedding keeps its state and the singleton runs the routed source14 query. -/
theorem singleStep_lift (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (query : (SourceSpec KemSK).Domain) (emb : Emb KemSK)
    (single : State KemSK) (work : OracleComp ServerAuthSpec ((SourceSpec KemSK).Range query))
    (lifted : embed setup codec c input query = StateT.lift work) :
    singleStep setup codec checks seed c input query emb single =
      (fun result => ((result.1, emb), result.2)) <$>
        (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed) (simulateQ route work)).run single := by
  simp only [singleStep, lifted, StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map]

/-- The embedding's state is ready for one step: only index `c` can hold the target, it holds it exactly from the target's creation on, the singleton has one owner, which is the drawn bundled owner until the first bundle and afterwards in InitSent or aborted, the first bundle was not rejected, the drawn created owner is Fresh, and the singleton retains the drawn Phase 1 bundle. -/
structure Ready (c : Nat) (pre : Pre KemSK) (emb : Emb KemSK) (single : State KemSK) : Prop where
  target : ∀ index, emb.owners[index]? = some none → index = c
  noTarget : emb.slot = .waiting ∨ emb.slot = .released → emb.owners[c]? ≠ some none
  placed : emb.slot = .fresh ∨ emb.slot = .bundled → emb.owners[c]? = some none
  singleton : ∃ owner, single.owners = [owner] ∧
    (emb.slot = .waiting ∨ emb.slot = .fresh ∨ emb.slot = .released → owner = pre.bundled) ∧
    (emb.slot = .bundled →
      PqxdhDeploymentEligibility.phaseClass owner.beacon.phase = .initSent ∨
        PqxdhDeploymentEligibility.phaseClass owner.beacon.phase = .aborted)
  notFailed : emb.slot ≠ .failed
  createdFresh : PqxdhDeploymentEligibility.phaseClass pre.created.beacon.phase = .fresh
  /-- The singleton's owner zero retains the drawn first bundle's Phase 1 bundle. -/
  init : single.inits 0 = pre.init

/-- An owner that is not established has no kernel to read. -/
theorem kernel_none (owner : Owner KemSK)
    (open_ : PqxdhDeploymentEligibility.phaseClass owner.beacon.phase ≠ .established) :
    PqxdhRegistrationJointLiveRead.value (KemSK := KemSK) .kernel owner = none := by
  rcases phase : owner.beacon.phase with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩
  all_goals simp_all [PqxdhRegistrationJointLiveRead.value, PqxdhRegistrationJointLiveRead.localValue,
    PqxdhDeploymentEligibility.phaseClass]

/-- The target's owner in the reassembled state is never established on a ready state. -/
theorem target_open (c : Nat) (pre : Pre KemSK) (emb : Emb KemSK) (single : State KemSK) (ready : Ready c pre emb single)
    (index : Nat) (held : emb.owners[index]? = some none) :
    PqxdhDeploymentEligibility.phaseClass (targetOwner pre emb single).beacon.phase ≠ .established := by
  have atC := ready.target index held
  subst atC
  obtain ⟨owner, single_eq, drawn, sent⟩ := ready.singleton
  unfold targetOwner
  split
  · rw [ready.createdFresh]
    decide
  · rename_i notFresh
    rw [single_eq]
    simp only [List.headD_cons]
    cases slot : emb.slot with
    | waiting => exact absurd held (ready.noTarget (Or.inl slot))
    | released => exact absurd held (ready.noTarget (Or.inr slot))
    | fresh => exact absurd slot notFresh
    | failed => exact absurd slot ready.notFailed
    | bundled =>
        rcases sent slot with sentPhase | abortedPhase
        · rw [sentPhase]
          decide
        · rw [abortedPhase]
          decide

/-- The native constructor is the local constructor followed by appending its owner. -/
theorem create_local (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64) (state : State KemSK) :
    PqxdhRegistrationSchedule.create setup pin keyId state =
      (fun owner => (state.owners.length, { state with owners := state.owners ++ [owner] })) <$>
        localCreate setup pin keyId := by
  rw [PqxdhRegistrationSchedule.create_source]
  simp only [localCreate, map_bind, map_pure]

/-- Without a target slot, the default of the reassembly is never used. -/
theorem map_getD_irrel (owners : List (Option (Owner KemSK))) (noTarget : ∀ index : Nat, owners[index]? ≠ some none)
    (first second : Owner KemSK) :
    owners.map (fun slot => slot.getD first) = owners.map (fun slot => slot.getD second) := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map]
  cases found : owners[index]? with
  | none => rfl
  | some slot =>
      cases slot with
      | some owner => rfl
      | none => exact absurd found (noTarget index)

/-- The target's owner depends only on whether the slot is fresh. -/
theorem targetOwner_slot (pre : Pre KemSK) (first second : Emb KemSK) (single : State KemSK)
    (same : first.slot = .fresh ↔ second.slot = .fresh) : targetOwner pre first single = targetOwner pre second single := by
  unfold targetOwner
  by_cases fresh : first.slot = .fresh
  · rw [ite_eq_left fresh, ite_eq_left (same.mp fresh)]
  · rw [ite_eq_right fresh, ite_eq_right (fun other => fresh (same.mpr other))]

open Classical in
/-- The reassembled retained bundles depend only on where the bundled target sits and on the embedding's own retained bundles. -/
theorem initsOf_congr (first second : Emb KemSK) (single : State KemSK)
    (target : ∀ index : Nat, (first.owners[index]? = some none ∧ first.slot ≠ .fresh) ↔
      (second.owners[index]? = some none ∧ second.slot ≠ .fresh))
    (same : first.inits = second.inits) : initsOf first single = initsOf second single := by
  funext index
  simp only [initsOf, target index, same]

/-- Without a bundled target, the reassembled retained bundles are the embedding's. -/
theorem initsOf_local (emb : Emb KemSK) (single : State KemSK)
    (local_ : ∀ index : Nat, ¬ (emb.owners[index]? = some none ∧ emb.slot ≠ .fresh)) : initsOf emb single = emb.inits := by
  funext index
  simp only [initsOf, local_ index, ite_false]

/-- Appending a local owner adds no target entry. -/
theorem append_some_target (owners : List (Option (Owner KemSK))) (owner : Owner KemSK) (index : Nat) :
    (owners ++ [some owner])[index]? = some none ↔ owners[index]? = some none := by
  rcases Nat.lt_or_ge index owners.length with inside | outside
  · rw [List.getElem?_append_left inside]
  · rw [List.getElem?_append_right outside, List.getElem?_eq_none outside]
    cases shift : index - owners.length <;> simp

open Classical in
/-- The embedding's create, unfolded. -/
theorem embed_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat) (input : AuthInput)
    (pin : Word32) (keyId : Std.U64) (emb : Emb KemSK) :
    (embed setup codec c input (.inl (.inr (.create pin keyId)))).run emb =
      if emb.owners.length = c ∧ emb.slot = .waiting ∧ (pin, keyId) = inputBinding input then
        pure (c, { emb with owners := emb.owners ++ [none], slot := .fresh })
      else
        (fun owner => (emb.owners.length, { emb with
          owners := emb.owners ++ [some owner]
          slot := if emb.owners.length = c ∧ emb.slot = .waiting then .released else emb.slot })) <$>
          coins (localCreate setup pin keyId) := rfl

open Classical in
/-- The eager create, unfolded. -/
theorem eager_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) (pin : Word32) (keyId : Std.U64)
    (state : State KemSK × Phase) :
    (eager setup codec checks seed c binding pre (.inl (.inr (.create pin keyId)))).run state =
      if state.2 = .waiting ∧ state.1.owners.length = c then
        if (pin, keyId) = binding then pure (c, ({ state.1 with owners := state.1.owners ++ [pre.created] }, .created))
        else (fun result => (result.1, (result.2, Phase.done))) <$>
          (base setup codec checks seed (.inl (.inr (.create pin keyId)))).run state.1
      else (keep setup codec checks seed (.inl (.inr (.create pin keyId)))).run state := rfl

/-- On a ready state whose slot is not taken, no entry holds the target. -/
theorem ready_noTarget (c : Nat) (pre : Pre KemSK) (emb : Emb KemSK) (single : State KemSK) (ready : Ready c pre emb single)
    (free : emb.slot = .waiting ∨ emb.slot = .released) : ∀ index : Nat, emb.owners[index]? ≠ some none := by
  intro index held
  have atC := ready.target index held
  subst atC
  exact ready.noTarget free held

/-- The native create, as a base step. -/
theorem base_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (pin : Word32) (keyId : Std.U64) (state : State KemSK) :
    (base setup codec checks seed (.inl (.inr (.create pin keyId)))).run state =
      PqxdhRegistrationSchedule.create setup pin keyId state := rfl

/-- A field read: the embedding answers from its local owner, or nothing for the target, and nothing changes. -/
theorem singleStep_read (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (index : Nat) (field : PqxdhRegistrationJointLiveRead.Field)
    (emb : Emb KemSK) (single : State KemSK) :
    singleStep setup codec checks seed c input (.inr (index, field)) emb single =
      pure (((emb.owners[index]?).bind fun slot => slot.bind (PqxdhRegistrationJointLiveRead.value field), emb), single) := by
  change (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed) (simulateQ route (pure _))).run single = _
  simp

/-- One create step commutes with the reassembly. -/
theorem step_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (binding : Word32 × Std.U64) (pre : Pre KemSK)
    (bound : inputBinding input = binding) (pin : Word32) (keyId : Std.U64) (emb : Emb KemSK) (single : State KemSK)
    (ready : Ready c pre emb single) :
    (fun result => (result.1.1, (eraseShared (multiOf pre result.1.2 result.2), phaseOf result.1.2.slot))) <$>
        singleStep setup codec checks seed c input (.inl (.inr (.create pin keyId))) emb single =
      (fun result => (result.1, (eraseShared result.2.1, result.2.2))) <$>
        (eager setup codec checks seed c binding pre (.inl (.inr (.create pin keyId)))).run
          (eraseShared (multiOf pre emb single), phaseOf emb.slot) := by
  have length : (eraseShared (multiOf pre emb single)).owners.length = emb.owners.length := by
    simp [eraseShared, multiOf]
  by_cases target : emb.owners.length = c ∧ emb.slot = .waiting ∧ (pin, keyId) = inputBinding input
  · obtain ⟨atC, waiting, chosen⟩ := target
    have free := ready_noTarget c pre emb single ready (Or.inl waiting)
    simp only [singleStep]
    rw [embed_create, ite_eq_left ⟨atC, waiting, chosen⟩, eager_create,
      ite_eq_left ⟨by simp [waiting, phaseOf], by rw [length, atC]⟩, ite_eq_left (chosen.trans bound)]
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    congr 2
    simp only [multiOf, eraseShared, List.map_append, List.map_cons, List.map_nil, Option.getD_none]
    have created : targetOwner pre ⟨emb.owners ++ [none], .fresh, emb.inits⟩ single = pre.created := by
      simp [targetOwner]
    have inits : initsOf ⟨emb.owners ++ [none], .fresh, emb.inits⟩ single = initsOf emb single := by
      rw [initsOf_local _ _ (fun _ held => held.2 rfl), initsOf_local _ _ (fun index held => free index held.1)]
    rw [created, map_getD_irrel emb.owners free pre.created (targetOwner pre emb single), inits]
    rfl
  · simp only [singleStep]
    rw [embed_create, ite_eq_right target, simulateQ_map, simulateQ_map, StateT.run_map,
      PqxdhDeploymentServerAuthEmbed.coins_route, Functor.map_map, eager_create]
    by_cases opening : phaseOf emb.slot = .waiting ∧ (eraseShared (multiOf pre emb single)).owners.length = c
    · have waiting : emb.slot = .waiting := by
        cases slot : emb.slot <;> simp_all [phaseOf]
      have atC : emb.owners.length = c := length ▸ opening.2
      have other : (pin, keyId) ≠ binding := fun same => target ⟨atC, waiting, same.trans bound.symm⟩
      rw [ite_eq_left opening, ite_eq_right other, base_create, create_local]
      simp only [Functor.map_map]
      congr 1
      funext owner
      simp only [atC, waiting, and_self, ite_true, length]
      have same : targetOwner pre ⟨emb.owners ++ [some owner], .released, emb.inits⟩ single =
          targetOwner pre emb single :=
        targetOwner_slot pre _ emb single (by simp [waiting])
      have free := ready_noTarget c pre emb single ready (Or.inl waiting)
      have inits : initsOf ⟨emb.owners ++ [some owner], .released, emb.inits⟩ single = initsOf emb single := by
        rw [initsOf_local _ _ (fun index held => free index ((append_some_target _ _ _).mp held.1)),
          initsOf_local _ _ (fun index held => free index held.1)]
      simp only [multiOf, eraseShared, List.map_append, List.map_cons, List.map_nil, Option.getD_some, same,
        phaseOf, inits]
      rfl
    · have keepSlot : ¬ (emb.owners.length = c ∧ emb.slot = .waiting) := by
        rintro ⟨atC, waiting⟩
        exact opening ⟨by simp [waiting, phaseOf], by rw [length, atC]⟩
      rw [ite_eq_right opening, keep_run, base_create, create_local]
      simp only [Functor.map_map]
      congr 1
      funext owner
      simp only [keepSlot, ite_false, length]
      have same : targetOwner pre ⟨emb.owners ++ [some owner], emb.slot, emb.inits⟩ single =
          targetOwner pre emb single :=
        targetOwner_slot pre _ emb single Iff.rfl
      have inits : initsOf ⟨emb.owners ++ [some owner], emb.slot, emb.inits⟩ single = initsOf emb single :=
        initsOf_congr _ _ _ (fun index => by simp only [append_some_target]) rfl
      simp only [multiOf, eraseShared, List.map_append, List.map_cons, List.map_nil, Option.getD_some, same, inits]
      rfl

/-- The embedding's bundle, unfolded. -/
theorem embed_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat) (input : AuthInput)
    (index : Nat) (emb : Emb KemSK) :
    (embed setup codec c input (.inl (.inr (.bundle index)))).run emb =
      match emb.owners[index]? with
      | none => pure (none, emb)
      | some none =>
          if emb.slot = .fresh then
            pure (input.phase1, { emb with slot := if input.phase1.isSome then .bundled else .failed })
          else pure (none, emb)
      | some (some owner) =>
          (fun result => (result.1.1, { emb with
            owners := emb.owners.set index (some result.1.2)
            inits := Function.update emb.inits index result.2 })) <$>
            coins (PqxdhDeploymentServerAuthEmbed.localBundleLog setup codec index owner (emb.inits index)) := rfl

open Classical in
/-- The eager bundle, unfolded. -/
theorem eager_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) (index : Nat)
    (state : State KemSK × Phase) :
    (eager setup codec checks seed c binding pre (.inl (.inr (.bundle index)))).run state =
      if state.2 = .created ∧ index = c then
        pure (pre.reply, ({ state.1 with
          owners := state.1.owners.set c pre.bundled
          inits := Function.update state.1.inits c pre.init }, .done))
      else (keep setup codec checks seed (.inl (.inr (.bundle index)))).run state := rfl

/-- The native bundle, as a base step. -/
theorem base_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (state : State KemSK) :
    (base setup codec checks seed (.inl (.inr (.bundle index)))).run state =
      (PqxdhRegistrationSchedule.bundle setup codec index).run state := rfl

/-- The native bundle of a present owner, in run form. -/
theorem bundle_found (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat) (state : State KemSK)
    (owner : Owner KemSK) (found : state.owners[index]? = some owner) :
    (PqxdhRegistrationSchedule.bundle setup codec index).run state =
      (fun result => (result.1.1, { state with
        owners := state.owners.set index result.1.2
        inits := Function.update state.inits index result.2 })) <$>
        PqxdhDeploymentServerAuthEmbed.localBundleLog setup codec index owner (state.inits index) :=
  PqxdhRegistrationSchedule.bundle_source setup codec index state owner found

/-- With the target only at `c`, changing the reassembly default changes only the entry at `c`. -/
theorem map_getD_set (owners : List (Option (Owner KemSK))) (c : Nat) (target : ∀ index : Nat, owners[index]? = some none → index = c)
    (placed : owners[c]? = some none) (first second : Owner KemSK) :
    owners.map (fun slot => slot.getD second) = (owners.map (fun slot => slot.getD first)).set c second := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, List.getElem?_set]
  by_cases same : c = index
  · subst same
    obtain ⟨bound, entry⟩ := List.getElem?_eq_some_iff.mp placed
    simp [bound, entry]
  · rw [ite_eq_right same]
    cases found : owners[index]? with
    | none => rfl
    | some slot =>
        cases slot with
        | some owner => rfl
        | none => exact absurd (target index found).symm same

/-- A bundle on a phase that is neither Fresh variant answers nothing and keeps the owner. -/
theorem bundle_sent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat) (owner : Owner KemSK)
    (sent : PqxdhDeploymentEligibility.phaseClass owner.beacon.phase ≠ .fresh) :
    localBundle setup codec index owner = pure (none, owner) := by
  unfold localBundle
  rcases phase : owner.beacon.phase with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩
  all_goals simp_all [PqxdhLivePhase1Bundle.bundle, PqxdhDeploymentEligibility.phaseClass]

/-- A logged bundle on a phase that is neither Fresh variant answers nothing and keeps the owner and its retained bundle. -/
theorem bundleLog_sent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat) (owner : Owner KemSK)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate)
    (sent : PqxdhDeploymentEligibility.phaseClass owner.beacon.phase ≠ .fresh) :
    PqxdhDeploymentServerAuthEmbed.localBundleLog setup codec index owner retained = pure ((none, owner), retained) := by
  unfold PqxdhDeploymentServerAuthEmbed.localBundleLog
  rcases phase : owner.beacon.phase with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩
  all_goals simp_all [PqxdhLivePhase1Bundle.bundle, PqxdhDeploymentEligibility.phaseClass]

/-- A local owner's retained bundle is the embedding's in the reassembly. -/
theorem initsOf_owner (emb : Emb KemSK) (single : State KemSK) (index : Nat) (owner : Owner KemSK)
    (found : emb.owners[index]? = some (some owner)) : initsOf emb single index = emb.inits index := by
  simp [initsOf, found]

/-- Updating a local owner's slot and retained bundle updates the reassembled retained bundles at that slot only. -/
theorem initsOf_set (emb : Emb KemSK) (single : State KemSK) (index : Nat) (owner updated : Owner KemSK)
    (found : emb.owners[index]? = some (some owner)) (retained : Option PqxdhEd25519EufCma.Phase1Candidate) :
    initsOf { emb with owners := emb.owners.set index (some updated), inits := Function.update emb.inits index retained }
        single = Function.update (initsOf emb single) index retained := by
  funext other
  by_cases same : other = index
  · subst same
    have bound : other < emb.owners.length := (List.getElem?_eq_some_iff.mp found).1
    simp [initsOf, List.getElem?_set_self bound]
  · have kept : (emb.owners.set index (some updated))[other]? = emb.owners[other]? := by
      simp [Ne.symm same]
    simp only [initsOf, Function.update_of_ne same]
    split_ifs <;> simp_all

/-- The target's first bundle, on a ready state: the reassembled retained bundles gain the drawn bundle at `c` and nothing else. -/
theorem initsOf_first (c : Nat) (pre : Pre KemSK) (emb : Emb KemSK) (single : State KemSK) (ready : Ready c pre emb single)
    (fresh : emb.slot = .fresh) (slot : Slot) (notFresh : slot ≠ .fresh) :
    initsOf { emb with slot := slot } single = Function.update (initsOf emb single) c pre.init := by
  funext other
  by_cases same : other = c
  · subst same
    simp [initsOf, ready.placed (Or.inl fresh), notFresh, ready.init]
  · have notTarget : ¬ emb.owners[other]? = some none := fun held => same (ready.target other held)
    simp [initsOf, notTarget, Function.update_of_ne same]

/-- One bundle step commutes with the reassembly. -/
theorem step_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (binding : Word32 × Std.U64) (pre : Pre KemSK)
    (published : input.phase1 = pre.reply) (index : Nat) (emb : Emb KemSK) (single : State KemSK)
    (ready : Ready c pre emb single) :
    (fun result => (result.1.1, (eraseShared (multiOf pre result.1.2 result.2), phaseOf result.1.2.slot))) <$>
        singleStep setup codec checks seed c input (.inl (.inr (.bundle index))) emb single =
      (fun result => (result.1, (eraseShared result.2.1, result.2.2))) <$>
        (eager setup codec checks seed c binding pre (.inl (.inr (.bundle index)))).run
          (eraseShared (multiOf pre emb single), phaseOf emb.slot) := by
  have found_m : (eraseShared (multiOf pre emb single)).owners[index]? =
      (emb.owners[index]?).map fun slot => slot.getD (targetOwner pre emb single) := by
    simp [eraseShared, multiOf, List.getElem?_map]
  simp only [singleStep]
  rw [embed_bundle, eager_bundle]
  cases found : emb.owners[index]? with
  | none =>
      have notTarget : ¬ (phaseOf emb.slot = .created ∧ index = c) := by
        rintro ⟨created, rfl⟩
        have fresh : emb.slot = .fresh := by cases slot : emb.slot <;> simp_all [phaseOf]
        rw [ready.placed (Or.inl fresh)] at found
        cases found
      rw [ite_eq_right notTarget, keep_run, base_bundle,
        bundle_missing setup codec index _ (by rw [found_m, found]; rfl)]
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
  | some slot =>
      cases slot with
      | none =>
          have atC := ready.target index found
          subst atC
          obtain ⟨owner, single_eq, drawn, sent⟩ := ready.singleton
          by_cases fresh : emb.slot = .fresh
          · have created : phaseOf emb.slot = .created ∧ index = index := ⟨by simp [fresh, phaseOf], rfl⟩
            rw [ite_eq_left fresh, ite_eq_left created]
            simp only [simulateQ_pure, StateT.run_pure, map_pure, published]
            have bundled : targetOwner pre { emb with slot := if pre.reply.isSome then .bundled else .failed } single =
                pre.bundled := by
              have notFresh : (if pre.reply.isSome then Slot.bundled else Slot.failed) ≠ .fresh := by
                split <;> simp
              simp only [targetOwner, notFresh, ite_false, single_eq, List.headD_cons]
              exact drawn (Or.inr (Or.inl fresh))
            have phase : phaseOf (if pre.reply.isSome then Slot.bundled else Slot.failed) = .done := by
              split <;> rfl
            have notFresh : (if pre.reply.isSome then Slot.bundled else Slot.failed) ≠ .fresh := by
              split <;> simp
            simp only [multiOf, eraseShared, bundled, phase,
              initsOf_first index pre emb single ready fresh _ notFresh]
            rw [map_getD_set emb.owners index ready.target found (targetOwner pre emb single) pre.bundled]
            rfl
          · have bundledSlot : emb.slot = .bundled := by
              cases slot : emb.slot with
              | waiting => exact absurd found (ready.noTarget (Or.inl slot))
              | released => exact absurd found (ready.noTarget (Or.inr slot))
              | fresh => exact absurd slot fresh
              | failed => exact absurd slot ready.notFailed
              | bundled => rfl
            have notCreated : ¬ (phaseOf emb.slot = .created ∧ index = index) := by
              simp [bundledSlot, phaseOf]
            have target : targetOwner pre emb single = owner := by
              simp only [targetOwner, fresh, ite_false, single_eq, List.headD_cons]
            have held : (eraseShared (multiOf pre emb single)).owners[index]? = some owner := by
              rw [found_m, found, Option.map_some, Option.getD_none, target]
            rw [ite_eq_right fresh, ite_eq_right notCreated, keep_run, base_bundle,
              bundle_found setup codec index _ owner held]
            dsimp only
            have phaseSent : PqxdhDeploymentEligibility.phaseClass owner.beacon.phase ≠ .fresh := by
              rcases sent bundledSlot with initSent | aborted
              · rw [initSent]
                decide
              · rw [aborted]
                decide
            rw [bundleLog_sent setup codec index owner _ phaseSent]
            simp only [simulateQ_pure, StateT.run_pure, map_pure, Function.update_eq_self]
            obtain ⟨bound, entry⟩ := List.getElem?_eq_some_iff.mp held
            rw [← entry, List.set_getElem_self bound]
            rfl
      | some owner =>
          have notCreated : ¬ (phaseOf emb.slot = .created ∧ index = c) := by
            rintro ⟨created, rfl⟩
            have fresh : emb.slot = .fresh := by cases slot : emb.slot <;> simp_all [phaseOf]
            rw [ready.placed (Or.inl fresh)] at found
            cases found
          have held : (eraseShared (multiOf pre emb single)).owners[index]? = some owner := by
            rw [found_m, found, Option.map_some, Option.getD_some]
          rw [ite_eq_right notCreated, keep_run, base_bundle, bundle_found setup codec index _ owner held]
          dsimp only
          rw [simulateQ_map, simulateQ_map, StateT.run_map, PqxdhDeploymentServerAuthEmbed.coins_route]
          have retained : (eraseShared (multiOf pre emb single)).inits index = emb.inits index :=
            initsOf_owner emb single index owner found
          rw [retained]
          simp only [Functor.map_map]
          congr 1
          funext result
          simp only [multiOf, eraseShared, List.map_set, Option.getD_some,
            initsOf_set emb single index owner result.1.2 found result.2]
          rfl

/-- The embedding's finish, unfolded. -/
theorem embed_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (c : Nat) (input : AuthInput)
    (index : Nat) (raw : Pqxdh.Bytes) (emb : Emb KemSK) :
    (embed setup codec c input (.inl (.inr (.finish index raw)))).run emb =
      match emb.owners[index]? with
      | none => pure (none, emb)
      | some none =>
          if emb.slot = .bundled then (fun reply => (reply, emb)) <$> forward (.finish raw)
          else pure (none, emb)
      | some (some owner) =>
          (fun result => (result.1, { emb with owners := emb.owners.set index (some result.2) })) <$>
            PqxdhDeploymentServerAuthEmbed.localFinish setup codec (emb.inits index) raw owner := rfl

/-- The native finish, as a base step. -/
theorem base_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) :
    (base setup codec checks seed (.inl (.inr (.finish index raw)))).run state =
      (PqxdhRegistrationSchedule.finish setup codec index raw).run state := rfl

/-- The native finish of a present owner, in run form. -/
theorem finish_found (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat) (raw : Pqxdh.Bytes)
    (state : State KemSK) (owner : Owner KemSK) (found : state.owners[index]? = some owner) :
    (PqxdhRegistrationSchedule.finish setup codec index raw).run state =
      (fun result => (result.1.1, ({ state with shared := result.2, owners := state.owners.set index result.1.2 } :
        State KemSK))) <$>
        (PqxdhRegistrationSchedule.ownerFinish setup codec (state.inits index) raw owner).run state.shared :=
  PqxdhRegistrationSchedule.finish_source setup codec index raw state owner found

/-- A finish outside InitSent answers nothing and keeps the owner, before any callback. -/
theorem nativeOwner_open (binding : session.CompletedRegistrationBinding) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (owner : Owner KemSK)
    (open_ : PqxdhDeploymentEligibility.phaseClass owner.beacon.phase ≠ .initSent) :
    PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := binding) (X := IdentitySeed) (Response := Response)
      decode raw owner = pure (none, owner) := by
  rcases phase : owner.beacon.phase with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩
  all_goals simp_all [PqxdhBeaconPhase2Publication.nativeOwner, PqxdhBeaconPhase2Publication.owner,
    PqxdhDeploymentEligibility.phaseClass]

/-- A hashed owner finish outside InitSent answers nothing and keeps the owner, before any hash or callback. -/
theorem ownerFinish_open (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes) (owner : Owner KemSK)
    (open_ : PqxdhDeploymentEligibility.phaseClass owner.beacon.phase ≠ .initSent) :
    PqxdhRegistrationSchedule.ownerFinish setup codec retained raw owner = pure (none, owner) := by
  unfold PqxdhRegistrationSchedule.ownerFinish
  rcases phase : owner.beacon.phase with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩
  all_goals simp_all [PqxdhDeploymentEligibility.phaseClass]

/-- Replacing a local owner keeps the reassembled retained bundles. -/
theorem initsOf_setOwner (emb : Emb KemSK) (single : State KemSK) (index : Nat) (owner updated : Owner KemSK)
    (found : emb.owners[index]? = some (some owner)) :
    initsOf { emb with owners := emb.owners.set index (some updated) } single = initsOf emb single := by
  refine initsOf_congr _ _ _ (fun other => ?_) rfl
  by_cases same : other = index
  · subst same
    have bound : other < emb.owners.length := (List.getElem?_eq_some_iff.mp found).1
    simp [List.getElem?_set_self bound, found]
  · simp [Ne.symm same]

/-- Erasing after reassembling is reassembling from the erased singleton state. -/
theorem erase_multiOf (pre : Pre KemSK) (emb : Emb KemSK) (single : State KemSK) :
    eraseShared (multiOf pre emb single) = multiOf pre emb (eraseShared single) := rfl

/-- A map that reads the shared state only after erasure has the same image before and after erasing the input. -/
theorem stable_map {α β : Type} (op : NativeGame KemSK α) (stable : Stable op) (f : α × NativeState KemSK → β)
    (reads : ∀ result, f result = f (Prod.map id eraseObservers result)) (state : NativeState KemSK) :
    f <$> op.run state = f <$> op.run (eraseObservers state) := by
  calc f <$> op.run state = (f ∘ Prod.map id eraseObservers) <$> op.run state :=
        congrArg (· <$> op.run state) (funext reads)
    _ = f <$> (Prod.map id eraseObservers <$> op.run state) := by rw [Functor.map_map]; rfl
    _ = f <$> (Prod.map id eraseObservers <$> op.run (eraseObservers state)) := by rw [stable state]
    _ = (f ∘ Prod.map id eraseObservers) <$> op.run (eraseObservers state) := by rw [Functor.map_map]; rfl
    _ = f <$> op.run (eraseObservers state) := congrArg (· <$> op.run (eraseObservers state)) (funext reads).symm

/-- One finish step commutes with the reassembly. -/
theorem step_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (binding : Word32 × Std.U64) (pre : Pre KemSK)
    (index : Nat) (raw : Pqxdh.Bytes) (emb : Emb KemSK) (single : State KemSK) (ready : Ready c pre emb single) :
    (fun result => (result.1.1, (eraseShared (multiOf pre result.1.2 result.2), phaseOf result.1.2.slot))) <$>
        singleStep setup codec checks seed c input (.inl (.inr (.finish index raw))) emb single =
      (fun result => (result.1, (eraseShared result.2.1, result.2.2))) <$>
        (eager setup codec checks seed c binding pre (.inl (.inr (.finish index raw)))).run
          (eraseShared (multiOf pre emb single), phaseOf emb.slot) := by
  have found_m : (eraseShared (multiOf pre emb single)).owners[index]? =
      (emb.owners[index]?).map fun slot => slot.getD (targetOwner pre emb single) := by
    simp [eraseShared, multiOf, List.getElem?_map]
  simp only [singleStep, eager, keep_run, base_finish]
  rw [embed_finish]
  cases found : emb.owners[index]? with
  | none =>
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw _ (by rw [found_m, found]; rfl)]
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
  | some slot =>
      cases slot with
      | none =>
          have atC := ready.target index found
          subst atC
          obtain ⟨owner, single_eq, drawn, sent⟩ := ready.singleton
          by_cases bundled : emb.slot = .bundled
          · have notFresh : emb.slot ≠ .fresh := by simp [bundled]
            have target : targetOwner pre emb single = owner := by
              simp only [targetOwner, notFresh, ite_false, single_eq, List.headD_cons]
            have held : (eraseShared (multiOf pre emb single)).owners[index]? = some owner := by
              rw [found_m, found, Option.map_some, Option.getD_none, target]
            have zero : single.owners[0]? = some owner := by simp [single_eq]
            have retained : (eraseShared (multiOf pre emb single)).inits index = single.inits 0 := by
              simp [eraseShared, multiOf, initsOf, found, notFresh]
            rw [ite_eq_left bundled, finish_found setup codec index raw _ owner held, retained]
            simp only [forward, simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
              route, StateT.run_map, PqxdhRegistrationSchedule.handler]
            rw [finish_found setup codec 0 raw single owner zero]
            simp only [Functor.map_map]
            have rhs := stable_map _ (PqxdhDeploymentServerAuthStable.ownerFinish_stable setup codec (single.inits 0) raw
              owner)
              (fun result : (Option Pqxdh.Bytes × Owner KemSK) × NativeState KemSK =>
                (result.1.1, (eraseShared (⟨result.2,
                  (eraseShared (multiOf pre emb single)).owners.set index result.1.2,
                  (eraseShared (multiOf pre emb single)).inits⟩ : State KemSK),
                  Phase.done)))
              (fun _ => rfl) single.shared
            have bundledPhase : phaseOf emb.slot = .done := by simp [bundled, phaseOf]
            rw [bundledPhase, show (eraseShared (multiOf pre emb single)).shared = eraseObservers single.shared from rfl,
              ← rhs]
            congr 1
            funext result
            simp only [multiOf, eraseShared, single_eq, List.set_cons_zero]
            have reassembled := map_getD_set emb.owners index ready.target found owner result.1.2
            simp only [targetOwner, notFresh, ite_false, List.headD_cons, reassembled, single_eq]
            rfl
          · have fresh : emb.slot = .fresh := by
              cases slot : emb.slot with
              | waiting => exact absurd found (ready.noTarget (Or.inl slot))
              | released => exact absurd found (ready.noTarget (Or.inr slot))
              | bundled => exact absurd slot bundled
              | failed => exact absurd slot ready.notFailed
              | fresh => rfl
            have target : targetOwner pre emb single = pre.created := by simp [targetOwner, fresh]
            have held : (eraseShared (multiOf pre emb single)).owners[index]? = some pre.created := by
              rw [found_m, found, Option.map_some, Option.getD_none, target]
            have open_ : PqxdhDeploymentEligibility.phaseClass pre.created.beacon.phase ≠ .initSent := by
              rw [ready.createdFresh]
              decide
            rw [ite_eq_right bundled, finish_found setup codec index raw _ pre.created held,
              ownerFinish_open setup codec _ raw pre.created open_]
            simp only [simulateQ_pure, StateT.run_pure, map_pure]
            obtain ⟨bound, entry⟩ := List.getElem?_eq_some_iff.mp held
            rw [← entry, List.set_getElem_self bound]
            rfl
      | some owner =>
          have held : (eraseShared (multiOf pre emb single)).owners[index]? = some owner := by
            rw [found_m, found, Option.map_some, Option.getD_some]
          have retained : (eraseShared (multiOf pre emb single)).inits index = emb.inits index :=
            initsOf_owner emb single index owner found
          rw [finish_found setup codec index raw _ owner held, retained]
          dsimp only
          rw [simulateQ_map, simulateQ_map, StateT.run_map]
          simp only [Functor.map_map]
          have factor : (fun result : (Option Pqxdh.Bytes × Owner KemSK) × State KemSK =>
              (result.1.1, (eraseShared (multiOf pre { emb with owners := emb.owners.set index (some result.1.2) } result.2),
                phaseOf emb.slot))) =
              (fun result => (result.1.1, (multiOf pre { emb with owners := emb.owners.set index (some result.1.2) } result.2,
                phaseOf emb.slot))) ∘ Prod.map id eraseShared := rfl
          rw [factor, comp_map, PqxdhDeploymentServerAuthStable.localOwnerFinish_route, Functor.map_map]
          have rhs := stable_map _ (PqxdhDeploymentServerAuthStable.ownerFinish_stable setup codec (emb.inits index) raw
            owner)
            (fun result : (Option Pqxdh.Bytes × Owner KemSK) × NativeState KemSK =>
              (result.1.1, (eraseShared (⟨result.2,
                (eraseShared (multiOf pre emb single)).owners.set index result.1.2,
                (eraseShared (multiOf pre emb single)).inits⟩ : State KemSK),
                phaseOf emb.slot)))
            (fun _ => rfl) single.shared
          rw [show (eraseShared (multiOf pre emb single)).shared = eraseObservers single.shared from rfl, ← rhs]
          congr 1
          funext result
          simp only [multiOf, eraseShared, List.map_set, Option.getD_some,
            initsOf_setOwner emb _ index owner result.1.2 found]
          rfl

/-- One step of the singleton side, reassembled, is one eager step on the reassembled state, up to the histories, for every query other than an identity, KEM, prekey or one-time read. -/
theorem step_commute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (input : AuthInput) (binding : Word32 × Std.U64) (pre : Pre KemSK)
    (bound : inputBinding input = binding) (published : input.phase1 = pre.reply)
    (query : (SourceSpec KemSK).Domain) (good : ¬ Bad query) (emb : Emb KemSK) (single : State KemSK)
    (ready : Ready c pre emb single) :
    (fun result => (result.1.1, (eraseShared (multiOf pre result.1.2 result.2), phaseOf result.1.2.slot))) <$>
        singleStep setup codec checks seed c input query emb single =
      (fun result => (result.1, (eraseShared result.2.1, result.2.2))) <$>
        (eager setup codec checks seed c binding pre query).run (eraseShared (multiOf pre emb single), phaseOf emb.slot) := by
  rcases query with (coin | request) | ⟨index, field⟩
  · rw [singleStep_lift setup codec checks seed c input _ emb single _ rfl]
    simp only [route, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      PqxdhRegistrationSchedule.handler, StateT.run_lift, Functor.map_map, eager, keep_run, base,
      PqxdhRegistrationJointRevealSchedule.native, bind_pure_comp]
    rfl
  · cases request with
    | create pin keyId => exact step_create setup codec checks seed c input binding pre bound pin keyId emb single ready
    | bundle index => exact step_bundle setup codec checks seed c input binding pre published index emb single ready
    | accept raw =>
        rw [singleStep_lift setup codec checks seed c input _ emb single _ rfl]
        simp only [route, forward, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          PqxdhRegistrationSchedule.handler, Functor.map_map, eager, keep_run, base,
          PqxdhRegistrationJointRevealSchedule.native]
        exact shared_commute _ (PqxdhDeploymentServerAuthStable.accept_stable _ _ _ _ _ _) pre emb single _
    | build session payload =>
        rw [singleStep_lift setup codec checks seed c input _ emb single _ rfl]
        simp only [route, forward, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          PqxdhRegistrationSchedule.handler, Functor.map_map, eager, keep_run, base,
          PqxdhRegistrationJointRevealSchedule.native]
        exact shared_commute _ (PqxdhDeploymentServerAuthStable.build_stable _ _ _ _ _) pre emb single _
    | finish index raw => exact step_finish setup codec checks seed c input binding pre index raw emb single ready
    | hmac key message =>
        rw [singleStep_lift setup codec checks seed c input _ emb single _ rfl]
        simp only [route, forward, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          PqxdhRegistrationSchedule.handler, Functor.map_map, eager, keep_run, base,
          PqxdhRegistrationJointRevealSchedule.native]
        exact shared_commute _ (PqxdhDeploymentServerAuthStable.hmac_stable _ _ _ _ _) pre emb single _
    | hash bytes =>
        rw [singleStep_lift setup codec checks seed c input _ emb single _ rfl]
        simp only [route, forward, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          PqxdhRegistrationSchedule.handler, Functor.map_map, eager, keep_run, base,
          PqxdhRegistrationJointRevealSchedule.native]
        exact shared_commute _ (PqxdhDeploymentServerAuthStable.hash_stable _) pre emb single _
    | reveal keyId =>
        rw [singleStep_lift setup codec checks seed c input _ emb single _ rfl]
        simp only [route, forward, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          PqxdhRegistrationSchedule.handler, Functor.map_map, eager, keep_run, base,
          PqxdhRegistrationJointRevealSchedule.native]
        exact shared_commute _ (PqxdhDeploymentServerAuthStable.reveal_stable _) pre emb single _
  · have kernel : field = .kernel := by
      by_contra other
      exact good other
    subst kernel
    rw [singleStep_read]
    simp only [eager, keep_run, base, PqxdhRegistrationJointRevealSchedule.native, map_pure]
    change pure _ = (fun result => (result.1, (eraseShared result.2.1, result.2.2))) <$>
      (fun result => (result.1, (result.2, phaseOf emb.slot))) <$>
        (pure (PqxdhRegistrationJointLiveRead.nativeStep (index, .kernel) (eraseShared (multiOf pre emb single))) :
          ProbComp _)
    simp only [map_pure, PqxdhRegistrationJointLiveRead.nativeStep]
    congr 2
    simp only [multiOf, eraseShared, List.getElem?_map]
    cases found : emb.owners[index]? with
    | none => rfl
    | some slot =>
        cases slot with
        | some owner => rfl
        | none =>
            simp only [Option.bind_none, Option.map_some, Option.getD_none, Option.bind_some]
            exact (kernel_none _ (target_open c pre emb single ready index found)).symm

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.keep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.keep_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.bundle_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.bundle_missing

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.base_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.base_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.shared_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.shared_commute

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.singleStep_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.singleStep_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.kernel_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.kernel_none

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.target_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.target_open

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.create_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.create_local

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.map_getD_irrel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.map_getD_irrel

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.targetOwner_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.targetOwner_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.embed_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.embed_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.eager_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.eager_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.ready_noTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.ready_noTarget

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.base_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.base_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.singleStep_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.singleStep_read

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.step_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.step_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.embed_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.embed_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.eager_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.eager_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.base_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.base_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.bundle_found' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.bundle_found

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.map_getD_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.map_getD_set

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.bundle_sent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.bundle_sent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.step_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.step_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.embed_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.embed_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.base_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.base_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.finish_found' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.finish_found

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.nativeOwner_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.nativeOwner_open

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.erase_multiOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.erase_multiOf

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.stable_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.stable_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.step_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.step_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.step_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.step_commute
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_congr
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_local
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.append_some_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.append_some_target
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.bundleLog_sent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.bundleLog_sent
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_owner
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_set
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_first
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.ownerFinish_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.ownerFinish_open
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_setOwner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocal.initsOf_setOwner
