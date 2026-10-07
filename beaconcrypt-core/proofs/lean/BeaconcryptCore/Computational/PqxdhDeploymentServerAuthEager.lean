-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthLocalize

/-! Drawing the target's material before the run (CE-8). The deployment experiment draws owner `c`'s identity seed, prekey and KEM pair at its create and its one-time key at its first bundle; the ServerAuth game draws the target's material before the adversary runs. `draw` is that early draw: the native constructor's three draws with the protected binding, then the native bundle program on the created owner. `swap` shows that the native source14 handler with field reads (`base`) and the eager handler run on a pre-drawn `Pre` (`eager`) give the same output distribution for every program, from every state with at most `c` owners: the early draws are independent of everything before their native positions, so each can be moved past the steps in between (`DeferredSampling.evalSPMF_bind_comm`). `localBundle_index` shows that the bundle program does not depend on the owner's slot index under the native signing callbacks. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhSecretInputKdf
open PqxdhJointGapDh (ScalarBytes)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhDeploymentServerAuthEmbed (SourceSpec Owner localCreate localBundle)
open PqxdhDeploymentServerAuthLocal (State base Phase Pre eager keep keep_run)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The target's material drawn before the run: the native constructor's draws with the protected binding and the native bundle program at slot zero. -/
noncomputable def draw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (binding : Word32 × Std.U64) :
    ProbComp (Pre KemSK) := do
  let created ← localCreate setup binding.1 binding.2
  let bundled ← localBundle setup codec 0 created
  pure ⟨created, bundled.1, bundled.2⟩

/-- The bundle program does not depend on the owner's slot index under the native signing callbacks. -/
theorem localBundle_index (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (first second : Nat)
    (owner : Owner KemSK) : localBundle setup codec first owner = localBundle setup codec second owner := by
  unfold localBundle PqxdhLivePhase1Bundle.bundle
  cases owner.beacon.phase with
  | fresh fresh prekey kem =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhLivePhase1Bundle.afterGenerated]
      refine bind_congr fun generated => ?_
      cases PqxdhBeaconPhase1Publication.prepare owner generated with
      | none => rfl
      | some prepared =>
          simp only [simulateQ_bind, PqxdhDeploymentCompileFootprint.signing_run, pure_bind]
          rfl
  | freshWithCoins fresh prekey oneTime kem =>
      simp only [PqxdhLivePhase1Bundle.afterGenerated]
      cases PqxdhBeaconPhase1Publication.prepare owner none with
      | none => rfl
      | some prepared =>
          simp only [simulateQ_bind, PqxdhDeploymentCompileFootprint.signing_run, pure_bind]
          rfl
  | _ => rfl

/-- After the target's material is used up, an eager step is a base step. -/
theorem eager_done_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) (query : (SourceSpec KemSK).Domain)
    (state : State KemSK) :
    (eager setup codec checks seed c binding pre query).run (state, .done) =
      (fun result => (result.1, (result.2, Phase.done))) <$> (base setup codec checks seed query).run state := by
  rcases query with (coin | request) | request
  · exact keep_run setup codec checks seed _ (state, .done)
  · cases request with
    | create pin keyId =>
        rw [PqxdhDeploymentServerAuthLocal.eager_create, ite_eq_right (by simp)]
        exact keep_run setup codec checks seed _ (state, .done)
    | bundle index =>
        rw [PqxdhDeploymentServerAuthLocal.eager_bundle, ite_eq_right (by simp)]
        exact keep_run setup codec checks seed _ (state, .done)
    | _ => exact keep_run setup codec checks seed _ (state, .done)
  · exact keep_run setup codec checks seed _ (state, .done)

/-- After the target's material is used up, the eager handler runs every program as the base handler. -/
theorem eager_done (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK)
    (program : OracleComp (SourceSpec KemSK) Result) (state : State KemSK) :
    (simulateQ (eager setup codec checks seed c binding pre) program).run (state, .done) =
      (fun result => (result.1, (result.2, Phase.done))) <$> (simulateQ (base setup codec checks seed) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, eager_done_step, bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1 result.2

/-- A base create appends one locally drawn owner and returns the old owner count. -/
theorem base_create_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (pin : Word32) (keyId : Std.U64) (state : State KemSK) (result : Nat × State KemSK)
    (member : result ∈ support ((base setup codec checks seed (.inl (.inr (.create pin keyId)))).run state)) :
    ∃ owner ∈ support (localCreate setup pin keyId),
      result = (state.owners.length, { state with owners := state.owners ++ [owner] }) := by
  rw [PqxdhDeploymentServerAuthLocal.base_create, PqxdhDeploymentServerAuthLocal.create_local, support_map] at member
  obtain ⟨owner, created, rfl⟩ := member
  exact ⟨owner, created, rfl⟩

/-- A base step other than a create keeps the number of owners and every Fresh owner other than a bundled one. -/
theorem base_keeps (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (query : (SourceSpec KemSK).Domain) (notCreate : ∀ pin keyId, query ≠ .inl (.inr (.create pin keyId)))
    (state : State KemSK) (result : (SourceSpec KemSK).Range query × State KemSK)
    (member : result ∈ support ((base setup codec checks seed query).run state)) :
    result.2.owners.length = state.owners.length ∧
      ∀ index owner, (∀ other, query = .inl (.inr (.bundle other)) → other ≠ index) → state.owners[index]? = some owner →
        PqxdhDeploymentEligibility.phaseClass owner.beacon.phase = .fresh → result.2.owners[index]? = some owner := by
  rcases query with (coin | request) | request
  · simp only [base, PqxdhRegistrationJointRevealSchedule.native, PqxdhRegistrationSchedule.handler, StateT.run_lift,
      support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    exact ⟨rfl, fun _ _ _ found _ => found⟩
  · cases request with
    | create pin keyId => exact absurd rfl (notCreate pin keyId)
    | bundle other =>
        rw [PqxdhDeploymentServerAuthLocal.base_bundle] at member
        cases found : state.owners[other]? with
        | none =>
            rw [PqxdhDeploymentServerAuthLocal.bundle_missing setup codec other state found, support_pure,
              Set.mem_singleton_iff] at member
            subst member
            exact ⟨rfl, fun _ _ _ held _ => held⟩
        | some bundled =>
            rw [PqxdhDeploymentServerAuthLocal.bundle_found setup codec other state bundled found, support_map] at member
            obtain ⟨inner, _, rfl⟩ := member
            refine ⟨by simp, fun index owner different held _ => ?_⟩
            rw [List.getElem?_set_ne (different other rfl)]
            exact held
    | finish other raw =>
        rw [PqxdhDeploymentServerAuthLocal.base_finish] at member
        cases found : state.owners[other]? with
        | none =>
            rw [PqxdhRegistrationSchedule.finish_missing setup codec other raw state found, support_pure,
              Set.mem_singleton_iff] at member
            subst member
            exact ⟨rfl, fun _ _ _ held _ => held⟩
        | some finished =>
            rw [PqxdhDeploymentServerAuthLocal.finish_found setup codec other raw state finished found, support_map] at member
            obtain ⟨inner, innerMember, rfl⟩ := member
            refine ⟨by simp, fun index owner _ held fresh => ?_⟩
            by_cases same : other = index
            · subst same
              rw [found, Option.some.injEq] at held
              subst held
              have open_ : PqxdhDeploymentEligibility.phaseClass finished.beacon.phase ≠ .initSent := by
                rw [fresh]
                decide
              rw [PqxdhDeploymentServerAuthLocal.nativeOwner_open codec.frameRead raw finished open_, simulateQ_pure,
                StateT.run_pure, support_pure, Set.mem_singleton_iff] at innerMember
              subst innerMember
              simp only [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1]
            · simp only [List.getElem?_set_ne same]
              exact held
    | accept raw =>
        have keep := PqxdhDeploymentServerAuthLocalize.onShared_owners _ state result member
        exact ⟨by rw [keep], fun _ _ _ held _ => by rw [keep]; exact held⟩
    | build session payload =>
        have keep := PqxdhDeploymentServerAuthLocalize.onShared_owners _ state result member
        exact ⟨by rw [keep], fun _ _ _ held _ => by rw [keep]; exact held⟩
    | hmac key message =>
        have keep := PqxdhDeploymentServerAuthLocalize.onShared_owners _ state result member
        exact ⟨by rw [keep], fun _ _ _ held _ => by rw [keep]; exact held⟩
    | hash bytes =>
        have keep := PqxdhDeploymentServerAuthLocalize.onShared_owners _ state result member
        exact ⟨by rw [keep], fun _ _ _ held _ => by rw [keep]; exact held⟩
    | reveal keyId =>
        have keep := PqxdhDeploymentServerAuthLocalize.onShared_owners _ state result member
        exact ⟨by rw [keep], fun _ _ _ held _ => by rw [keep]; exact held⟩
  · simp only [base, PqxdhRegistrationJointRevealSchedule.native, StateT.run, support_pure,
      Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, fun _ _ _ held _ => held⟩

/-- While the target is created and not bundled, every step other than its bundle is a base step. -/
theorem eager_created_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) (query : (SourceSpec KemSK).Domain)
    (other : query ≠ .inl (.inr (.bundle c))) (state : State KemSK) :
    (eager setup codec checks seed c binding pre query).run (state, .created) =
      (fun result => (result.1, (result.2, Phase.created))) <$> (base setup codec checks seed query).run state := by
  rcases query with (coin | request) | request
  · exact keep_run setup codec checks seed _ (state, .created)
  · cases request with
    | create pin keyId =>
        rw [PqxdhDeploymentServerAuthLocal.eager_create, ite_eq_right (by simp)]
        exact keep_run setup codec checks seed _ (state, .created)
    | bundle index =>
        have different : index ≠ c := fun same => other (by rw [same])
        rw [PqxdhDeploymentServerAuthLocal.eager_bundle, ite_eq_right (by simp [different])]
        exact keep_run setup codec checks seed _ (state, .created)
    | _ => exact keep_run setup codec checks seed _ (state, .created)
  · exact keep_run setup codec checks seed _ (state, .created)

/-- A local constructor's owner is Fresh. -/
theorem localCreate_fresh (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64) (owner : Owner KemSK)
    (member : owner ∈ support (localCreate setup pin keyId)) :
    PqxdhDeploymentEligibility.phaseClass owner.beacon.phase = .fresh := by
  simp only [localCreate, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
  obtain ⟨_, _, _, _, _, _, rfl⟩ := member
  rfl

set_option linter.deprecated false in
/-- While the target is created and not bundled, its first bundle can be drawn before the rest of the run. -/
theorem swap_created (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (program : OracleComp (SourceSpec KemSK) Result)
    (state : State KemSK) (owner : Owner KemSK) (found : state.owners[c]? = some owner)
    (fresh : PqxdhDeploymentEligibility.phaseClass owner.beacon.phase = .fresh) (created : Owner KemSK) :
    𝒮[(simulateQ (base setup codec checks seed) program).run state] =
      𝒮[do
        let bundled ← localBundle setup codec 0 owner
        (fun result : Result × (State KemSK × Phase) => (result.1, result.2.1)) <$>
          (simulateQ (eager setup codec checks seed c binding ⟨created, bundled.1, bundled.2⟩) program).run
            (state, .created)] := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _).symm
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      by_cases bundleC : query = .inl (.inr (.bundle c))
      · subst bundleC
        rw [PqxdhDeploymentServerAuthLocal.base_bundle, PqxdhDeploymentServerAuthLocal.bundle_found setup codec c state owner
          found, bind_map_left, localBundle_index setup codec c 0 owner]
        refine DeferredSampling.evalSPMF_bind_congr_left _ _ _ fun bundled => ?_
        rw [PqxdhDeploymentServerAuthLocal.eager_bundle, ite_eq_left ⟨rfl, rfl⟩, pure_bind, eager_done, Functor.map_map]
        simp
      · simp only [eager_created_step setup codec checks seed c binding _ query bundleC, bind_map_left, map_bind]
        rw [DeferredSampling.evalSPMF_bind_comm]
        refine evalSPMF_bind_congr fun result member => ?_
        have kept : result.2.owners[c]? = some owner := by
          by_cases create : ∃ pin keyId, query = .inl (.inr (.create pin keyId))
          · obtain ⟨pin, keyId, rfl⟩ := create
            obtain ⟨added, _, rfl⟩ := base_create_support setup codec checks seed pin keyId state result member
            exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found
          · push Not at create
            exact (base_keeps setup codec checks seed query create state result member).2 c owner
              (fun other same different => bundleC (by rw [same, different])) found fresh
        exact ih result.1 result.2 kept

/-- Before the target's creation, every step other than the `c`-th create is a base step. -/
theorem eager_waiting_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (pre : Pre KemSK) (query : (SourceSpec KemSK).Domain)
    (state : State KemSK)
    (other : ∀ pin keyId, query = .inl (.inr (.create pin keyId)) → state.owners.length ≠ c) :
    (eager setup codec checks seed c binding pre query).run (state, .waiting) =
      (fun result => (result.1, (result.2, Phase.waiting))) <$> (base setup codec checks seed query).run state := by
  rcases query with (coin | request) | request
  · exact keep_run setup codec checks seed _ (state, .waiting)
  · cases request with
    | create pin keyId =>
        rw [PqxdhDeploymentServerAuthLocal.eager_create, ite_eq_right (by simp [other pin keyId rfl])]
        exact keep_run setup codec checks seed _ (state, .waiting)
    | bundle index =>
        rw [PqxdhDeploymentServerAuthLocal.eager_bundle, ite_eq_right (by simp)]
        exact keep_run setup codec checks seed _ (state, .waiting)
    | _ => exact keep_run setup codec checks seed _ (state, .waiting)
  · exact keep_run setup codec checks seed _ (state, .waiting)

set_option linter.deprecated false in
/-- Drawing the target's material before the run: from every state with at most `c` owners, the native handler and the eager handler on the early draw give the same output distribution, for every program. -/
theorem swap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (binding : Word32 × Std.U64) (program : OracleComp (SourceSpec KemSK) Result)
    (state : State KemSK) (short : state.owners.length ≤ c) :
    𝒮[(simulateQ (base setup codec checks seed) program).run state] =
      𝒮[do
        let pre ← draw setup codec binding
        (fun result : Result × (State KemSK × Phase) => (result.1, result.2.1)) <$>
          (simulateQ (eager setup codec checks seed c binding pre) program).run (state, .waiting)] := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _).symm
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      by_cases target : ∃ pin keyId, query = .inl (.inr (.create pin keyId)) ∧ state.owners.length = c
      · obtain ⟨pin, keyId, rfl, atC⟩ := target
        subst atC
        by_cases chosen : (pin, keyId) = binding
        · simp only [PqxdhDeploymentServerAuthLocal.eager_create, ite_eq_left chosen]
          rw [PqxdhDeploymentServerAuthLocal.base_create, PqxdhDeploymentServerAuthLocal.create_local, bind_map_left]
          subst chosen
          simp only [draw, bind_assoc, pure_bind]
          refine evalSPMF_bind_congr fun owner member => ?_
          have found : ({ state with owners := state.owners ++ [owner] } : State KemSK).owners[state.owners.length]? =
              some owner := by simp
          exact swap_created setup codec checks seed state.owners.length (pin, keyId) (next state.owners.length) _ owner
            found (localCreate_fresh setup pin keyId owner member) owner
        · simp only [PqxdhDeploymentServerAuthLocal.eager_create, ite_eq_right chosen, and_self, ite_true,
            bind_map_left, eager_done]
          simp only [map_bind, Functor.map_map, Prod.mk.eta, id_map']
          exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _).symm
      · push Not at target
        simp only [eager_waiting_step setup codec checks seed c binding _ query state target, bind_map_left, map_bind]
        rw [DeferredSampling.evalSPMF_bind_comm]
        refine evalSPMF_bind_congr fun result member => ?_
        have shorter : result.2.owners.length ≤ c := by
          by_cases create : ∃ pin keyId, query = .inl (.inr (.create pin keyId))
          · obtain ⟨pin, keyId, rfl⟩ := create
            obtain ⟨added, _, rfl⟩ := base_create_support setup codec checks seed pin keyId state result member
            have different := target pin keyId rfl
            simp only [List.length_append, List.length_singleton]
            omega
          · push Not at create
            rw [(base_keeps setup codec checks seed query create state result member).1]
            exact short
        exact ih result.1 result.2 shorter

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.localBundle_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.localBundle_index

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.eager_done_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.eager_done_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.eager_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.eager_done

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.base_create_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.base_create_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.base_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.base_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.eager_created_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.eager_created_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.localCreate_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.localCreate_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.swap_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.swap_created

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.eager_waiting_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.eager_waiting_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager.swap
