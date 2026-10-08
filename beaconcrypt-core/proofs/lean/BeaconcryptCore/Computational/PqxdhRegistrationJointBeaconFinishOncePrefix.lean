import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOncePost

/-!
# The KEM creation index at the cut (item 2, stage T, prefix)

The post-challenge module bounds the hidden reads after the cut by the potential at the cut: the number of owners whose phase holds the selected KEM creation index, plus one while the KEM router has not yet handed that index out (`KemOnce`). This module shows that every prechallenge context of the opaque KEM-ideal branch satisfies `KemOnce` (`sourcePreOpaque_once`, `sharedStart_once`).

The prefix runs the source program from an empty owner list and a fresh router (counter 0), so the potential starts at one. The source client, the source backend and the stopped KEM router are collapsed into one optional stateful interpreter (`preTop`, by `composeOpt`), and no source request increases the potential (`pre_step`): a raw `create` appends an owner exactly with the index the router hands out and increments the counter (`client_created`), no other request increases the owner count (`client_count`), and no step decreases the counter (`combine_mono`). The rest of the scan up to the selected raw accept (its attached verification and the steps before encapsulation) does not touch the owners and only increases the counter.

These are structural facts about the executable prefix; they charge nothing.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRawOpaque (OpaqueCut OpaqueContext opaqueScan sourcePreOpaque rejectRun)

/-! ### The collapsed prefix interpreter -/

section Stack

variable {ι ι' : Type} {baseSpec : OracleSpec ι} {spec' : OracleSpec.{0, 0} ι'} {KemSK Reader Response : Type}

/-- The source backend collapsed onto a KEM router. -/
noncomputable def preLow (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) :=
  composeOpt (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity) router

/-- The source client collapsed onto the source backend and a KEM router. -/
noncomputable def preTop (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) :=
  composeOpt (PqxdhRegistrationJointRevealSchedule.client setup codec)
    (preLow setup codec checks identityIndex publicIdentity router)

/-- The potential of the prefix: the owners holding the selected KEM index, plus one while the router has not yet handed it out. -/
def prePotential (selected : Nat) (state : List EncodedEntry × (NativeState KemSK × PqxdhDynamicKemJointSource.State KemSK)) :
    Nat :=
  ownerCount selected state.1 + pending selected (created state.2.2)

/-- A private-pool request of the source backend reaches the router unchanged, with the native state kept. -/
theorem preLow_pool (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec'))))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (native : NativeState KemSK)
    (lower : PqxdhDynamicKemJointSource.State KemSK) :
    (((preLow setup codec checks identityIndex publicIdentity router (.inl (.inl query))).run).run (native, lower)) =
      (fun result => (result.1, (native, result.2))) <$> (((router query).run).run lower).liftComp spec' := by
  have backendStep : (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity
      (.inl (.inl query))).run native =
      (fun reply => (reply, native)) <$> (liftM ((PqxdhLiveKemBirth.Spec KemSK).query query) :
        OracleComp (PqxdhLiveKemBirth.Spec KemSK) _) := rfl
  rw [preLow, composeOpt_step, backendStep]
  simp only [simulateQ_map, simulateQ_spec_query, OptionT.run_map, StateT.run_map, Functor.map_map, liftComp_self]
  congr 1
  funext result
  rcases result with ⟨_ | reply, after⟩ <;> rfl

variable {coins : {X : Type} → ProbComp X → OracleComp spec' X} {primitives : PqxdhJointIdentity.Primitives}
  {pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
    (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp spec')))}

theorem preLow_mono (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (counts : CountsCreates pool) :
    StepMono (preLow setup codec checks identityIndex publicIdentity
      (PqxdhDynamicKemJointRouter.combine coins primitives pool)) (fun state => created state.2) :=
  stepMono_composeOpt _ _ created (combine_mono coins primitives pool counts)

/-- A raw `create` of the source client keeps the prefix potential. -/
theorem pre_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (counts : CountsCreates pool)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) (owners : List EncodedEntry)
    (native : NativeState KemSK) (lower : PqxdhDynamicKemJointSource.State KemSK) :
    ∀ result ∈ support (((simulateQ (preLow setup codec checks identityIndex publicIdentity
        (PqxdhDynamicKemJointRouter.combine coins primitives pool))
        ((PqxdhRegistrationJointRevealSchedule.client setup codec (.inl (.inr (.create pin keyId)))).run owners)).run).run
          (native, lower)), ∀ value, result.1 = some value →
      ownerCount selected value.2 + pending selected (created result.2.2) ≤
        ownerCount selected owners + pending selected (created lower) := by
  intro result member value found
  rw [create_run, simulateQ_map, OptionT.run_map, StateT.run_map, ← QueryImpl.simulateQ_compose,
    option_lift_state (PqxdhDynamicKemJointRouter.combine coins primitives pool) _ (fun query extra below => by
      rw [QueryImpl.apply_compose]
      simp only [PqxdhRegistrationJointServiceSchedule.poolLift, simulateQ_spec_query]
      exact preLow_pool setup codec checks identityIndex publicIdentity _ query extra below),
    Functor.map_map, support_map] at member
  obtain ⟨inner, reached, rfl⟩ := member
  have routed := mem_support_of_mem_support_liftComp _ _ inner reached
  have grows := option_monotone _ created (combine_mono coins primitives pool counts) _ lower inner routed
  rcases inner with ⟨_ | born, after⟩
  · cases found
  · simp only [Option.map_some, Option.some.injEq] at found
    subst found
    cases born with
    | none => simpa using pending_anti selected grows
    | some birth =>
        obtain ⟨index, step⟩ := client_created coins primitives pool counts lower _ routed birth rfl
        dsimp only
        rw [ownerCount_birth, step]
        simp only [index]
        have := pending_step selected (created lower)
        omega

/-- No source request increases the prefix potential, including a request the router stops. -/
theorem pre_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (counts : CountsCreates pool)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : List EncodedEntry × (NativeState KemSK × PqxdhDynamicKemJointSource.State KemSK)) :
    ∀ result ∈ support (((preTop setup codec checks identityIndex publicIdentity
        (PqxdhDynamicKemJointRouter.combine coins primitives pool) query).run).run state),
      prePotential selected result.2 ≤ prePotential selected state := by
  intro result member
  rw [preTop, composeOpt_step, support_map] at member
  obtain ⟨inner, reached, rfl⟩ := member
  have grows := option_monotone _ _ (preLow_mono setup codec checks identityIndex publicIdentity counts) _ state.2 _
    reached
  have pend := pending_anti selected grows
  rcases inner with ⟨_ | ⟨answer, owners⟩, after⟩
  · simp only [prePotential, Option.map_none, Option.getD_none]
    dsimp only at pend
    omega
  · simp only [prePotential, Option.map_some, Option.getD_some]
    by_cases create : CreateKind query
    · obtain ⟨pin, keyId, rfl⟩ : ∃ pin keyId, query = .inl (.inr (.create pin keyId)) := by
        rcases query with (coin | request) | read
        · simp [CreateKind] at create
        · cases request with
          | create pin keyId => exact ⟨pin, keyId, rfl⟩
          | _ => simp [CreateKind] at create
        · simp [CreateKind] at create
      exact pre_create setup codec checks identityIndex publicIdentity selected counts pin keyId state.1 state.2.1
        state.2.2 _ reached (answer, owners) rfl
    · have source := option_support _ _ _ _ reached (answer, owners) rfl
      have counted := client_count setup codec selected query create state.1 _ source
      dsimp only at counted pend
      omega

/-- No source program increases the prefix potential. -/
theorem pre_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (counts : CountsCreates pool) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) α)
    (state : List EncodedEntry × (NativeState KemSK × PqxdhDynamicKemJointSource.State KemSK)) :
    ∀ result ∈ support (((simulateQ (preTop setup codec checks identityIndex publicIdentity
        (PqxdhDynamicKemJointRouter.combine coins primitives pool)) work).run).run state),
      prePotential selected result.2 ≤ prePotential selected state :=
  option_invariant _ (fun current => prePotential selected current ≤ prePotential selected state)
    (fun query current holds result member =>
      (pre_step setup codec checks identityIndex publicIdentity selected counts query current result member).trans holds)
    work state le_rfl

/-- The source commands interpreted by the actual encapsulator and a KEM router do not increase the prefix potential. -/
theorem commands_once (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (counts : CountsCreates pool) {α : Type}
    (work : OracleComp (SourceSpec KemSK) α) (owners : List EncodedEntry) (native : NativeState KemSK)
    (lower : PqxdhDynamicKemJointSource.State KemSK) :
    ∀ result ∈ support (((simulateQ (PqxdhDynamicKemJointRouter.combine coins primitives pool)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks identityIndex publicIdentity work owners
            native))).run).run lower), ∀ reached, result.1 = some reached →
      ownerCount selected reached.1.2 + pending selected (created result.2) ≤
        ownerCount selected owners + pending selected (created lower) := by
  intro result member reached found
  rw [PqxdhRegistrationJointKemEncapsulation.commands, PqxdhRegistrationJointKemEncapsulation.program_actual,
    composeOpt_run, composeOpt_run, Functor.map_map, support_map] at member
  obtain ⟨inner, member, rfl⟩ := member
  have bound := pre_run (coins := coins) (primitives := primitives) setup codec checks identityIndex publicIdentity
    selected counts work (owners, (native, lower)) inner member
  rcases inner with ⟨_ | answer, after⟩
  · cases found
  · simp only [Option.map_some, Option.some.injEq] at found
    subst found
    simpa [prePotential] using bound

end Stack

/-! ### Every prechallenge context satisfies `KemOnce` -/

section Context

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- An active cut reached by the explicit opaque scan under the stopped router keeps the prefix potential of its start. -/
theorem opaqueScan_once (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × PqxdhRegistrationJointAcceptCutTag.Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat) (owners : List EncodedEntry) (native : NativeState KemSK)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (lower : PqxdhDynamicKemJointSource.State KemSK) :
    ∀ result ∈ support (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected
        pairs) (opaqueScan (Reader := Reader) setup codec checks identityIndex publicIdentity observe work index owners
          native)).run).run lower),
      ∀ raw value ephemeral consumed native' owners' next,
        result.1 = some (.pending raw value ephemeral consumed native' owners' next) →
        ownerCount selected owners' + pending selected (created result.2) ≤
          ownerCount selected owners + pending selected (created lower) := by
  have counts : CountsCreates (PqxdhDynamicKemRouter.source setup.baseImpl setup.kem selected pairs) :=
    source_counts _ _ _ _
  have mono : StepMono (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs) created :=
    combine_mono (fun work => work) setup.joint _ counts
  intro result member raw value ephemeral consumed native' owners' next found
  rw [opaqueScan, option_simulate_bind, mem_support_bind_iff] at member
  obtain ⟨first, firstReached, member⟩ := member
  rcases first with ⟨_ | reached, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member] at found
    cases found
  · have bound := commands_once (coins := fun work => work) (primitives := setup.joint) setup codec checks identityIndex
      publicIdentity selected counts _ owners native lower _ firstReached reached rfl
    dsimp only at member
    split at member
    · simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      rw [member] at found
      cases found
    · rename_i rawCut nextCut cutEq
      split at member
      · obtain ⟨_, contradiction⟩ := PqxdhRegistrationJointKemRawOpaque.rejectRun_complete setup codec checks
          identityIndex publicIdentity observe _ _ _ _ _ _
          (option_support _ _ _ _ member _ found)
        cases contradiction
      · rw [option_simulate_bind, mem_support_bind_iff] at member
        obtain ⟨second, secondReached, member⟩ := member
        have grows := option_monotone _ created mono _ after second secondReached
        rcases second with ⟨_ | prepared, afterPrepared⟩
        · simp only [support_pure, Set.mem_singleton_iff] at member
          rw [member] at found
          cases found
        · dsimp only at member grows
          split at member
          · obtain ⟨_, contradiction⟩ := PqxdhRegistrationJointKemRawOpaque.rejectRun_complete setup codec checks
              identityIndex publicIdentity observe _ _ _ _ _ _
              (option_support _ _ _ _ member _ found)
            cases contradiction
          · simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
            rw [member] at found
            simp only [Option.some.injEq, OpaqueCut.pending.injEq] at found
            obtain ⟨-, -, -, -, -, rfl, -⟩ := found
            rw [member]
            have := pending_anti selected grows
            dsimp only at this bound ⊢
            omega

/-- Every prechallenge context of the opaque KEM-ideal branch satisfies `KemOnce`: at the selected raw accept, at most one owner holds the selected KEM index, and none does while the router has not yet handed it out. -/
theorem sourcePreOpaque_once (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    ∀ context ∈ support (sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index chosen), KemOnce selected.val context := by
  intro context reached
  rw [sourcePreOpaque, mem_support_bind_iff] at reached
  obtain ⟨born, _, reached⟩ := reached
  rcases bornCase : born.1 with _ | server
  · rw [bornCase] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    rw [reached]
    trivial
  · rw [bornCase] at reached
    dsimp only at reached
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨others, _, result, resultReached, rfl⟩ := reached
    rcases cutCase : result.1 with _ | cut
    · simp only [KemOnce]
    · rcases cut with outcome | ⟨raw, value, ephemeral, consumed, native, owners, next⟩
      · simp only [KemOnce]
      · simp only [KemOnce]
        have := opaqueScan_once setup codec checks _ _ _ work index [] _ selected.val _ _ result resultReached raw value
          ephemeral consumed native owners next cutCase
        have start : pending selected.val (created (born.2.1.1, PqxdhDynamicKemRouter.empty (KemSK := KemSK))) = 1 := by
          have zero : (PqxdhDynamicKemRouter.empty (KemSK := KemSK)).created = 0 := rfl
          simp [pending, created, zero]
        have empty : ownerCount selected.val [] = 0 := rfl
        rw [start, empty] at this
        exact this

/-- Every outcome of G1's prefix for the KEM-ideal branch has a prechallenge context satisfying `KemOnce`. -/
theorem sharedStart_once (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    ∀ start ∈ support (PqxdhRegistrationJointKemPostSkeleton.sharedStart (Reader := Reader) setup codec checks ensureInit
      supplied decision work runtime count selected index), KemOnce selected.val start.2.2.1 := by
  intro start reached
  simp only [PqxdhRegistrationJointKemPostSkeleton.sharedStart, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at reached
  obtain ⟨chosen, _, context, contextReached, encapsulated, _, rfl⟩ := reached
  exact sourcePreOpaque_once setup codec checks ensureInit supplied decision work runtime count selected index chosen
    context contextReached

end Context

end BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.preLow_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.preLow_pool

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.preLow_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.preLow_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pre_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pre_create

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pre_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pre_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pre_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pre_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.commands_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.commands_once

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.opaqueScan_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.opaqueScan_once

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.sourcePreOpaque_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.sourcePreOpaque_once

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.sharedStart_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.sharedStart_once
