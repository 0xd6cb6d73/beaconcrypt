-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor

/-! LQ-F upstream, unit A2: stage T of item 2 over the logged source and every two-read form (LQ-F upstream design-v2, section 4.4, module `…ItemOnce`). The logged root client `rootClientL` makes at most two root requests and the logged factored root client `entryClientL` at most two value requests, with no premise (`rootClientL_two`, `entryClientL_two`): one at the Server's private resumption root and at most one at a grouped Beacon finish on the challenge marker. With stage S1c over the logged source, the logged opaque KEM-ideal branch and the uniform-root world are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256` plus the sum of two one-query HMAC-SHA-512 PRF advantages (`opaqueBranchL_uniform_two`).

The argument is the classical stage T (`PqxdhRegistrationJointBeaconFinishOnce`, Rust `finish_registration` in `beaconcrypt/src/beacon.rs` acting only in `InitSent` and leaving it on every outcome, and every Beacon generating its own ML-KEM key pair), on the logged layers:

- The potential is the number of owners holding the selected KEM creation index plus one while the KEM router has not yet handed it out; it does not read the log. The logged grouped client, the logged skeleton, the actual encapsulator and the router are collapsed into one optional stateful interpreter (`topImplL`), and every logged-source request makes at most as many hidden reads as the potential drops (`top_stepL`). A source14 request other than the raw accept is the classical request with the log kept (`groupedClientL_inl`), so the classical facts apply (`groupedClient_marked`, `groupedClient_count`, `create_step`); the logged accept reaches the native layer as one logged accept request, which makes no hidden read (`skelImplL_marked`, transported along `acceptStepL_fst`) and keeps the owners; the Server read is one identity-pool reveal of the Server's slot, which keeps the owners and is not a grouped finish. No step decreases the router's counter (`midL_mono`).
- In the prefix, the logged source client, its native backend under the actual encapsulator and the stopped KEM router are collapsed the same way (`preTopL`); no logged-source request increases the potential (`pre_stepL`), so every active logged cut satisfies `KemOnceL` (`commandsL_once`, `opaqueScanL_once`, `sourcePreOpaqueL_once`, `sharedStartL_once`).
- `postSkelL_two` adds the resumption's one read to the potential at the cut, at most one.

These are structural facts about the logged programs; they charge nothing and add no assumption. The two-read bound holds for every logged-source program, the compiled LQ-F program with its terminal reads, Server read and post phase included. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemPostSkeleton (GSpec Services SkelState groupedClient groupedPoolLift)
open PqxdhRegistrationJointKemRootExpand (valueRead? HiddenC resumeImpl_hidden fwd_hidden)
open PqxdhRegistrationJointKemRomSplit (isQueryBoundP_option_of_step resume_root query_free query_one)
open PqxdhRegistrationJointBeaconFinishOnce (PotBound potBound_map potBound_of_bound isQueryBoundP_of_potBound optPot
  option_potential option_invariant option_monotone option_support option_simulate_bind simulate_support composeOpt
  composeOpt_step composeOpt_run StepMono stepMono_composeOpt combine_mono CountsCreates created pending pending_anti
  ownerCount CreateKind FinishAt markedGroup skelImpl_marked groupedClient_marked groupedClient_count client_count
  lowImpl low_hidden low_mono low_eq midImpl create_step preLow pre_create router_counts source_counts)
open PqxdhDeploymentLaterServerSource (Log)
open PqxdhDeploymentLaterServerCommands (Local)
open PqxdhDeploymentLaterServerItemTargets (AcceptL GSpecL skelImplL groupedClientL skelResumeL postSkelL sharedStartL
  rootClientL entryClientL)
open PqxdhDeploymentLaterServerItemFree (SpecL clientL logClient implL run_clientL)

/-! ### Requests of the logged source -/

section Kinds

variable {KemSK Response : Type}

/-- The logged grouped requests whose prepared root carries the challenge marker: those of the grouped interface; the logged accept is not one. -/
def markedGroupL : (GSpecL KemSK Response).Domain → Bool
  | .inl query => markedGroup (KemSK := KemSK) (Response := Response) query
  | .inr _ => false

/-- The logged source's raw `create` request. -/
def CreateKindL : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop
  | .inl query => CreateKind (KemSK := KemSK) query
  | .inr _ => False

/-- The hidden-read bound of one logged-source request: that of the classical request (one for a grouped finish of an owner that awaits its finish with the selected KEM index), and none for the Server read. -/
def finishBoundL (selected : Nat) : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → List EncodedEntry → Nat
  | .inl query, owners => PqxdhRegistrationJointBeaconFinishOnce.finishBound (KemSK := KemSK) selected query owners
  | .inr _, _ => 0

/-- The hidden-read bound of a logged-source request is at most `ownerCount`, the number of owners holding the selected KEM index: by `PqxdhRegistrationJointBeaconFinishOnce.finishBound_le` on a source14 request; the Server read's bound is 0. -/
theorem finishBoundL_le (selected : Nat) (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain)
    (owners : List EncodedEntry) : finishBoundL selected query owners ≤ ownerCount selected owners := by
  rcases query with query | read
  · exact PqxdhRegistrationJointBeaconFinishOnce.finishBound_le (KemSK := KemSK) selected query owners
  · exact Nat.zero_le (ownerCount selected owners)

end Kinds

/-! ### Source14 requests of the logged clients -/

section Steps

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The logged form of a source client on a source14 request other than the raw accept runs that client with the log kept. -/
theorem logClient_run {ι' : Type} {spec' : OracleSpec ι'}
    (client : QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK)
      (StateT (List EncodedEntry) (OracleComp spec')))
    (pool : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp spec')) (identityIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : ∀ raw, query ≠ .inl (.inr (.accept raw))) (held : Local) :
    (logClient client pool identityIndex (.inl query)).run held =
      (fun result => (result.1, (result.2, held.2))) <$>
        simulateQ (fun q => ((spec' + AcceptL).query (.inl q) : OracleComp (spec' + AcceptL) _))
          ((client query).run held.1) := by
  rcases query with (coin | request) | read
  · rfl
  · cases request
    case accept raw => exact absurd rfl (other raw)
    all_goals rfl
  · rfl

/-- The logged source client on a source14 request other than the raw accept is the source client with the log kept. -/
theorem clientL_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : ∀ raw, query ≠ .inl (.inr (.accept raw))) (held : Local) :
    (clientL (Response := Response) setup codec identityIndex (.inl query)).run held =
      (fun result => (result.1, (result.2, held.2))) <$>
        simulateQ (fun q => ((SpecL KemSK Response).query (.inl q) : OracleComp (SpecL KemSK Response) _))
          ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run held.1) :=
  logClient_run _ _ identityIndex query other held

/-- The logged grouped client on a source14 request other than the raw accept is the grouped client with the log kept. -/
theorem groupedClientL_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (identityIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : ∀ raw, query ≠ .inl (.inr (.accept raw))) (held : Local) :
    (groupedClientL (Response := Response) setup codec selected challenge identityIndex (.inl query)).run held =
      (fun result => (result.1, (result.2, held.2))) <$>
        simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
          ((groupedClient setup codec selected challenge query).run held.1) :=
  PqxdhDeploymentLaterServerItemTargets.groupedClientL_inl setup codec selected challenge identityIndex query other held

end Steps

/-! ### The logged postchallenge stack -/

section Stack

variable {ι ι' : Type} {baseSpec : OracleSpec ι} {spec' : OracleSpec.{0, 0} ι'} {KemSK Reader Response V : Type}

/-- Every step of the logged skeleton makes at most one hidden read, and only on a grouped finish with the challenge marker; the logged accept makes none (its classical projection `acceptStep` makes none, `acceptStepL_fst`). -/
theorem skelImplL_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (query : (GSpecL KemSK Response).Domain) :
    HiddenC (skelImplL setup codec checks identityIndex publicIdentity services query)
      (if markedGroupL query = true then 1 else 0) := by
  rcases query with query | raw
  · exact skelImpl_marked setup codec checks identityIndex publicIdentity services query
  · intro state
    have free := skelImpl_marked setup codec checks identityIndex publicIdentity services (.inl (.inr (.accept raw)))
      state
    simp only [markedGroup, markedGroupL, Bool.false_eq_true, ite_false] at free ⊢
    change ((PqxdhRegistrationJointKemPostSkeleton.acceptStep (V := V) setup codec checks identityIndex publicIdentity
      raw).run state).IsQueryBoundP _ 0 at free
    rw [← PqxdhDeploymentLaterServerItemTargets.acceptStepL_fst, isQueryBoundP_map_iff] at free
    exact free

/-- The logged skeleton collapsed onto the interpreters below it. -/
noncomputable def midImplL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) :=
  composeOpt (skelImplL setup codec checks identityIndex publicIdentity services) (lowImpl (V := V) setup router)

/-- The logged grouped client collapsed onto the logged skeleton and the interpreters below it. -/
noncomputable def topImplL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) (selected : Nat)
    (challenge : MlKem768Ciphertext)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) :=
  composeOpt (groupedClientL setup codec selected challenge identityIndex)
    (midImplL setup codec checks identityIndex publicIdentity services router)

/-- The potential of the logged postchallenge phase: the owners holding the selected KEM index, plus one while the router has not yet handed it out. The log is not read. -/
def potentialL (selected : Nat) {S : Type} (state : Local × (S × PqxdhDynamicKemJointSource.State KemSK)) : Nat :=
  ownerCount selected state.1.1 + pending selected (created state.2.2)

/-- On a classical request, the collapsed logged skeleton is the collapsed classical skeleton. -/
theorem midImplL_inl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) {α : Type}
    (work : OracleComp (GSpec KemSK Response) α) :
    simulateQ (midImplL setup codec checks identityIndex publicIdentity services router)
        (simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _)) work) =
      simulateQ (midImpl setup codec checks identityIndex publicIdentity services router) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, simulateQ_spec_query]
  rfl

/-- Every step of the collapsed logged skeleton makes at most one hidden read, and only on a grouped finish with the challenge marker. -/
theorem midL_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec'))))
    (query : (GSpecL KemSK Response).Domain) (state : SkelState KemSK V × PqxdhDynamicKemJointSource.State KemSK) :
    (((midImplL setup codec checks identityIndex publicIdentity services router query).run).run state).IsQueryBoundP
      (fun query => valueRead? query = true) (if markedGroupL query = true then 1 else 0) := by
  rw [midImplL, composeOpt_step, isQueryBoundP_map_iff]
  exact low_hidden setup router _ _ (skelImplL_marked setup codec checks identityIndex publicIdentity services query
    state.1) state.2

/-- Every logged-source request of the logged grouped client sends at most `finishBoundL` requests with the challenge marker: the classical bound on a source14 request, none for the logged accept and the Server read. -/
theorem groupedClientL_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (identityIndex : Nat)
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (held : Local) :
    ((groupedClientL (Response := Response) setup codec selected challenge identityIndex query).run held).IsQueryBoundP
      (fun query => markedGroupL (KemSK := KemSK) (Response := Response) query = true)
      (finishBoundL selected query held.1) := by
  have lifted : ∀ {β : Type} (work : OracleComp (GSpec KemSK Response) β) (k : ℕ),
      work.IsQueryBoundP (fun query => markedGroup (KemSK := KemSK) (Response := Response) query = true) k →
      IsQueryBoundP
        (simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _)) work)
        (fun query => markedGroupL (KemSK := KemSK) (Response := Response) query = true) k := by
    intro _ work k bounded
    refine IsQueryBoundP.simulateQ_of_step bounded (fun query marked => query_one _ _)
      (fun query marked => query_free _ _ ?_)
    simpa [markedGroupL] using marked
  rcases query with query | later
  · by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
    · obtain ⟨raw, rfl⟩ := accept
      change IsQueryBoundP ((fun answer => (answer.1, (held.1, held.2 ++ [answer.2]))) <$>
        ((GSpecL KemSK Response).query (.inr raw) : OracleComp (GSpecL KemSK Response) _)) _ _
      rw [isQueryBoundP_map_iff]
      exact (query_free _ _ (by simp [markedGroupL])).mono (Nat.zero_le _)
    · rw [groupedClientL_run setup codec selected challenge identityIndex query (fun raw same => accept ⟨raw, same⟩)
        held, isQueryBoundP_map_iff]
      exact lifted _ _ (groupedClient_marked setup codec selected challenge query held.1)
  · change IsQueryBoundP ((fun seed => ((seed, held.2), held)) <$>
      simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
        (groupedPoolLift (Response := Response) (.inl (.inr (.reveal identityIndex))))) _ _
    rw [isQueryBoundP_map_iff]
    exact (lifted _ _ (query_free _ _ (by simp [markedGroup]))).mono (Nat.zero_le _)

/-- No logged-source request other than `create` increases the count of owners holding the selected KEM index, and a grouped finish of an owner that awaits its finish with the selected index decreases it by one; the logged accept and the Server read keep the owners. -/
theorem groupedClientL_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (marker identityIndex : Nat)
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (notCreate : ¬ CreateKindL query) (held : Local) :
    ∀ result ∈ support ((groupedClientL (Response := Response) setup codec marker challenge identityIndex query).run
        held),
      ownerCount selected result.2.1 + finishBoundL selected query held.1 ≤ ownerCount selected held.1 := by
  rcases query with query | later
  · by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
    · obtain ⟨raw, rfl⟩ := accept
      intro result member
      change result ∈ support ((fun answer => (answer.1, (held.1, held.2 ++ [answer.2]))) <$>
        ((GSpecL KemSK Response).query (.inr raw) : OracleComp (GSpecL KemSK Response) _)) at member
      rw [support_map] at member
      obtain ⟨_, -, rfl⟩ := member
      simp [finishBoundL, PqxdhRegistrationJointBeaconFinishOnce.finishBound, FinishAt]
    · intro result member
      rw [groupedClientL_run setup codec marker challenge identityIndex query (fun raw same => accept ⟨raw, same⟩)
        held, support_map] at member
      obtain ⟨inner, reached, rfl⟩ := member
      exact groupedClient_count setup codec selected challenge marker query notCreate held.1 inner
        (simulate_support _ _ reached)
  · intro result member
    change result ∈ support ((fun seed => ((seed, held.2), held)) <$>
      simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
        (groupedPoolLift (Response := Response) (.inl (.inr (.reveal identityIndex))))) at member
    rw [support_map] at member
    obtain ⟨_, -, rfl⟩ := member
    simp [finishBoundL]

variable {coins : {X : Type} → ProbComp X → OracleComp spec' X} {primitives : PqxdhJointIdentity.Primitives}
  {pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
    (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp spec')))}

/-- No step of the collapsed logged skeleton decreases the KEM creation counter. -/
theorem midL_mono (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (counts : CountsCreates pool) :
    StepMono (midImplL setup codec checks identityIndex publicIdentity services
      (PqxdhDynamicKemJointRouter.combine coins primitives pool)) (fun state => created state.2) :=
  stepMono_composeOpt _ _ created (low_mono setup counts)

/-- A raw `create` of the logged grouped client keeps the potential: it is the classical `create` with the log kept (`PqxdhRegistrationJointBeaconFinishOnce.create_step`). -/
theorem createL_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (counts : CountsCreates pool) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (keyId : Std.U64) (owners : List EncodedEntry) (log : Log) (skel : SkelState KemSK V)
    (lower : PqxdhDynamicKemJointSource.State KemSK) :
    ∀ result ∈ support (((simulateQ (midImplL setup codec checks identityIndex publicIdentity services
        (PqxdhDynamicKemJointRouter.combine coins primitives pool))
        ((groupedClientL setup codec selected challenge identityIndex (.inl (.inl (.inr (.create pin keyId))))).run
          (owners, log))).run).run (skel, lower)), ∀ value, result.1 = some value →
      ownerCount selected value.2.1 + pending selected (created result.2.2) ≤
        ownerCount selected owners + pending selected (created lower) := by
  intro result member value found
  rw [groupedClientL_run setup codec selected challenge identityIndex _ (fun raw same => by cases same) (owners, log),
    simulateQ_map, midImplL_inl, OptionT.run_map, StateT.run_map, support_map] at member
  obtain ⟨inner, reached, rfl⟩ := member
  rcases inner with ⟨_ | inner, after⟩
  · cases found
  · simp only [Option.map_some, Option.some.injEq] at found
    subst found
    exact create_step setup codec checks identityIndex publicIdentity services selected challenge counts pin keyId
      owners skel lower _ reached inner rfl

/-- Every logged-source request of the continuation makes at most as many hidden reads as the potential drops; a stopped request ends with potential 0. -/
theorem top_stepL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (counts : CountsCreates pool)
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain)
    (state : Local × (SkelState KemSK V × PqxdhDynamicKemJointSource.State KemSK)) :
    PotBound (((topImplL setup codec checks identityIndex publicIdentity services selected challenge
        (PqxdhDynamicKemJointRouter.combine coins primitives pool) query).run).run state)
      (fun query => valueRead? query = true) (optPot (potentialL selected)) (potentialL selected state) := by
  obtain ⟨⟨owners, log⟩, skel, lower⟩ := state
  rw [topImplL, composeOpt_step]
  apply potBound_map
  have dle := finishBoundL_le selected query owners
  refine potBound_of_bound (d := finishBoundL selected query owners)
    (isQueryBoundP_option_of_step _ _ _
      (groupedClientL_marked setup codec selected challenge identityIndex query (owners, log))
      (fun query current => midL_marked setup codec checks identityIndex publicIdentity services _ query current)
      (skel, lower))
    (dle.trans (Nat.le_add_right _ _)) ?_
  intro result member
  rcases result with ⟨_ | ⟨answer, held⟩, after⟩
  · simp only [Function.comp, optPot, Option.map_none, zero_add, potentialL]
    exact dle.trans (Nat.le_add_right _ _)
  · simp only [Function.comp, optPot, Option.map_some, Option.getD_some, potentialL]
    by_cases create : CreateKindL query
    · obtain ⟨pin, keyId, rfl⟩ : ∃ pin keyId, query = .inl (.inl (.inr (.create pin keyId))) := by
        rcases query with ((coin | request) | read) | later
        · simp [CreateKindL, CreateKind] at create
        · cases request with
          | create pin keyId => exact ⟨pin, keyId, rfl⟩
          | _ => simp [CreateKindL, CreateKind] at create
        · simp [CreateKindL, CreateKind] at create
        · simp [CreateKindL] at create
      have := createL_step setup codec checks identityIndex publicIdentity services selected challenge counts pin keyId
        owners log skel lower _ member (answer, held) rfl
      simpa [finishBoundL, PqxdhRegistrationJointBeaconFinishOnce.finishBound, FinishAt] using this
    · have reached := option_support _ _ _ _ member (answer, held) rfl
      have counted := groupedClientL_count setup codec selected challenge selected identityIndex query create
        (owners, log) _ reached
      have grows := option_monotone _ _ (midL_mono setup codec checks identityIndex publicIdentity services counts) _
        (skel, lower) _ member
      have pend := pending_anti selected grows
      dsimp only at pend counted ⊢
      omega

/-- The hidden reads of the logged continuation are bounded by the potential at its start. -/
theorem top_potentialL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (counts : CountsCreates pool) {α : Type}
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) α)
    (state : Local × (SkelState KemSK V × PqxdhDynamicKemJointSource.State KemSK)) :
    PotBound (((simulateQ (topImplL setup codec checks identityIndex publicIdentity services selected challenge
        (PqxdhDynamicKemJointRouter.combine coins primitives pool)) work).run).run state)
      (fun query => valueRead? query = true) (optPot (potentialL selected)) (potentialL selected state) :=
  option_potential _ _ (potentialL selected) (fun _ => True)
    (fun query current _ => top_stepL setup codec checks identityIndex publicIdentity services selected challenge
      counts query current)
    (fun _ _ _ _ _ _ _ => trivial) work state trivial

end Stack

/-! ### The logged postchallenge phase -/

section Skeleton

open PqxdhDeploymentLaterServerOpaque (OpaqueContext)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X V : Type}

/-- The logged prechallenge context of an active cut has at most one owner holding the selected KEM index, and none while the router has not yet handed it out: the potential at the cut is at most one. -/
def KemOnceL (selected : Nat) {count : Nat} : OpaqueContext Reader KemSK A X count → Prop
  | .ready _ _ (some (.pending _ _ _ _ _ owners _ _)) state _ =>
      ownerCount selected owners + pending selected state.2.created ≤ 1
  | _ => True

/-- Stage T over the logged source, the hidden reads of the postchallenge phase: for any services, the logged skeleton's postchallenge phase makes at most two hidden reads when the logged prechallenge context satisfies `KemOnceL`: one at the Server's private resumption root and at most one at a grouped Beacon finish on the challenge marker. -/
theorem postSkelL_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (services : Services V Response)
    (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (context : OpaqueContext Reader KemSK A X count) (once : KemOnceL selected.val context) :
    (postSkelL setup codec checks decision count selected services chosen challenge context).IsQueryBoundP
      (fun query => valueRead? query = true) 2 := by
  rcases context with state | ⟨server, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, log,
    next⟩), state, runtime⟩
  · trivial
  · trivial
  · trivial
  · simp only [postSkelL]
    split
    · rw [isQueryBoundP_map_iff]
      refine fwd_hidden _ _ _ ?_
      rw [low_eq, skelResumeL, option_simulate_bind]
      refine isQueryBoundP_bind (n := 1) (m := 1) ?_ fun result reached => ?_
      · exact low_hidden setup _ _ 1 (IsQueryBoundP.simulateQ_run_StateT_of_step (resume_root setup codec checks _ _ raw
          value ephemeral _ _ native.2 consumed) (fun query current =>
            resumeImpl_hidden setup.hmac native.2.sessions services query current) _) _
      · rcases result with ⟨_ | answer, after⟩
        · trivial
        · dsimp only
          rw [composeOpt_run, isQueryBoundP_map_iff, composeOpt_run, isQueryBoundP_map_iff]
          have counts : CountsCreates (PqxdhDynamicKemRouter.post setup.kem selected.val
              (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge
              PqxdhRegistrationJointBeaconOpaqueFinishRouter.placeholder) := router_counts _ _ _
          have mono : StepMono (lowImpl (V := V) setup (PqxdhDynamicKemJointRouter.post setup.joint setup.kem
              selected.val (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge
              PqxdhRegistrationJointBeaconOpaqueFinishRouter.placeholder)) created :=
            low_mono (coins := PqxdhPrivateKemSource.ccaCoins) (primitives := setup.joint) setup counts
          have grows := option_monotone _ created mono _ _ _ reached
          refine (isQueryBoundP_of_potBound (top_potentialL (V := V) (coins := PqxdhPrivateKemSource.ccaCoins)
            (primitives := setup.joint) setup codec checks _ _ services selected.val challenge counts _
            ((owners, log ++ [some ephemeral.secret]), (answer.2, after)))).mono ?_
          have pend := pending_anti selected.val grows
          simp only [KemOnceL] at once
          simp only [potentialL]
          change pending selected.val (created after) ≤ pending selected.val state.2.created at pend
          omega
    · trivial

end Skeleton

/-! ### The logged prefix -/

section Prefix

variable {ι ι' : Type} {baseSpec : OracleSpec ι} {spec' : OracleSpec.{0, 0} ι'} {KemSK Reader Response : Type}

/-- The native backend of the logged source client under the actual encapsulator, collapsed onto a KEM router. -/
noncomputable def preLowL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) :=
  composeOpt (PqxdhRegistrationJointKemEntryFactor.mapRun (PqxdhRegistrationJointKemEncapsulation.actual setup)
    (implL setup codec checks identityIndex publicIdentity)) router

/-- The logged source client collapsed onto its native backend under the actual encapsulator and a KEM router. -/
noncomputable def preTopL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) :=
  composeOpt (clientL (Response := Response) setup codec identityIndex)
    (preLowL setup codec checks identityIndex publicIdentity router)

/-- The potential of the logged prefix: the owners holding the selected KEM index, plus one while the router has not yet handed it out. The log is not read. -/
def prePotentialL (selected : Nat) (state : Local × (NativeState KemSK × PqxdhDynamicKemJointSource.State KemSK)) :
    Nat :=
  ownerCount selected state.1.1 + pending selected (created state.2.2)

/-- On a classical request, the collapsed logged backend is the collapsed classical source backend (`PqxdhRegistrationJointKemEncapsulation.query_actual`). -/
theorem preLowL_inl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) α) :
    simulateQ (preLowL setup codec checks identityIndex publicIdentity router)
        (simulateQ (fun q => ((SpecL KemSK Response).query (.inl q) : OracleComp (SpecL KemSK Response) _)) work) =
      simulateQ (preLow setup codec checks identityIndex publicIdentity router) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, simulateQ_spec_query]
  have backend : PqxdhRegistrationJointKemEntryFactor.mapRun (PqxdhRegistrationJointKemEncapsulation.actual setup)
      (implL setup codec checks identityIndex publicIdentity) (.inl query) =
      PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity query := by
    apply StateT.ext
    intro state
    rw [PqxdhRegistrationJointKemEntryFactor.mapRun_run]
    exact PqxdhRegistrationJointKemEncapsulation.query_actual setup codec checks identityIndex publicIdentity query
      state
  simp only [preLowL, preLow, composeOpt, backend]
  rfl

variable {coins : {X : Type} → ProbComp X → OracleComp spec' X} {primitives : PqxdhJointIdentity.Primitives}
  {pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
    (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp spec')))}

/-- The logged prefix backend `preLowL` on the combined KEM router is monotone in the router's KEM creation counter `created` when the pool counts its creations (`CountsCreates`): no step decreases it (`stepMono_composeOpt` with `combine_mono`). -/
theorem preLowL_mono (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (counts : CountsCreates pool) :
    StepMono (preLowL (Response := Response) setup codec checks identityIndex publicIdentity
      (PqxdhDynamicKemJointRouter.combine coins primitives pool)) (fun state => created state.2) :=
  stepMono_composeOpt _ _ created (combine_mono coins primitives pool counts)

/-- No logged-source request other than `create` increases the count of owners holding the selected KEM index: a source14 request by `PqxdhRegistrationJointBeaconFinishOnce.client_count`; the logged accept and the Server read keep the owners. -/
theorem clientL_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected identityIndex : Nat)
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (notCreate : ¬ CreateKindL query) (held : Local) :
    ∀ result ∈ support ((clientL (Response := Response) setup codec identityIndex query).run held),
      ownerCount selected result.2.1 ≤ ownerCount selected held.1 := by
  rcases query with query | later
  · by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
    · obtain ⟨raw, rfl⟩ := accept
      intro result member
      change result ∈ support ((fun answer => (answer.1, (held.1, held.2 ++ [answer.2]))) <$>
        ((SpecL KemSK Response).query (.inr raw) : OracleComp (SpecL KemSK Response) _)) at member
      rw [support_map] at member
      obtain ⟨_, -, rfl⟩ := member
      exact le_rfl
    · intro result member
      rw [clientL_run setup codec identityIndex query (fun raw same => accept ⟨raw, same⟩) held, support_map] at member
      obtain ⟨inner, reached, rfl⟩ := member
      exact client_count setup codec selected query notCreate held.1 inner (simulate_support _ _ reached)
  · intro result member
    change result ∈ support ((fun seed => ((seed, held.2), held)) <$>
      simulateQ (fun q => ((SpecL KemSK Response).query (.inl q) : OracleComp (SpecL KemSK Response) _))
        (PqxdhRegistrationJointServiceSchedule.poolLift (Response := Response) (.inl (.inr (.reveal identityIndex)))))
      at member
    rw [support_map] at member
    obtain ⟨_, -, rfl⟩ := member
    exact le_rfl

/-- A raw `create` of the logged source client keeps the prefix potential: it is the classical `create` with the log kept (`PqxdhRegistrationJointBeaconFinishOnce.pre_create`). -/
theorem preL_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (counts : CountsCreates pool)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) (owners : List EncodedEntry) (log : Log)
    (native : NativeState KemSK) (lower : PqxdhDynamicKemJointSource.State KemSK) :
    ∀ result ∈ support (((simulateQ (preLowL setup codec checks identityIndex publicIdentity
        (PqxdhDynamicKemJointRouter.combine coins primitives pool))
        ((clientL (Response := Response) setup codec identityIndex (.inl (.inl (.inr (.create pin keyId))))).run
          (owners, log))).run).run (native, lower)), ∀ value, result.1 = some value →
      ownerCount selected value.2.1 + pending selected (created result.2.2) ≤
        ownerCount selected owners + pending selected (created lower) := by
  intro result member value found
  rw [clientL_run setup codec identityIndex _ (fun raw same => by cases same) (owners, log), simulateQ_map,
    preLowL_inl, OptionT.run_map, StateT.run_map, support_map] at member
  obtain ⟨inner, reached, rfl⟩ := member
  rcases inner with ⟨_ | inner, after⟩
  · cases found
  · simp only [Option.map_some, Option.some.injEq] at found
    subst found
    exact pre_create setup codec checks identityIndex publicIdentity selected counts pin keyId owners native lower _
      reached inner rfl

/-- No logged-source request increases the prefix potential, including a request the router stops. -/
theorem pre_stepL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (counts : CountsCreates pool)
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain)
    (state : Local × (NativeState KemSK × PqxdhDynamicKemJointSource.State KemSK)) :
    ∀ result ∈ support (((preTopL (Response := Response) setup codec checks identityIndex publicIdentity
        (PqxdhDynamicKemJointRouter.combine coins primitives pool) query).run).run state),
      prePotentialL selected result.2 ≤ prePotentialL selected state := by
  obtain ⟨⟨owners, log⟩, native, lower⟩ := state
  intro result member
  rw [preTopL, composeOpt_step, support_map] at member
  obtain ⟨inner, reached, rfl⟩ := member
  have grows := option_monotone _ _ (preLowL_mono setup codec checks identityIndex publicIdentity counts) _
    (native, lower) _ reached
  have pend := pending_anti selected grows
  rcases inner with ⟨_ | ⟨answer, held⟩, after⟩
  · simp only [prePotentialL, Option.map_none, Option.getD_none]
    dsimp only at pend
    omega
  · simp only [prePotentialL, Option.map_some, Option.getD_some]
    by_cases create : CreateKindL query
    · obtain ⟨pin, keyId, rfl⟩ : ∃ pin keyId, query = .inl (.inl (.inr (.create pin keyId))) := by
        rcases query with ((coin | request) | read) | later
        · simp [CreateKindL, CreateKind] at create
        · cases request with
          | create pin keyId => exact ⟨pin, keyId, rfl⟩
          | _ => simp [CreateKindL, CreateKind] at create
        · simp [CreateKindL, CreateKind] at create
        · simp [CreateKindL] at create
      exact preL_create setup codec checks identityIndex publicIdentity selected counts pin keyId owners log native
        lower _ reached (answer, held) rfl
    · have source := option_support _ _ _ _ reached (answer, held) rfl
      have counted := clientL_count setup codec selected identityIndex query create (owners, log) _ source
      dsimp only at counted pend
      omega

/-- No logged-source program increases the prefix potential. -/
theorem pre_runL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (counts : CountsCreates pool) {α : Type}
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) α)
    (state : Local × (NativeState KemSK × PqxdhDynamicKemJointSource.State KemSK)) :
    ∀ result ∈ support (((simulateQ (preTopL (Response := Response) setup codec checks identityIndex publicIdentity
        (PqxdhDynamicKemJointRouter.combine coins primitives pool)) work).run).run state),
      prePotentialL selected result.2 ≤ prePotentialL selected state :=
  option_invariant _ (fun current => prePotentialL selected current ≤ prePotentialL selected state)
    (fun query current holds result member =>
      (pre_stepL setup codec checks identityIndex publicIdentity selected counts query current result member).trans
        holds)
    work state le_rfl

/-- The logged commands interpreted by the actual encapsulator and a KEM router do not increase the prefix potential. -/
theorem commandsL_once (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (counts : CountsCreates pool) {α : Type}
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) α) (owners : List EncodedEntry) (log : Log)
    (native : NativeState KemSK) (lower : PqxdhDynamicKemJointSource.State KemSK) :
    ∀ result ∈ support (((simulateQ (PqxdhDynamicKemJointRouter.combine coins primitives pool)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity work owners log
            native))).run).run lower), ∀ reached, result.1 = some reached →
      ownerCount selected reached.1.2.1 + pending selected (created result.2) ≤
        ownerCount selected owners + pending selected (created lower) := by
  intro result member reached found
  rw [run_clientL (Response := Response), PqxdhRegistrationJointKemEntryFactor.simulateQ_mapRun, composeOpt_run,
    composeOpt_run, Functor.map_map, support_map] at member
  obtain ⟨inner, member, rfl⟩ := member
  have bound := pre_runL (coins := coins) (primitives := primitives) (Response := Response) setup codec checks
    identityIndex publicIdentity selected counts work ((owners, log), (native, lower)) inner member
  rcases inner with ⟨_ | answer, after⟩
  · cases found
  · simp only [Option.map_some, Option.some.injEq] at found
    subst found
    simpa [prePotentialL] using bound

end Prefix

/-! ### Every logged prechallenge context satisfies `KemOnceL` -/

section Context

open PqxdhDeploymentLaterServerOpaque (OpaqueCut OpaqueContext opaqueScan sourcePreOpaque)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- An active cut reached by the explicit logged opaque scan under the stopped router keeps the prefix potential of its start. -/
theorem opaqueScanL_once (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × PqxdhRegistrationJointAcceptCutTag.Tag → R)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (index : Nat) (owners : List EncodedEntry)
    (log : Log) (native : NativeState KemSK) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (lower : PqxdhDynamicKemJointSource.State KemSK) :
    ∀ result ∈ support (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected
        pairs) (opaqueScan (Reader := Reader) setup codec checks identityIndex publicIdentity observe work index owners
          log native)).run).run lower),
      ∀ raw value ephemeral consumed native' owners' log' next,
        result.1 = some (.pending raw value ephemeral consumed native' owners' log' next) →
        ownerCount selected owners' + pending selected (created result.2) ≤
          ownerCount selected owners + pending selected (created lower) := by
  have counts : CountsCreates (PqxdhDynamicKemRouter.source setup.baseImpl setup.kem selected pairs) :=
    source_counts _ _ _ _
  have mono : StepMono (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
      created :=
    combine_mono (fun work => work) setup.joint _ counts
  intro result member raw value ephemeral consumed native' owners' log' next found
  rw [opaqueScan, option_simulate_bind, mem_support_bind_iff] at member
  obtain ⟨first, firstReached, member⟩ := member
  rcases first with ⟨_ | reached, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member] at found
    cases found
  · have bound := commandsL_once (coins := fun work => work) (primitives := setup.joint) (Response := Response) setup
      codec checks identityIndex publicIdentity selected counts _ owners log native lower _ firstReached reached rfl
    dsimp only at member
    split at member
    · simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      rw [member] at found
      cases found
    · rename_i rawCut nextCut cutEq
      split at member
      · obtain ⟨_, contradiction⟩ := PqxdhDeploymentLaterServerItemSplit.rejectRunL_complete setup codec checks
          identityIndex publicIdentity observe _ _ _ _ _ _ _ _ (option_support _ _ _ _ member _ found)
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
          · obtain ⟨_, contradiction⟩ := PqxdhDeploymentLaterServerItemSplit.rejectRunL_complete setup codec checks
              identityIndex publicIdentity observe _ _ _ _ _ _ _ _ (option_support _ _ _ _ member _ found)
            cases contradiction
          · simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
            rw [member] at found
            simp only [Option.some.injEq, OpaqueCut.pending.injEq] at found
            obtain ⟨-, -, -, -, -, rfl, -, -⟩ := found
            rw [member]
            have := pending_anti selected grows
            dsimp only at this bound ⊢
            omega

/-- Every logged prechallenge context of the logged KEM-ideal branch satisfies `KemOnceL`: at the selected raw accept, at most one owner holds the selected KEM index, and none does while the router has not yet handed it out. -/
theorem sourcePreOpaqueL_once (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    ∀ context ∈ support (sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index chosen), KemOnceL selected.val context := by
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
    · simp only [KemOnceL]
    · rcases cut with outcome | ⟨raw, value, ephemeral, consumed, native, owners, log, next⟩
      · simp only [KemOnceL]
      · simp only [KemOnceL]
        have := opaqueScanL_once (Response := Response) setup codec checks _ _ _ work index [] [] _ selected.val _ _
          result resultReached raw value ephemeral consumed native owners log next cutCase
        have start : pending selected.val (created (born.2.1.1, PqxdhDynamicKemRouter.empty (KemSK := KemSK))) = 1 := by
          have zero : (PqxdhDynamicKemRouter.empty (KemSK := KemSK)).created = 0 := rfl
          simp [pending, created, zero]
        have empty : ownerCount selected.val [] = 0 := rfl
        rw [start, empty] at this
        exact this

/-- Every outcome of G1's prefix for the logged KEM-ideal branch has a logged prechallenge context satisfying `KemOnceL`. -/
theorem sharedStartL_once (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    ∀ start ∈ support (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index), KemOnceL selected.val start.2.2.1 := by
  intro start reached
  simp only [sharedStartL, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨chosen, _, context, contextReached, encapsulated, _, rfl⟩ := reached
  exact sourcePreOpaqueL_once setup codec checks ensureInit supplied decision work runtime count selected index chosen
    context contextReached

end Context

/-! ### Two hidden reads and the two-slot PRF step -/

section Two

open PqxdhSecretInputKdf (hmacPrfRealGame hmacPrfRandomGame)
open PqxdhCorrelatedExpandHybrid (IsRoot uniformGame indexedReduction)
open PqxdhRegistrationJointKemEntryFactor (Output)
open PqxdhRegistrationJointKemSecondEntry (IsValue)
open PqxdhExtractRomHiddenSuffix (splitGame)
open PqxdhDeploymentLaterServerOpaque (opaqueBranch)
open PqxdhDeploymentLaterServerItemTargets (sharedClientL)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- Stage T over the logged source. The logged root client makes at most two root requests, repeated requests included: one at the Server's private resumption root and at most one at a grouped Beacon finish on the challenge marker. No premise is needed. -/
theorem rootClientL_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsQueryBoundP IsRoot 2 :=
  PqxdhDeploymentLaterServerItemRoot.rootClientL_root setup codec checks ensureInit supplied decision work runtime count
    selected index 2 fun start reached =>
      postSkelL_two setup codec checks decision count selected _ start.2.1 start.2.2.2 start.2.2.1
        (sharedStartL_once setup codec checks ensureInit supplied decision work runtime count selected index start
          reached)

/-- Stage T over the logged source for the logged factored root client: at most two value requests. -/
theorem entryClientL_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := Output)) 2 :=
  PqxdhDeploymentLaterServerItemRoot.entryClientL_value setup codec checks ensureInit supplied decision work runtime
    count selected index 2 fun start reached =>
      postSkelL_two setup codec checks decision count selected _ start.2.1 start.2.2.2 start.2.2.1
        (sharedStartL_once setup codec checks ensureInit supplied decision work runtime count selected index start
          reached)

/-- Stage S2 over the logged source with two slots: G1's split world on the logged prefix and client and the uniform-root world on the logged root client are distinguishable with advantage at most the sum of two one-query HMAC-SHA-512 PRF advantages. -/
theorem splitL_uniform_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    (splitGame (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClientL setup codec checks decision count selected)).boolDistAdvantage
      (uniformGame (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)) ≤
      ∑ slot ∈ Finset.range 2,
        (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
          ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)) :=
  PqxdhDeploymentLaterServerItemRoot.splitL_uniform setup codec checks ensureInit supplied decision work runtime count
    selected index 2 (rootClientL_two setup codec checks ensureInit supplied decision work runtime count selected index)

/-- Stages S1c and S2 over the logged source with two slots: the logged opaque KEM-ideal branch and the uniform-root world on the logged root client are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256` (route R1) plus the sum of two one-query HMAC-SHA-512 PRF advantages. -/
theorem opaqueBranchL_uniform_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ kind, work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some kind) (budget kind)) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      (uniformGame (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range 2,
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) :=
  PqxdhDeploymentLaterServerItemRoot.opaqueBranchL_uniform setup codec checks ensureInit supplied decision work runtime
    count selected index budget certified 2
    (rootClientL_two setup codec checks ensureInit supplied decision work runtime count selected index)

end Two

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.finishBoundL_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.finishBoundL_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.logClient_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.logClient_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.clientL_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.clientL_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.groupedClientL_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.groupedClientL_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.skelImplL_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.skelImplL_marked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.midImplL_inl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.midImplL_inl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.midL_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.midL_marked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.groupedClientL_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.groupedClientL_marked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.groupedClientL_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.groupedClientL_count

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.midL_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.midL_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.createL_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.createL_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.top_stepL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.top_stepL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.top_potentialL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.top_potentialL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.postSkelL_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.postSkelL_two

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.preLowL_inl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.preLowL_inl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.preLowL_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.preLowL_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.clientL_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.clientL_count

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.preL_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.preL_create

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.pre_stepL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.pre_stepL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.pre_runL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.pre_runL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.commandsL_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.commandsL_once

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.opaqueScanL_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.opaqueScanL_once

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.sourcePreOpaqueL_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.sourcePreOpaqueL_once

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.sharedStartL_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.sharedStartL_once

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.rootClientL_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.rootClientL_two

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.entryClientL_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.entryClientL_two

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.splitL_uniform_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.splitL_uniform_two

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.opaqueBranchL_uniform_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemOnce.opaqueBranchL_uniform_two
