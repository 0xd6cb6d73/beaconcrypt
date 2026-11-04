-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeBuildBills
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendRequestBounds
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformNativeFrontendBills
open BeaconcryptCore.Refinement
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open RegistrationNativePlatformEffectCompiler (Spec effect)
open RegistrationNativePlatformNativeBuildBills (effectCost)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePublicationCosts (hashCost)
open RegistrationNativeBuildCosts (adminCost envCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_mono weighted_run weighted_simulate weighted_indicator)
variable {n : Nat} {E Platform A B S : Type}
def publicationCost (qSign : Nat) (kind : EffectKind) := hashCost kind + (hashCost kind + coinCost qSign kind) * 3
def branchCost (qSign : Nat) (kind : EffectKind) := publicationCost qSign kind + adminCost kind
private def Bounded (kind : EffectKind) (work : StateT S (OracleComp (Spec n)) A) (cap : Nat) : Prop :=
  ∀ before, Weighted (effectCost kind) (work.run before) cap
private theorem map_iff {I X Y : Type} {spec : OracleSpec I}
    (cost : I → Nat) (work : OracleComp spec X) (change : X → Y) (cap : Nat) :
    Weighted cost (change <$> work) cap ↔ Weighted cost work cap :=
  isQueryBound_map_iff work change cap _ _
private theorem pure_bound (kind : EffectKind) (value : A) (cap : Nat) :
    Bounded kind (pure value : StateT S (OracleComp (Spec n)) A) cap := by
  intro before
  trivial
private theorem bind_bound (kind : EffectKind) (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (firstCap laterCap : Nat)
    (first : Bounded kind work firstCap) (later : ∀ value, Bounded kind (next value) laterCap) :
    Bounded kind (work >>= next) (firstCap + laterCap) := by
  intro before
  simp only [StateT.run_bind]
  exact weighted_bind _ _ _ firstCap laterCap (first before) (fun result => later result.1 result.2)
private theorem effect_bound (kind : EffectKind) (query : (EnvEffects n).Domain) :
    Bounded kind (effect (Platform := S) query) (envCost kind query) := by
  intro before
  simp only [effect, StateT.run_lift, bind_pure_comp, map_iff]
  exact RegistrationNativeWeightedContext.query_bound (effectCost kind) (.inl query)
variable [primitive : AdapterSealPrimitive.Operations]
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (qSign : Nat) (signing : ∀ request, (sign request).IsTotalQueryBound qSign)
variable (erased : commitment.CommitmentTranscript)
local notation "pairTarget" => RegistrationNativePlatformPairedServerCompiler.target (n := n) source view failure allocation erased helper sign writer
private theorem paired_forward (kind : EffectKind) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) (work : OracleComp (EnvEffects n) A) (cap : Nat)
    (bounded : Weighted (envCost kind) work cap) :
    Bounded kind (simulateQ (pairTarget initial output) (simulateQ RegistrationNativePlatformPairedServerCompiler.forward work)) cap := by
  rw [← QueryImpl.simulateQ_compose]
  have leaves : (pairTarget initial output) ∘ₛ RegistrationNativePlatformPairedServerCompiler.forward = effect := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativePlatformPairedServerCompiler.forward,
      simulateQ_spec_query, RegistrationNativePlatformPairedServerCompiler.target]
  rw [leaves]
  intro before
  exact weighted_run (envCost kind) (effectCost kind) effect work cap before bounded
    (fun query current => effect_bound kind query current)
include signing in
private theorem paired_known (kind : EffectKind) (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) :
    Bounded kind (simulateQ (pairTarget initial output) (RegistrationNativePlatformPairedServerCompiler.known (n := n) control)) (branchCost qSign kind) := by
  unfold RegistrationNativePlatformPairedServerCompiler.known
  simp only [simulateQ_bind, simulateQ_spec_query]
  exact bind_bound kind _ _ (publicationCost qSign kind) (adminCost kind)
    (RegistrationNativePlatformNativeBuildBills.bound_publication helper source view failure allocation sign qSign signing writer kind erased initial output)
    (fun published => paired_forward source view failure allocation helper writer sign erased kind initial output _ _
      (RegistrationNativeBuildCosts.known_after_bound control published kind))
include signing in
private theorem paired_hidden (kind : EffectKind) (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    Bounded kind (simulateQ (pairTarget initial output) (RegistrationNativePlatformPairedServerCompiler.hidden control slot)) (branchCost qSign kind) := by
  unfold RegistrationNativePlatformPairedServerCompiler.hidden
  simp only [simulateQ_bind, simulateQ_spec_query]
  exact bind_bound kind _ _ (publicationCost qSign kind) (adminCost kind)
    (RegistrationNativePlatformNativeBuildBills.bound_publication helper source view failure allocation sign qSign signing writer kind erased initial output)
    (fun published => paired_forward source view failure allocation helper writer sign erased kind initial output _ _
      (RegistrationNativeBuildCosts.hidden_after_bound control slot published kind))
include signing in
/-- Both literal known/hidden source material branches retain the actual publication bill plus their one administrative install attempt. -/
theorem branch_bound (kind : EffectKind) (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) :
    Bounded kind (RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice) (branchCost qSign kind) := by
  cases choice with
  | known output => exact paired_known source view failure allocation helper writer sign qSign signing erased kind control initial output
  | hidden reference => exact paired_hidden source view failure allocation helper writer sign qSign signing erased kind control reference.slot initial _

variable {KemSK : Type}
omit primitive in
def localBill (qSign qKem : Nat) (kind : EffectKind) : (RegistrationNativePlatformPublicFrontend.LocalSpec n KemSK).Domain → Nat
  | .inl query => RegistrationNativeRestrictedCosts.bill (n := n) (KemSK := KemSK) qSign qKem (.inl query) kind
  | .inr _ => 0
omit primitive in
private def effectsToLocal : QueryImpl (Spec n) (OracleComp (RegistrationNativePlatformPublicFrontend.LocalSpec n KemSK)) :=
  RegistrationNativePlatformPublicFrontend.buildEmbedding ∘ₛ RegistrationNativePlatformServerFrontendCompiler.embed
omit primitive in
private theorem effects_to_local_bound (qSign qKem : Nat) (kind : EffectKind) (work : OracleComp (Spec n) A) (cap : Nat)
    (bounded : Weighted (effectCost kind) work cap) :
    Weighted (localBill (n := n) (KemSK := KemSK) qSign qKem kind) (simulateQ (effectsToLocal (KemSK := KemSK)) work) cap := by
  apply weighted_simulate (effectCost kind) _ _ work cap bounded
  intro query
  cases query <;> simp [effectsToLocal, QueryImpl.apply_compose, RegistrationNativePlatformServerFrontendCompiler.embed,
    RegistrationNativePlatformPublicFrontend.buildEmbedding, RegistrationNativePlatformPublicFrontend.effect,
    RegistrationNativePlatformPublicFrontend.localQuery, RegistrationNativePlatformPublicFrontend.localCoin,
    Weighted, localBill, RegistrationNativeRestrictedCosts.bill, effectCost]
omit primitive in
private theorem lifted_effects_bound (qSign qKem : Nat) (kind : EffectKind)
    (work : StateT (RegistrationNativePlatformBoundCompiler.PublicState Platform) (OracleComp (Spec n)) A)
    (cap : Nat) (bounded : Bounded kind work cap) (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    Weighted (localBill (n := n) (KemSK := KemSK) qSign qKem kind)
      (simulateQ (RegistrationNativePlatformPublicFrontend.buildEmbedding (KemSK := KemSK))
        ((RegistrationNativePlatformServerFrontendCompiler.liftEffects work).run before)) cap := by
  unfold RegistrationNativePlatformServerFrontendCompiler.liftEffects StateT.run
  rw [← QueryImpl.simulateQ_compose]
  exact effects_to_local_bound qSign qKem kind _ cap (bounded before)
omit primitive in
private theorem pin_bound (kind : EffectKind) (current : session.ServerAuthenticationPin) :
    Bounded kind (RegistrationNativePlatformServerRestrictedService.pin (n := n) (Platform := Platform) current) (hashCost kind) := by
  unfold RegistrationNativePlatformServerRestrictedService.pin
  have query := effect_bound (n := n) (S := RegistrationNativePlatformBoundCompiler.PublicState Platform) kind
    (.inr (.hash (PqxdhRefinement.absBytes current.public_key)))
  have hash : Bounded kind (effect (n := n) (Platform := RegistrationNativePlatformBoundCompiler.PublicState Platform)
      (.inr (.hash (PqxdhRefinement.absBytes current.public_key)))) (hashCost kind) := by
    cases kind <;> simpa [envCost, effectKind, hashCost] using query
  simpa only [Nat.add_zero] using bind_bound kind _ _ (hashCost kind) 0 hash (fun _ => pure_bound kind _ 0)
omit primitive in
def buildCost (qSign : Nat) (kind : EffectKind) := (coinCost 108 kind + branchCost qSign kind + hashCost kind + adminCost kind) * 4

include signing in
private theorem target_bound (qKem : Nat) (kind : EffectKind) (reservePeer : StateT Platform ProbComp Bool)
    (query : RegistrationNativePlatformServerFrontendProgram.Spec.Domain)
    (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    Weighted (localBill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((((RegistrationNativePlatformPublicFrontend.buildEmbedding (KemSK := KemSK)).mapStateTBase
        (RegistrationNativePlatformServerFrontendCompiler.target (n := n) source view failure allocation erased helper sign writer reservePeer)) query).run before)
      (coinCost 108 kind + branchCost qSign kind + hashCost kind + adminCost kind) := by
  change Weighted _ (simulateQ (RegistrationNativePlatformPublicFrontend.buildEmbedding (KemSK := KemSK))
    ((RegistrationNativePlatformServerFrontendCompiler.target source view failure allocation erased helper sign writer reservePeer query).run before)) _
  cases query with
  | pin current =>
    exact weighted_mono _ _ _ _ (lifted_effects_bound qSign qKem kind _ _ (pin_bound kind current) before) (by omega)
  | reserve =>
    have reserved : Bounded kind (RegistrationNativePlatformBoundCompiler.liftPlatform
        (RegistrationNativePlatformEffectCompiler.compile (n := n) reservePeer)) 0 := by
      intro current
      simp only [RegistrationNativePlatformBoundCompiler.liftPlatform, StateT.run, map_iff]
      exact RegistrationNativePlatformNativeBuildBills.compile_zero kind reservePeer current.2
    exact weighted_mono _ _ 0 _ (lifted_effects_bound qSign qKem kind _ _ reserved before) (Nat.zero_le _)
  | present keyId =>
    have present : Bounded kind (effect (n := n) (Platform := RegistrationNativePlatformBoundCompiler.PublicState Platform) (.inr (.peerPresent keyId))) (adminCost kind) := by
      have actual := effect_bound (n := n) (S := RegistrationNativePlatformBoundCompiler.PublicState Platform) kind (.inr (.peerPresent keyId))
      cases kind <;> simpa [envCost, effectKind, adminCost] using actual
    exact weighted_mono _ _ _ _ (lifted_effects_bound qSign qKem kind _ _ present before) (by omega)
  | service control initial message =>
    simp only [RegistrationNativePlatformServerFrontendCompiler.target,
      RegistrationNativePlatformServerFrontendCompiler.service, StateT.run_bind, StateT.run_lift,
      simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.buildEmbedding,
      RegistrationNativePlatformPublicFrontend.localQuery, bind_assoc, pure_bind]
    rw [Weighted, isQueryBound_query_bind_iff]
    refine ⟨?_, ?_⟩
    · simp only [localBill, RegistrationNativeRestrictedCosts.bill]
      omega
    · intro selected
      cases selected with
      | none => trivial
      | some choice =>
        apply weighted_mono _ _ _ _
          (lifted_effects_bound qSign qKem kind _ _
            (branch_bound source view failure allocation helper writer sign qSign signing erased kind control initial choice) before)
        simp only [localBill, RegistrationNativeRestrictedCosts.bill]
        omega

variable {I : Type} {base : OracleSpec I}
include signing in
/-- The literal corrected public Server build has concrete old/global coin/hash/admin costs from its source material demand, publication, pin and installation leaves. P sampler effects are billed separately. -/
theorem build_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (qKem : Nat) (kind : EffectKind)
    (reservePeer : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (identitySource : RegistrationNativeMldsa.Source) (before : RegistrationNativePlatformPublicFrontend.State identitySource Platform) :
    Weighted (localBill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((RegistrationNativePlatformPublicFrontend.build (n := n) setup sign view failure allocation erased helper writer reservePeer handle application identitySource).run before)
      (buildCost qSign kind) := by
  simp only [RegistrationNativePlatformPublicFrontend.build, StateT.run, map_iff]
  let impl := (RegistrationNativePlatformPublicFrontend.buildEmbedding (n := n) (KemSK := KemSK)).mapStateTBase
    (RegistrationNativePlatformServerFrontendCompiler.target setup.source view failure allocation erased helper sign writer reservePeer)
  let stepCost := coinCost 108 kind + branchCost qSign kind + hashCost kind + adminCost kind
  have typed := weighted_indicator (fun _ => True) stepCost
    ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before.1.server) 4
    ((isQueryBoundP_true_iff _ _).mpr (RegistrationNativePlatformServerFrontendRequestBounds.program handle application before.1.server))
  have freeBound := weighted_run (fun _ => stepCost) (localBill (n := n) (KemSK := KemSK) qSign qKem kind) impl
    ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before.1.server) (stepCost * 4)
    (before.1.environment.receipts, before.2) (by simpa only [ite_true] using typed)
    (target_bound (n := n) (KemSK := KemSK) setup.source view failure allocation helper writer sign qSign signing erased qKem kind reservePeer)
  dsimp only [impl] at freeBound
  rw [← QueryImpl.simulateQ_mapStateTBase_run] at freeBound
  exact freeBound

omit primitive in
/-- Displayed conservative native/global build costs: material108 and at most three charged signing allowances inside four literal frontend leaves. -/
theorem build_cost (count : Nat) (kind : EffectKind) :
    buildCost count kind = match kind with
      | .coin => 4 * (108 + 3 * count)
      | .hash => 20
      | .administrative => 8 := by
  cases kind <;> simp [buildCost, branchCost, publicationCost, coinCost, hashCost, adminCost, Nat.mul_comm]
end BeaconcryptCore.Computational.RegistrationNativePlatformNativeFrontendBills

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeFrontendBills.branch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeFrontendBills.branch_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeFrontendBills.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeFrontendBills.build_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeFrontendBills.build_cost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeFrontendBills.build_cost
