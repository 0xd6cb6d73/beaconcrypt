-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBuildSafe
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerFacts
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerSafe
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler
/-! The actual corrected Server publication is noninstalling until its literal final continuation. That continuation uses precisely the material choice returned by its preceding demand. Failed publication and insertion outcomes remain part of the same source tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePairedSafe (GlobalInstall)
open RegistrationNativePlatformBoundCompiler (PublicState)
variable {n : Nat} {KemSK E Platform A : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

def Free {X : Type} (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) X) : Prop :=
  work.AllQueriesSatisfy (fun query=>¬GlobalInstall (KemSK := KemSK) PqxdhRecordLiftInterface.Role.beacon query)

omit primitive in
private theorem effects_free {X : Type} (work : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) X)
    (allowed : work.AllQueriesSatisfy RegistrationNativePlatformPairedPublicationFree.Allowed) :
    Free (simulateQ (RegistrationNativePlatformPublicSlotEffects.effects (KemSK := KemSK)) work) := by
  apply RegistrationNativeHiddenAllocationCore.simulation _ _ _ _ _ allowed
  intro query permitted
  cases query with
  | inl query=>
    rcases query with coin|capability
    · simp [RegistrationNativePlatformPublicSlotEffects.effects,RegistrationNativePairedCompile.effects,allQueriesSatisfy_query_iff,GlobalInstall,RegistrationNativeSecretWordAtomInstallCaps.Install,RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]
    · cases capability
      case installServer keyId binding kernel=>exact (permitted .server rfl).elim
      case installBeacon owner shell kernel=>exact (permitted .beacon rfl).elim
      all_goals simp [RegistrationNativePlatformPublicSlotEffects.effects,RegistrationNativePairedCompile.effects,allQueriesSatisfy_query_iff,GlobalInstall,RegistrationNativeSecretWordAtomInstallCaps.Install,RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]
  | inr coin=>simp [RegistrationNativePlatformPublicSlotEffects.effects,RegistrationNativePairedCompile.effects,allQueriesSatisfy_query_iff,GlobalInstall,RegistrationNativeSecretWordAtomInstallCaps.Install,RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]

private theorem forward_run (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (work : OracleComp (EnvEffects n) A) (before : PublicState Platform) :
    simulateQ (RegistrationNativePlatformPublicSlotEffects.effects (KemSK := KemSK))
      ((simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output)
        (simulateQ RegistrationNativePlatformPairedServerCompiler.forward work)).run before) =
      (fun value => (value, before)) <$> simulateQ RegistrationNativePairedCompile.effects work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPairedServerCompiler.forward,
      RegistrationNativePlatformPairedServerCompiler.target, RegistrationNativePlatformEffectCompiler.effect,
      StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind,
      RegistrationNativePlatformPublicSlotEffects.effects, RegistrationNativePairedCompile.effects]
    apply bind_congr
    intro reply
    exact ih reply

def output : Choice n → PqxdhServerAuthKeySchedule.Output
  | .known value => value
  | .hidden reference => PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBoundPublication.fixedSeed

def after (control : pqxdh.ServerState) : Choice n →
    RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) →
    OracleComp (EnvEffects n) (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)))
  | .known _, published => RegistrationNativePairedServerService.knownAfter control published
  | .hidden reference, published => RegistrationHiddenInstall.after control reference.slot published

private theorem branch_run (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : Choice n) (before : PublicState Platform) :
    simulateQ (RegistrationNativePlatformPublicSlotEffects.effects (KemSK := KemSK))
      ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before) = (do
      let reached ← simulateQ (RegistrationNativePlatformPublicSlotEffects.effects (KemSK := KemSK))
        ((RegistrationNativePlatformBoundCompiler.compile source view failure allocation erased helper sign writer initial (output choice)).run before)
      (fun value => (value, reached.2)) <$> simulateQ RegistrationNativePairedCompile.effects (after control choice reached.1)) := by
  cases choice <;>
    simp only [RegistrationNativePlatformServerRestrictedService.branch, RegistrationNativePlatformPairedServerCompiler.known,
      RegistrationNativePlatformPairedServerCompiler.hidden, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, RegistrationNativePlatformPairedServerCompiler.target, output, after]
  all_goals
    apply bind_congr
    intro reached
    exact forward_run source view failure allocation erased helper sign writer initial _ _ reached.2

/-- The actual known/hidden Server continuation emits no Beacon installation, independently of successful output. -/
theorem branch (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : Choice n) (before : PublicState Platform) :
    Free (simulateQ (RegistrationNativePlatformPublicSlotEffects.effects (KemSK := KemSK))
      ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before)) := by
  rw [branch_run]
  apply allQueriesSatisfy_bind
  · exact effects_free _ (RegistrationNativePlatformPairedPublicationFree.compile source view failure allocation erased helper sign writer initial (output choice) before)
  · intro reached
    apply RegistrationNativeHiddenAllocationCore.mapped
    have capped : (after control choice reached.1).IsQueryBoundP
        (RegistrationNativeSecretWordAtomInstallCaps.InstallEnv PqxdhRecordLiftInterface.Role.beacon) 0 := by
      cases choice with
      | known value=>exact RegistrationNativePlatformPairedInstallFacts.server_known_bound .beacon control reached.1
      | hidden reference=>exact RegistrationNativePlatformPairedInstallFacts.server_hidden_bound .beacon control reference.slot reached.1
    have absent := (isQueryBoundP_zero_iff (after control choice reached.1)
      (fun query=>¬RegistrationNativeSecretWordAtomInstallCaps.InstallEnv PqxdhRecordLiftInterface.Role.beacon query)).mp
      (by simpa only [not_not] using capped)
    apply RegistrationNativeHiddenAllocationCore.simulation _ _ _ _ _ absent
    intro query quiet
    rcases query with coin|capability
    · simp only [RegistrationNativePairedCompile.effects,allQueriesSatisfy_query_iff]
      intro impossible
      cases impossible
    · cases capability
      case installBeacon owner shell kernel=>exact (quiet rfl).elim
      all_goals simp [RegistrationNativePairedCompile.effects,allQueriesSatisfy_query_iff,GlobalInstall,RegistrationNativeSecretWordAtomInstallCaps.Install,RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]

def embed : QueryImpl (RegistrationNativePlatformServerFrontendCompiler.Spec n)
    (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK))
  | .inl message => RegistrationNativePlatformPublicSlotEffects.demand message
  | .inr query => RegistrationNativePlatformPublicSlotEffects.effects query

private theorem service_run (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : Message) (before : PublicState Platform) :
    simulateQ (embed (KemSK := KemSK))
      ((RegistrationNativePlatformServerFrontendCompiler.service source view failure allocation erased helper sign writer control initial message).run before) = (do
      let selected ← RegistrationNativePlatformPublicSlotEffects.demand (n := n) (KemSK := KemSK) message
      match selected with
      | none => pure (.ok (.Err control), before)
      | some choice => simulateQ RegistrationNativePlatformPublicSlotEffects.effects ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before)) := by
  simp only [RegistrationNativePlatformServerFrontendCompiler.service, StateT.run_bind,
    StateT.run_lift, bind_pure_comp, simulateQ_bind, simulateQ_spec_query,
    embed, bind_map_left]
  apply bind_congr
  intro selected
  cases selected with
  | none => rfl
  | some choice =>
    simp only [RegistrationNativePlatformServerFrontendCompiler.liftEffects, StateT.run,
      ← QueryImpl.simulateQ_compose]
    have joined : embed (n := n) (KemSK := KemSK) ∘ₛ RegistrationNativePlatformServerFrontendCompiler.embed = RegistrationNativePlatformPublicSlotEffects.effects := by
      funext query
      simp only [QueryImpl.compose, RegistrationNativePlatformServerFrontendCompiler.embed, simulateQ_spec_query, embed]
    rw [joined]

/-- The same actual material demand and every source publication failure remain free of Beacon installation. -/
theorem service (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : Message) (before : PublicState Platform) :
    Free (simulateQ (embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformServerFrontendCompiler.service source view failure allocation erased helper sign writer control initial message).run before)) := by
  rw [service_run]
  apply allQueriesSatisfy_bind
  · simp [RegistrationNativePlatformPublicSlotEffects.demand,allQueriesSatisfy_query_iff,GlobalInstall,RegistrationNativeSecretWordAtomInstallCaps.Install,RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]
  · intro selected
    cases selected with
    | none=>trivial
    | some choice=>exact branch source view failure allocation erased helper sign writer control initial choice before

omit primitive in
private theorem lift_effects_free (work : StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (quiet : RegistrationNativePlatformPairedPublicationFree.Quiet work) (before : PublicState Platform) :
    Free (simulateQ (embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformServerFrontendCompiler.liftEffects work).run before)) := by
  change Free (simulateQ embed (simulateQ RegistrationNativePlatformServerFrontendCompiler.embed (work.run before)))
  rw [← QueryImpl.simulateQ_compose]
  have joined : embed (n := n) (KemSK := KemSK) ∘ₛ RegistrationNativePlatformServerFrontendCompiler.embed = RegistrationNativePlatformPublicSlotEffects.effects := by
    funext query
    simp only [QueryImpl.compose, RegistrationNativePlatformServerFrontendCompiler.embed, simulateQ_spec_query, embed]
  rw [joined]
  exact effects_free _ (quiet before)

omit primitive in
private theorem effect_quiet (query : (EnvEffects n).Domain)
    (free : ∀ role, ¬ RegistrationNativeSecretWordAtomInstallCaps.InstallEnv role query) :
    RegistrationNativePlatformPairedPublicationFree.Quiet
      (RegistrationNativePlatformEffectCompiler.effect (Platform := Platform) query) := by
  intro before
  simp only [RegistrationNativePlatformEffectCompiler.effect, StateT.run_lift, bind_pure_comp, map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr free) (fun _ => trivial)

/-- Every literal corrected Server frontend leaf checks constructor-kind matching, including real reserve and source writer outcomes. -/
theorem target (reserve : StateT Platform ProbComp Bool)
    (query : RegistrationNativePlatformServerFrontendProgram.Spec.Domain) (before : PublicState Platform) :
    Free (simulateQ (embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformServerFrontendCompiler.target source view failure allocation erased helper sign writer reserve query).run before)) := by
  cases query with
  | pin current =>
    apply lift_effects_free
    exact RegistrationNativePlatformPairedPublicationFree.bind_quiet _ _
      (effect_quiet _ (by intro role; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]))
      (fun _ => RegistrationNativePlatformPairedPublicationFree.pure_quiet _)
  | reserve =>
    apply lift_effects_free
    intro current
    simp only [RegistrationNativePlatformBoundCompiler.liftPlatform, StateT.run, map_eq_bind_pure_comp]
    exact allQueriesSatisfy_bind (RegistrationNativePlatformPairedPublicationFree.platform_quiet reserve current.2) (fun _ => trivial)
  | present keyId =>
    apply lift_effects_free
    exact effect_quiet _ (by intro role; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv])
  | service control initial message => exact service source view failure allocation erased helper sign writer control initial message before

/-- The complete actual four-leaf Server controller issues no Beacon installation query under any replies. -/
theorem program (reserve : StateT Platform ProbComp Bool)
    (work : OracleComp RegistrationNativePlatformServerFrontendProgram.Spec A) (before : PublicState Platform) :
    Free (simulateQ (embed (n := n) (KemSK := KemSK))
      ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target source view failure allocation erased helper sign writer reserve) work).run before)) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (target source view failure allocation erased helper sign writer reserve query before)
      (fun reached => ih reached.1 reached.2)
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole

namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))



/-- The actual public Server build issues no Beacon installation, including unsuccessful publication and insertion paths. -/
theorem build (handle : Nat) (application : Option (Slice U8)) (before : State source Platform) :
    Free (simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
      ((executeLocal (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper implementation reservePeer handle application source)).run before)) := by
  simp only [executeLocal, RegistrationNativePlatformPublicFrontend.build, StateT.run, simulateQ_map]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  have joined : (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK) ∘ₛ embedLocal) ∘ₛ buildEmbedding =
      RegistrationNativePlatformRecordPartnerServerOtherRole.embed := by
    funext query
    cases query with
    | inl message => simp only [QueryImpl.compose, buildEmbedding, localQuery, embedLocal,
        simulateQ_spec_query, RegistrationNativePlatformPublicCoinEmbedding.embed,
        RegistrationNativePlatformRecordPartnerServerOtherRole.embed, RegistrationNativePlatformPublicSlotEffects.demand]
    | inr query => cases query with
      | inl query => simp [QueryImpl.compose, buildEmbedding, effect, localQuery, embedLocal,
          RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePlatformRecordPartnerServerOtherRole.embed,
          RegistrationNativePlatformPublicSlotEffects.effects, RegistrationNativePairedCompile.effects]
      | inr coin => simp [QueryImpl.compose, buildEmbedding, localCoin, embedLocal, publicCoin,
          RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.effect,
          RegistrationNativePublicFrontend.liftLocal, RegistrationNativePlatformRecordPartnerServerOtherRole.embed,
          RegistrationNativePlatformPublicSlotEffects.effects, RegistrationNativePairedCompile.effects]
  rw [joined, map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind
    (RegistrationNativePlatformRecordPartnerServerOtherRole.program setup.source view failure allocation erased helper sign implementation reservePeer _ (before.1.environment.receipts,before.2))
    (fun _ => trivial)
/-- The original actual build therefore retains the exact opposite-role successful-handle list. -/
theorem build_handles (handle : Nat) (application : Option (Slice U8)) (before : State source Platform)
    (trace : List PqxdhDeploymentInterface.Handle) :
    (simulateQ (RegistrationNativePlatformRecordPartnerSnapshotHandles.handler (n := n) (KemSK := KemSK) PqxdhRecordLiftInterface.Role.beacon)
      (simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
        ((executeLocal (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper implementation reservePeer handle application source)).run before))).run trace =
      (fun value=>(value,trace)) <$>simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
        ((executeLocal (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper implementation reservePeer handle application source)).run before) := by
  apply RegistrationNativePlatformRecordPartnerSnapshotHandles.free
  have noInstall := build (n := n) (KemSK := KemSK) setup source sign view failure allocation reservePeer erased helper implementation handle application before
  have capped := (isQueryBoundP_zero_iff _ (fun query=>¬RegistrationNativePairedSafe.GlobalInstall (KemSK := KemSK)
    PqxdhRecordLiftInterface.Role.beacon query)).mpr noInstall
  simpa only [not_not] using capped
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.branch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.service
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.build
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.build_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerOtherRole.build_handles
