-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal
/-! The complete actual public Server build cannot append a physical Beacon owner. Its moved-token four-leaf controller, stateful preflights, native publication and known or hidden install suffix retain all source failures and the same P. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformEffectCompiler (Spec)
open RegistrationNativeHiddenAllocationService (EffectAllowed)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePlatformHiddenAllocationPublication (Quiet pure_quiet bind_quiet map_quiet)
open RegistrationNativePlatformBoundCompiler (PublicState)
variable {n : Nat} {I KemSK Platform E Encoded A : Type} {base : OracleSpec I}
private theorem server_known (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (RegistrationNativePairedServerService.knownInstall (n := n) control published) EffectAllowed := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
  | ok result => cases result with
    | Err previous => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
    | Ok pending =>
        cases requested : pending.request with
        | fail error | div => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
        | ok keyId =>
            cases divided : pending.into_parts with
            | fail error | div => simp only [RegistrationNativePairedServerService.knownInstall, prepared]; trivial
            | ok parts =>
                simp only [RegistrationNativePairedServerService.knownInstall, prepared]
                change AllQueriesSatisfy (((EnvEffects n).query (.inr (.installServer keyId
                  (PqxdhRecordLiftInterface.PeerBinding.ofSession parts.1.binding) (.known parts.1.ratchet))) :
                    OracleComp (EnvEffects n) Bool) >>= fun inserted => pure (parts.2.finish inserted)) EffectAllowed
                exact ⟨rfl, fun _ => trivial⟩

private theorem server_hidden (reference : RegistrationNativePairedDemand.Reference n) (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (RegistrationHiddenInstall.install control reference.slot published) EffectAllowed := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error | div => simp only [RegistrationHiddenInstall.install, prepared]; trivial
  | ok result => cases result with
    | Err previous => simp only [RegistrationHiddenInstall.install, prepared]; trivial
    | Ok pending =>
        cases requested : pending.request with
        | fail error | div => simp only [RegistrationHiddenInstall.install, prepared]; trivial
        | ok keyId =>
            cases divided : pending.into_parts with
            | fail error | div => simp only [RegistrationHiddenInstall.install, prepared]; trivial
            | ok parts =>
                simp only [RegistrationHiddenInstall.install, prepared]
                change AllQueriesSatisfy (((EnvEffects n).query (.inr (.installServer keyId
                  (PqxdhRecordLiftInterface.PeerBinding.ofSession parts.1.binding) (.hidden reference.slot))) :
                    OracleComp (EnvEffects n) Bool) >>= fun inserted => pure (parts.2.finish inserted)) EffectAllowed
                exact ⟨rfl, fun _ => trivial⟩

theorem server_known_allowed (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (RegistrationNativePairedServerService.knownAfter (n := n) control published) EffectAllowed := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact server_known control published

theorem server_hidden_allowed (reference : RegistrationNativePairedDemand.Reference n) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (RegistrationHiddenInstall.after control reference.slot published) EffectAllowed := by
  cases published with
  | fail error | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok published => exact server_hidden reference control published

private theorem effect_quiet (query : (EnvEffects n).Domain) (allowed : EffectAllowed query) :
    Quiet (RegistrationNativePlatformEffectCompiler.effect (Platform := Platform) query) := by
  intro before
  simp only [RegistrationNativePlatformEffectCompiler.effect, StateT.run_lift, bind_pure_comp]
  exact RegistrationNativeHiddenAllocationCore.mapped _ _ _ ((allQueriesSatisfy_query_iff _ _).mpr allowed)

private theorem effect_program (work : OracleComp (EnvEffects n) A) (allowed : work.AllQueriesSatisfy EffectAllowed) :
    Quiet (simulateQ (RegistrationNativePlatformEffectCompiler.effect (Platform := Platform)) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_quiet value
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_quiet _ _ (effect_quiet query first) (fun reply => ih reply (later reply))

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

private theorem effect_forward (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (work : OracleComp (EnvEffects n) A) :
    simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output)
      (simulateQ RegistrationNativePlatformPairedServerCompiler.forward work) =
      simulateQ RegistrationNativePlatformEffectCompiler.effect work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- Both actual supplied-material Server branches append no physical owner, including real publication and peer installation. -/
theorem branch (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) :
    Quiet (RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice) := by
  cases choice with
  | known output =>
    simp only [RegistrationNativePlatformServerRestrictedService.branch, RegistrationNativePlatformPairedServerCompiler.known,
      simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPairedServerCompiler.target]
    apply bind_quiet _ _ (RegistrationNativePlatformHiddenAllocationPublication.compile source view failure allocation erased helper sign writer initial output)
    intro published
    rw [effect_forward]
    exact effect_program _ (server_known_allowed control published)
  | hidden reference =>
    simp only [RegistrationNativePlatformServerRestrictedService.branch, RegistrationNativePlatformPairedServerCompiler.hidden,
      simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPairedServerCompiler.target]
    apply bind_quiet _ _ (RegistrationNativePlatformHiddenAllocationPublication.compile source view failure allocation erased helper sign writer initial
      (PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBoundPublication.fixedSeed))
    intro published
    rw [effect_forward]
    exact effect_program _ (server_hidden_allowed reference control published)

def Allowed : (RegistrationNativePlatformServerFrontendCompiler.Spec n).Domain → Prop
  | .inl _ => True
  | .inr query => RegistrationNativePlatformHiddenAllocationPublication.Allowed query

omit primitive in
private theorem lift_effects (work : StateT (PublicState Platform) (OracleComp (Spec n)) A) (free : Quiet work)
    (before : PublicState Platform) :
    ((RegistrationNativePlatformServerFrontendCompiler.liftEffects work).run before).AllQueriesSatisfy (Allowed (n := n)) := by
  change (simulateQ RegistrationNativePlatformServerFrontendCompiler.embed (work.run before)).AllQueriesSatisfy Allowed
  apply RegistrationNativeHiddenAllocationCore.simulation _ RegistrationNativePlatformHiddenAllocationPublication.Allowed Allowed _ _ (free before)
  intro query permitted
  exact (allQueriesSatisfy_query_iff _ _).mpr permitted

/-- The source material service itself performs no physical append and retains all supplied-choice outcomes. -/
theorem service (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) (before : PublicState Platform) :
    ((RegistrationNativePlatformServerFrontendCompiler.service source view failure allocation erased helper sign writer control initial message).run before).AllQueriesSatisfy
      (Allowed (n := n)) := by
  simp only [RegistrationNativePlatformServerFrontendCompiler.service, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, ?_⟩
  intro choice
  cases choice with
  | none => trivial
  | some choice => exact lift_effects _ (branch source view failure allocation erased helper sign writer control initial choice) before

/-- Every literal request in the moved-token Server frontend preserves physical owner allocation. -/
theorem target (reserve : StateT Platform ProbComp Bool)
    (request : RegistrationNativePlatformServerFrontendProgram.Spec.Domain) (before : PublicState Platform) :
    ((RegistrationNativePlatformServerFrontendCompiler.target source view failure allocation erased helper sign writer reserve request).run before).AllQueriesSatisfy
      (Allowed (n := n)) := by
  cases request with
  | pin current =>
    apply lift_effects
    unfold RegistrationNativePlatformServerRestrictedService.pin
    exact bind_quiet _ _ (effect_quiet _ rfl) (fun _ => pure_quiet _)
  | reserve =>
    apply lift_effects
    intro previous
    simp only [RegistrationNativePlatformBoundCompiler.liftPlatform, StateT.run]
    exact RegistrationNativeHiddenAllocationCore.mapped _ _ _
      (RegistrationNativePlatformHiddenAllocationPublication.platform_quiet reserve previous.2)
  | present keyId => exact lift_effects _ (effect_quiet (.inr (.peerPresent keyId)) rfl) before
  | service control initial message => exact service source view failure allocation erased helper sign writer control initial message before

/-- The exact four-leaf controller closes its physical-allocation footprint on all source results. -/
theorem program (reserve : StateT Platform ProbComp Bool)
    (work : OracleComp RegistrationNativePlatformServerFrontendProgram.Spec A) (before : PublicState Platform) :
    ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target source view failure allocation erased helper sign writer reserve) work).run before).AllQueriesSatisfy
      (Allowed (n := n)) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (target source view failure allocation erased helper sign writer reserve request before)
      (fun result => ih result.1 result.2)

omit primitive in
private theorem embedding (work : OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n) A)
    (free : work.AllQueriesSatisfy (Allowed (n := n))) :
    (simulateQ (RegistrationNativePlatformPublicFrontend.buildEmbedding (KemSK := KemSK)) work).AllQueriesSatisfy
      (RegistrationNativePlatformHiddenAllocationLocal.Allowed (KemSK := KemSK)) := by
  apply RegistrationNativeHiddenAllocationCore.simulation _ Allowed _ _ _ free
  intro request permitted
  rcases request with message | effect | coin
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · cases effect <;> exact (allQueriesSatisfy_query_iff _ _).mpr permitted
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial

/-- Actual public build combines moved-token control and the dynamic source compiler without a physical append request. -/
theorem build (setup : Setup base KemSK) (reserve : StateT Platform ProbComp Bool)
    (handle : Nat) (application : Option (Slice U8)) {mlSource : RegistrationNativeMldsa.Source}
    (before : RegistrationNativePlatformPublicFrontend.State mlSource Platform) :
    ((RegistrationNativePlatformPublicFrontend.build (n := n) (KemSK := KemSK) setup sign view failure allocation erased helper writer reserve handle application mlSource).run before).AllQueriesSatisfy
      (RegistrationNativePlatformHiddenAllocationLocal.Allowed (KemSK := KemSK)) := by
  simp only [RegistrationNativePlatformPublicFrontend.build, StateT.run]
  apply RegistrationNativeHiddenAllocationCore.mapped
  apply embedding
  exact program setup.source view failure allocation erased helper sign writer reserve _ _

end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.server_known_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.server_known_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.server_hidden_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.server_hidden_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.branch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.service

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps.build
