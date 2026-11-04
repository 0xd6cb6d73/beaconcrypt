-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotAgreement
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter
/-! The actual selective backend preserves the opaque slot observer through every native sampler, material request and publication failure. Explicit administrative effects remain literal shared-World calls. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open RegistrationNativePlatformRecordSlotNeutral (Quiet EffectQuiet)
open RegistrationNativeHiddenAllocationCore (mapped simulation)
open RegistrationNativeHiddenInterpreter (Provider)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK ProviderState A : Type} {base : OracleSpec I}

private theorem every {J V : Type} {spec : OracleSpec J} (work : OracleComp spec V) : work.AllQueriesSatisfy (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query continuation ih => exact ⟨trivial,ih⟩

private theorem coins (work : ProbComp A) : (simulateQ (RegistrationNativeHiddenService.coins (n := n)) work).AllQueriesSatisfy EffectQuiet := by
  apply simulation _ (fun _ => True) EffectQuiet _ work (every work)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem material (slot : PqxdhRecordLiftInterface.Slot n) (before : RegistrationNativeHiddenService.State n) :
    ((RegistrationNativeHiddenService.material slot).run before).AllQueriesSatisfy EffectQuiet := by
  simp only [RegistrationNativeHiddenService.material,StateT.run]
  split
  · trivial
  · exact mapped _ _ EffectQuiet (coins _)

private theorem hidden (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : RegistrationNativeRelatedFamily.Message) (before : RegistrationNativeHiddenService.State n) :
    ((RegistrationNativeHiddenService.demand source input inside message).run before).AllQueriesSatisfy EffectQuiet := by
  simp only [RegistrationNativeHiddenService.demand,StateT.run]
  repeat' split
  all_goals first | trivial | exact mapped _ _ EffectQuiet (material _ _)

private theorem known (bytes : Pqxdh.Bytes) (before : RegistrationNativeSelectiveHiddenService.State n) :
    ((RegistrationNativeSelectiveHiddenService.known bytes).run before).AllQueriesSatisfy EffectQuiet := by
  simp only [RegistrationNativeSelectiveHiddenService.known,StateT.run]
  split
  · trivial
  · exact mapped _ _ EffectQuiet (coins _)

private theorem onHidden (work : StateT (RegistrationNativeHiddenService.State n) (OracleComp (EnvEffects n)) A)
    (quiet : ∀before,(work.run before).AllQueriesSatisfy EffectQuiet) (before : RegistrationNativeSelectiveHiddenService.State n) :
    ((RegistrationNativeSelectiveHiddenService.onHidden work).run before).AllQueriesSatisfy EffectQuiet := by
  exact mapped _ _ EffectQuiet (quiet _)

/-- Every genuine selective material branch uses only public coins; cache hits and overflow retain their actual replies and private tables. -/
theorem demand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : RegistrationNativeRelatedFamily.Message)
    (before : RegistrationNativeSelectiveHiddenService.State n) :
    ((RegistrationNativeSelectiveHiddenService.demand source input inside candidate message).run before).AllQueriesSatisfy EffectQuiet := by
  simp only [RegistrationNativeSelectiveHiddenService.demand,StateT.run]
  repeat' split
  all_goals first
    | exact onHidden _ (hidden source input _ message) _
    | exact mapped _ _ EffectQuiet (known _ _)

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
local notation "implementation" => RegistrationNativeSelectiveHiddenInterpreter.handler (n := n) setup wire sign seed scalar candidate provider
local notation "Ghost" => RegistrationNativePlatformRecordSlotGhost.State n
local notation "Private" => RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState

/-- Outside the explicitly forwarded effect branch, the complete actual backend has no opaque-slot update. -/
theorem quiet (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (notEffect : ∀effect,query ≠ .inl (.inr (.inl (.inr (.inr effect))))) (before : Private) :
    ((implementation query).run before).AllQueriesSatisfy Quiet := by
  rcases query with (prepare | (message | (publication | effect)) | kem) | record
  · trivial
  · simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onKeys,StateT.run]
    apply mapped _ _ Quiet
    exact RegistrationNativePlatformRecordSlotNeutral.effects_quiet _ (demand _ _ _ _ _ _)
  · simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.publication,StateT.run]
    apply mapped _ _ Quiet
    apply mapped _ _ Quiet
    exact RegistrationNativePlatformRecordSlotNeutral.effects_quiet _ (RegistrationNativePlatformRecordSlotNeutral.publication_quiet _ _ _ _ _)
  · exact False.elim (notEffect effect rfl)
  · simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.routed,StateT.run]
    apply mapped _ _ Quiet
    apply mapped _ _ Quiet
    exact RegistrationNativePlatformRecordSlotNeutral.coins_quiet _
  · simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler,StateT.run,StateT.lift,bind_pure_comp]
    apply mapped _ _ Quiet
    apply mapped _ _ Quiet
    exact (allQueriesSatisfy_query_iff _ _).mpr trivial

/-- Closing one public observer query through the actual selective backend equals observing its literal shared-World execution. -/
theorem query (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (ghost : Ghost) (before : Private) :
    RegistrationNativePlatformRecordSlotGhost.program ((implementation query).run before) ghost =
      (fun result => ((result.1.1,result.2),result.1.2)) <$>
        (simulateQ implementation ((RegistrationNativePlatformPublicRecordSlotAgreement.direct query).run ghost)).run before := by
  have interpreted :
      (simulateQ implementation ((RegistrationNativePlatformPublicRecordSlotAgreement.direct query).run ghost)).run before =
        (fun result => ((result.1,RegistrationNativePlatformPublicRecordSlotAgreement.directUpdate query result.1 ghost),result.2)) <$>
          (implementation query).run before := by
    simp only [RegistrationNativePlatformPublicRecordSlotAgreement.direct,StateT.run,simulateQ_map,simulateQ_spec_query]
    change ((fun reply => (reply,RegistrationNativePlatformPublicRecordSlotAgreement.directUpdate query reply ghost)) <$> implementation query).run before = _
    rw [StateT.run_map]
    rfl
  rw [interpreted]
  simp only [Functor.map_map]
  by_cases effect : ∃request,query=.inl (.inr (.inl (.inr (.inr request))))
  · obtain ⟨request,rfl⟩ := effect
    have actual : (implementation (.inl (.inr (.inl (.inr (.inr request)))))).run before =
        (fun reply => (reply,before)) <$> ((WorldSpec n).query (.inr (.inl request)) : OracleComp (WorldSpec n) _) := by
      simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
        RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.effect,StateT.run,
        StateT.lift,bind_pure_comp,PqxdhRecordLiftInterface.effectLift,Functor.map_map]
      cases before
      rfl
    rw [actual]
    simp only [RegistrationNativePlatformRecordSlotGhost.program,simulateQ_map,simulateQ_spec_query,
      StateT.run,Functor.map_map,
      RegistrationNativePlatformPublicRecordSlotAgreement.directUpdate]
    change ((fun reply => (reply,before)) <$> RegistrationNativePlatformRecordSlotGhost.handler (.inr (.inl request))).run ghost = _
    rw [StateT.run_map]
    simp only [RegistrationNativePlatformRecordSlotGhost.handler,StateT.run,Functor.map_map]
  · have noEffect : ∀request,query ≠ .inl (.inr (.inl (.inr (.inr request)))) := by
      intro request same
      exact effect ⟨request,same⟩
    rw [RegistrationNativePlatformRecordSlotNeutral.program_quiet _ (quiet setup wire sign seed scalar candidate provider query noEffect before) ghost]
    have noUpdate : ∀reply,RegistrationNativePlatformPublicRecordSlotAgreement.directUpdate query reply ghost=ghost := by
      intro reply
      rcases query with (prepare | (message | (publication | request)) | kem) | record
      all_goals first | exact False.elim (noEffect request rfl) | rfl
    simp only [noUpdate]


/-- Closing the complete adaptive source slot observer commutes with the actual selective backend, retaining all original private poststate. -/
theorem program (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A) (ghost : Ghost) (before : Private) :
    RegistrationNativePlatformRecordSlotGhost.program ((simulateQ implementation work).run before) ghost =
      (fun result => ((result.1.1,result.2),result.1.2)) <$>
        (simulateQ implementation ((simulateQ RegistrationNativePlatformPublicRecordSlotAgreement.direct work).run ghost)).run before := by
  let left := QueryImpl.Stateful.link RegistrationNativePlatformPublicRecordSlotAgreement.direct implementation
  let right := QueryImpl.Stateful.link implementation RegistrationNativePlatformRecordSlotGhost.handler
  have step (request : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (state : Ghost × Private) :
      Prod.map id Prod.swap <$> (left request).run state=(right request).run state.swap := by
    have source := QueryImpl.Stateful.simulateQ_link_run RegistrationNativePlatformPublicRecordSlotAgreement.direct implementation
      ((RegistrationNativePublicFrontend.Spec n KemSK).query request : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) state.1 state.2
    have target := QueryImpl.Stateful.simulateQ_link_run implementation RegistrationNativePlatformRecordSlotGhost.handler
      ((RegistrationNativePublicFrontend.Spec n KemSK).query request : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) state.2 state.1
    simp only [simulateQ_spec_query] at source target
    change Prod.map id Prod.swap <$> (QueryImpl.Stateful.link RegistrationNativePlatformPublicRecordSlotAgreement.direct implementation request).run (state.1,state.2) =
      (QueryImpl.Stateful.link implementation RegistrationNativePlatformRecordSlotGhost.handler request).run (state.2,state.1)
    rw [source,target]
    simp only [QueryImpl.Stateful.Frame.prod,PFunctor.Lens.State.fst,PFunctor.Lens.State.snd]
    change Prod.map id Prod.swap <$> ((fun result : ((RegistrationNativePublicFrontend.Spec n KemSK).Range request × Ghost) × Private => (result.1.1,(result.1.2,result.2))) <$> _) =
      (fun result : ((RegistrationNativePublicFrontend.Spec n KemSK).Range request × Private) × Ghost => (result.1.1,(result.1.2,result.2))) <$> RegistrationNativePlatformRecordSlotGhost.program _ _
    rw [query setup wire sign seed scalar candidate provider request state.1 state.2]
    simp only [Functor.map_map,Prod.map_def,id_eq,Prod.swap]
  have whole := map_run_simulateQ_eq_of_query_map_eq left right Prod.swap step work (ghost,before)
  rw [QueryImpl.Stateful.simulateQ_link_run,QueryImpl.Stateful.simulateQ_link_run] at whole
  simp only [QueryImpl.Stateful.Frame.prod,PFunctor.Lens.State.fst,PFunctor.Lens.State.snd,
    Functor.map_map,Prod.map_def,id_eq,Prod.swap] at whole
  have mapped := congrArg (Functor.map (fun result : A × (Private × Ghost) => ((result.1,result.2.1),result.2.2))) whole
  simpa only [Functor.map_map,RegistrationNativePlatformRecordSlotGhost.program,PFunctor.Lens.State.mk_put,id_map'] using mapped.symm

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend.demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend.demand
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend.quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend.program
