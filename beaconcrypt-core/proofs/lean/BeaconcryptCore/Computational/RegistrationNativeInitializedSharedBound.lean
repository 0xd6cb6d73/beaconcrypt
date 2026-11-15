-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitializedSharedMatch
import BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainCreateCaps
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateStartup

/-! The actual original-ledger SharedMatch event retains its original zero-query collision reduction. Ghost candidate reports are erased only in the private source interpreter; the native transcript, full continued state, source create cap and existing collider costs are unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeInitializedSharedBound
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDynamicIdentityPool (DynamicSpec SourceState IsCreate)
open PqxdhJointPhase1Reports (ProtocolSpec SourceClass)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainSource (implementation)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private def eraseReports : QueryImpl ProtocolSpec (OracleComp DynamicSpec)
  | .inl query => DynamicSpec.query query
  | .inr _ => pure ()

private theorem erase_source (joint : PqxdhJointIdentity.Primitives)
    (work : OracleComp ProtocolSpec Value) (before : SourceState) :
    (simulateQ (implementation joint) work).run before =
      (simulateQ (PqxdhDynamicIdentityPool.lazyImpl joint) (simulateQ eraseReports work)).run before := by
  have composed : PqxdhDynamicIdentityPool.lazyImpl joint ∘ₛ eraseReports = implementation joint := by
    funext query
    cases query <;> simp [QueryImpl.apply_compose, eraseReports, implementation]
  rw [← QueryImpl.simulateQ_compose, composed]

private theorem erase_creates (work : OracleComp ProtocolSpec Value) (count : Nat)
    (bounded : work.IsQueryBoundP (SourceClass IsCreate) count) :
    (simulateQ eraseReports work).IsQueryBoundP IsCreate count := by
  apply OracleComp.IsQueryBoundP.simulateQ_of_step bounded
  · rintro (query | report) selected <;>
      simp_all [eraseReports, SourceClass, OracleComp.isQueryBoundP_query_iff]
  · rintro (query | report) unselected <;>
      simp_all [eraseReports, SourceClass, OracleComp.isQueryBoundP_query_iff]

/-- The unchanged original matching event pays the original collision reduction on the very same private source execution. -/
theorem source_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (readback : RegistrationNativeWire.InitReadBack wire)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (context : RegistrationNativeIdentityWorld.Context n KemSK) (count : Nat)
    (bounded : (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work
      (⟨context, []⟩ : State n KemSK source)).IsQueryBoundP (SourceClass IsCreate) (count + 1)) :
    Pr{let result ← (simulateQ (implementation setup.joint)
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work
        (⟨context, []⟩ : State n KemSK source))).run PqxdhDynamicIdentityPool.initialState}[∃ first second,
      RegistrationNativeSharedMatchCollision.SharedMatch setup.source.crypto
        (RegistrationNativeWire.ledgerCodec wire) first second
        (PqxdhDeploymentServerAuthEvent.regsOf result.1.2.1.ledger.transcript)] ≤
      ∑ target : Fin (count + 1), PqxdhJointIdentity.advantage setup.joint
        (PqxdhDeploymentServerAuthInjective.collider setup.joint count target) := by
  have included := prEvent_mono_of_support
    ((simulateQ (implementation setup.joint)
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work
        (⟨context, []⟩ : State n KemSK source))).run PqxdhDynamicIdentityPool.initialState)
    (fun result => ∃ first second, RegistrationNativeSharedMatchCollision.SharedMatch setup.source.crypto
      (RegistrationNativeWire.ledgerCodec wire) first second
      (PqxdhDeploymentServerAuthEvent.regsOf result.1.2.1.ledger.transcript))
    (fun result => PqxdhDeploymentServerAuthInjective.Collision setup.joint result.2.seeds)
    (by
      rintro result reached ⟨first, second, shared⟩
      exact RegistrationNativeInitializedSharedMatch.source_collision setup checks wire route representation
        created credential readback bounds mode work context result reached first second shared)
  have loss := RegistrationNativeIdentityCollisionBound.lazy_collision_bound setup
    (simulateQ eraseReports (RegistrationNativeIdentityMain.run setup checks wire route representation created credential
      bounds mode work (⟨context, []⟩ : State n KemSK source))) count (erase_creates _ _ bounded)
  rw [← erase_source] at loss
  exact included.trans loss

/-- The literal original raw compiler's create allowance is retained, including all unsuccessful queries. -/
def createCap (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget) : Nat :=
  ∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds (1 : Fin 12) full * budget.cap full

/-- Hidden-bit tests and fresh-message generation do not create a Beacon identity. -/
theorem createCap_eq (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget) :
    createCap bounds budget = budget.create := by
  simp [createCap, Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost, PqxdhDeploymentInterface.Budget.cap]

/-- Every actual initialized execution uses the public client's original command cap; source ownership and source correspondence are discharged internally. -/
theorem run_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (readback : RegistrationNativeWire.InitReadBack wire)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (context : RegistrationNativeIdentityWorld.Context n KemSK) :
    Pr{let result ← (RegistrationNativeExperiment.run setup checks wire route representation created source credential
      bounds mode work (RegistrationNativeIdentityMainSource.project
        ((⟨context, []⟩ : State n KemSK source), PqxdhDynamicIdentityPool.initialState)))}[∃ first second,
      RegistrationNativeSharedMatchCollision.SharedMatch setup.source.crypto
        (RegistrationNativeWire.ledgerCodec wire) first second
        (PqxdhDeploymentServerAuthEvent.regsOf result.2.1.ledger.transcript)] ≤
      ∑ target : Fin (createCap bounds budget + 1), PqxdhJointIdentity.advantage setup.joint
        (PqxdhDeploymentServerAuthInjective.collider setup.joint (createCap bounds budget) target) := by
  have sourceCap := RegistrationNativeIdentityMainCreateCaps.program_bound setup checks wire route representation
    created credential (RegistrationNativeFullCompiler.compile setup.source.crypto wire
      created.server.server.metadata.sender bounds mode work) (createCap bounds budget)
    (RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire created.server.server.metadata.sender
      bounds mode work budget bounded 1) (⟨context, []⟩ : State n KemSK source)
  have fullCap : (RegistrationNativeIdentityMain.run setup checks wire route representation created credential
      bounds mode work (⟨context, []⟩ : State n KemSK source)).IsQueryBoundP
      (SourceClass IsCreate) (createCap bounds budget + 1) := by
    rw [RegistrationNativeIdentityMain.run, isQueryBoundP_map_iff]
    exact sourceCap.mono (Nat.le_succ _)
  rw [← RegistrationNativeIdentityMainFull.full_source setup checks wire route representation created credential
    bounds mode work _ (RegistrationNativeIdentityMainHistoryRun.initial_inv (mlSource := source) setup.joint context).1.1,
    prEvent_map]
  exact source_bound setup checks wire route representation created credential readback bounds mode work context
    (createCap bounds budget) fullCap

private theorem initial_project (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (empty : initial.state.beacons = []) :
    RegistrationNativeIdentityMainSource.project
      ((⟨RegistrationNativeIdentityWorld.project initial.state, []⟩ : State n KemSK source),
        PqxdhDynamicIdentityPool.initialState) = initial.state := by
  rcases initial with ⟨created, credential, server, owners, pool, parsed⟩
  dsimp only at empty
  subst owners
  rfl

/-- Actual generated startup, including every Server constructor, mandatory Server ML and initialization failure, retains the original public matching event and collision loss. -/
theorem profile_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (readback : RegistrationNativeWire.InitReadBack wire)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ exposed, RegistrationNativeInterface.Respects budget (adversary exposed)) :
    Pr{let win ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source
      ensureInit identityIndex serverKeyId bounds mode adversary
      (fun result => @decide (∃ first second, RegistrationNativeSharedMatchCollision.SharedMatch setup.source.crypto
        (RegistrationNativeWire.ledgerCodec wire) first second
        (PqxdhDeploymentServerAuthEvent.regsOf result.2.1.ledger.transcript)) (Classical.propDecidable _)))}[win = true] ≤
      ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
        (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target) := by
  rw [← createCap_eq bounds budget]
  unfold RegistrationNativeExperiment.profile
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun initialized reached => ?_
  cases initialized with
  | none => simp
  | some initial =>
      have empty := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial reached).1
      have loss := run_bound setup checks wire route representation initial.created initial.credential readback bounds mode
        (adversary initial.public) budget (bounded initial.public) (RegistrationNativeIdentityWorld.project initial.state)
      rw [initial_project initial empty] at loss
      simpa only [prEvent_map, decide_eq_true_eq] using loss

end BeaconcryptCore.Computational.RegistrationNativeInitializedSharedBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializedSharedBound.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializedSharedBound.source_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializedSharedBound.createCap_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializedSharedBound.createCap_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializedSharedBound.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializedSharedBound.run_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializedSharedBound.profile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializedSharedBound.profile_bound
