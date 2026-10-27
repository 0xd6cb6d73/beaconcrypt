import BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver

/-!
The enlarged source scheduler retains the original Server identity and metadata, allocation controls and consumed identifiers. These are exactly the fields used by root acceptance; the actual reached peer maps continue to evolve and remain in the full state. Actual generation and optional publication supply the initial live state. No callback-preservation, successful finish or honest-candidate premise is introduced.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields
open PqxdhPhase2SourceScheduler PqxdhPhase2SourceAux PqxdhPrivateKemSource PqxdhJointKdfGame
variable {ι M P I D K X Response A : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Only root-relevant fixed Server fields are compared; peer maps and all primitive effects stay in their actual reached states. -/
def Fields {I₁ D₁ K₁ A₁ I₂ D₂ K₂ A₂ : Type} {B₁ B₂ : Nat}
    (before : PqxdhRegistrationProtocolState.State M P I₁ D₁ K₁ A₁ S B₁)
    (after : PqxdhRegistrationProtocolState.State M P I₂ D₂ K₂ A₂ S B₂) : Prop :=
  after.controls = before.controls ∧ after.consumed = before.consumed ∧
    ∀ index, (after.roles.1.1 index).server.identity = (before.roles.1.1 index).server.identity ∧
      (after.roles.1.1 index).server.metadata = (before.roles.1.1 index).server.metadata

private theorem support_simulation {κ μ Result : Type} {source : OracleSpec κ} {target : OracleSpec μ}
    (impl : QueryImpl source (OracleComp target)) (work : OracleComp source Result) :
    support (simulateQ impl work) ⊆ support work := by
  have kept := support_simulateQ_run'_subset (impl.liftTarget (StateT Unit (OracleComp target))) work ()
  simpa [simulateQ_liftTarget, StateT.run'_eq, liftM_run_StateT] using kept

private theorem support_state_simulation {κ μ Result Aux : Type} {source : OracleSpec κ} {target : OracleSpec μ}
    (impl : QueryImpl source (StateT Aux (OracleComp target))) (work : OracleComp source Result)
    (state : Aux) (result : Result × Aux) (supported : result ∈ support ((simulateQ impl work).run state)) :
    result.1 ∈ support work := by
  apply support_simulateQ_run'_subset impl work state
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ supported

set_option backward.isDefEq.respectTransparency false in
/-- Original services and every native finish preserve the exact root-relevant Server fields on their supported results. -/
theorem compiler_step_fields
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (query : (Spec baseSpec S B).Domain) (state : State M P I D K A S B)
    (result : (Spec baseSpec S B).Range query × State M P I D K A S B)
    (supported : result ∈ support ((compiler source writer senderId route decodeFrame localImpl query).run state)) :
    Fields state result.2 := by
  rcases query with ((record | forwarded) | finish)
  · have original := support_simulation _ _ supported
    have servers := PqxdhProtocolServerInvariant.source_step_fields source writer senderId route decodeFrame record state result original
    have controls := PqxdhRegistrationProtocolState.source_controls source writer senderId route decodeFrame
      (liftM ((RawCtxProtocolReveals.SourceSpec S B).query record)) state result
      (by simpa only [simulateQ_spec_query] using original)
    exact ⟨controls.1, controls.2, servers⟩
  · simp only [compiler, PqxdhProtocolSelector.compiler, StateT.run, bind_pure_comp, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  · cases finish with
    | finish selected raw =>
      simp only [compiler, PqxdhPhase2LiveFinish.finishImpl, StateT.run_mk, bind_pure_comp, support_map] at supported
      obtain ⟨nativeResult, _, rfl⟩ := supported
      exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- The full adaptive source scheduler preserves fixed Server fields while retaining the actual evolving peer maps. -/
theorem compiler_fields {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (Spec baseSpec S B) Result) (state : State M P I D K A S B)
    (result : Result × State M P I D K A S B)
    (supported : result ∈ support ((simulateQ (compiler source writer senderId route decodeFrame localImpl) client).run state)) :
    Fields state result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨intermediate, first, rest⟩ := supported
    have before := compiler_step_fields source writer senderId route decodeFrame localImpl query state intermediate first
    have after := ih intermediate.1 intermediate.2 result rest
    exact ⟨after.1.trans before.1, after.2.1.trans before.2.1, fun index =>
      ⟨(after.2.2 index).1.trans (before.2.2 index).1, (after.2.2 index).2.trans (before.2.2 index).2⟩⟩

/-- The concrete ordinary scheduler retains the same Server fields under complete current-identity reassociation. -/
theorem ordinary_fields {Result : Type}
    (attachedVerify : PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : PqxdhJointIdentity.Primitives) (count : Nat)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (Spec baseSpec S B) Result) (state : State M P I D K A S B)
    (identities : PqxdhPhase1AcceptanceOracle.BareState count)
    (result : Result × State M P I D K (A × PqxdhPhase1AcceptanceOracle.BareState count) S B)
    (supported : result ∈ support ((simulateQ
      (ordinary attachedVerify primitives count source writer senderId route decodeFrame localImpl) client).run
        (PqxdhPhase2OldSource.packState state identities))) :
    Fields state result.2 := by
  rw [← compiler_complete, support_map] at supported
  obtain ⟨original, originalSupport, rfl⟩ := supported
  have sourceSupport := support_state_simulation _ _ _ original originalSupport
  exact compiler_fields source writer senderId route decodeFrame localImpl client state original.1 sourceSupport

set_option backward.isDefEq.respectTransparency false in
/-- Actual fresh-owner publication and every enlarged scheduler continuation preserve the original Server fixed fields. -/
theorem driver_fields
    {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (env : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (index : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (generated : Generated setup Unit) (transcript : PqxdhEd25519EufCma.Phase1PublicTranscript setup.Context)
    (result : PqxdhEd25519EufCma.Phase1Candidate × (PqxdhPhase2GeneratedDriver.driver env program).State)
    (supported : result ∈ support ((PqxdhPhase2GeneratedDriver.driver env program).main index publicIdentity generated transcript)) :
    Fields env.initial result.2.2 := by
  simp only [PqxdhPhase2GeneratedDriver.driver, mem_support_bind_iff] at supported
  obtain ⟨started, startSupport, selected, selectedSupport, finalSupport⟩ := supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ finalSupport
  obtain ⟨servers, controls, consumed⟩ := PqxdhGeneratedBeaconState.start_servers setup env.phase1Writer index publicIdentity generated
    env.binding (PqxdhGeneratedBeaconSelector.bundle transcript) env.initial started (support_simulation _ _ startSupport)
  have after := compiler_fields env.source env.recordWriter env.senderId env.route env.decode env.localImpl
    _ started.2 selected selectedSupport
  exact ⟨after.1.trans controls, after.2.1.trans consumed, fun index =>
    ⟨(after.2.2 index).1.trans (congrArg (fun family => (family index).server.identity) servers),
      (after.2.2 index).2.trans (congrArg (fun family => (family index).server.metadata) servers)⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual original generated execution supplies its selected full state and preserves the fixed Server fields through every source operation, native finish and candidate acceptance branch. -/
theorem program_fields {KemSK : Type}
    {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (env : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (attachedVerify : PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : PqxdhJointIdentity.Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (result : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup KemSK (PqxdhPhase2GeneratedDriver.driver env program).State)) ×
        PqxdhPhase1AcceptanceOracle.BareState count)
    (supported : result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives count
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (PqxdhPhase2GeneratedDriver.driver env program)))) :
    ∃ output, result.1 = some output ∧ Fields env.initial output.context.selection.2 := by
  rw [PqxdhGeneratedPhase1Prefix.program_complete] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨seed, _, generated, _, selected, selectedSupport, finalSupport⟩ := supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ finalSupport
  have localSupport := support_state_simulation _ _ _ selected selectedSupport
  have originalSupport := support_simulation _ _ localSupport
  exact ⟨_, rfl, driver_fields env program 0 (primitives.publicKeys seed)
    (PqxdhPrivateRootSource.eraseGenerated generated) _ selected.1 originalSupport⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original generated source execution supplies the same reached Server fields read by native root generation, binding, replay admission and allocation. Only the generated KEM secret is erased from the returned representation. -/
theorem reached_root_fields {KemSK : Type}
    {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (env : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (attachedVerify : PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : PqxdhJointIdentity.Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (result : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup KemSK (PqxdhPhase2GeneratedDriver.driver env program).State)) ×
        PqxdhPhase1AcceptanceOracle.BareState count)
    (supported : result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives count
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (PqxdhPhase2GeneratedDriver.driver env program))))
    (secretIdentity : M → Pqxdh.Bytes) (index : Fin S) (server : Pqxdh.ServerState)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId index server env.initial) :
    ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
      PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId index
        server output.context.selection.2 := by
  obtain ⟨output, outputEq, fields⟩ := program_fields env program attachedVerify primitives count baseImpl kem result supported
  refine ⟨PqxdhPrivateRootSource.eraseOutput output, by simp only [outputEq, Option.map_some], ?_⟩
  simpa only [PqxdhProtocolServerInvariant.RootFields, PqxdhPrivateRootSource.eraseOutput,
    PqxdhPrivateRootSource.eraseRetained, fields.1, fields.2.1,
    (fields.2.2 index).1, (fields.2.2 index).2] using initialMatch

end BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.compiler_step_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.compiler_step_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.compiler_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.compiler_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.ordinary_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.ordinary_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.driver_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.driver_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.program_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.program_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.reached_root_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields.reached_root_fields
