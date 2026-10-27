import BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver

/-!
The designated generated KEM handle remains the only generated handle in the actual live owner family. Original records, public and identity services, selected decapsulation and every optional native finish retain this invariant on the same full source state. Actual private-prefix support supplies the generated output internally; no selected-key honesty, byte injectivity, callback preservation or storage premise is added.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance
open PqxdhPhase2SourceScheduler PqxdhPhase2SourceAux PqxdhPrivateKemSource PqxdhJointKdfGame
open PqxdhGeneratedBeaconState (IdentityHandle KemHandle)
open PqxdhPhase2JointIdentity (Converted)
open PqxdhPhase2KemProvenance (Owner)
open PqxdhStatefulPhase1EufCma (TargetKemPublicKey)
variable {ι M P I D K X Response A : Type} {baseSpec : OracleSpec ι} {S B : Nat}

def Family (index : Nat) (publicKey : TargetKemPublicKey) (state : State M P I D K A S B) : Prop :=
  ∀ position, Owner index publicKey (state.roles.1.2 position)

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
/-- Every concrete original, forwarded or finish request preserves the designated handle family on its actual supported reply. -/
theorem compiler_step_valid
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (index : Nat) (publicKey : TargetKemPublicKey)
    (query : (Spec baseSpec S B).Domain) (state : State M P I D K A S B)
    (valid : Family index publicKey state) (result : (Spec baseSpec S B).Range query × State M P I D K A S B)
    (supported : result ∈ support ((compiler source writer senderId route decodeFrame localImpl query).run state)) :
    Family index publicKey result.2 := by
  rcases query with ((record | forwarded) | finish)
  · exact PqxdhPhase2KemProvenance.source_step_valid source writer senderId route decodeFrame index publicKey
      record state valid result (support_simulation _ _ supported)
  · simp only [compiler, PqxdhProtocolSelector.compiler, StateT.run, bind_pure_comp, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact valid
  · cases finish with
    | finish selected raw =>
      simp only [compiler, PqxdhPhase2LiveFinish.finishImpl, StateT.run_mk, bind_pure_comp, support_map] at supported
      obtain ⟨nativeResult, nativeSupported, rfl⟩ := supported
      have changed := PqxdhPhase2KemProvenance.native_valid (sourceNative source localImpl)
        index publicKey decodeFrame raw (state.roles.1.2 selected) (valid selected) state.primitive nativeResult nativeSupported
      intro position
      by_cases same : position = selected
      · subst position
        simpa only [PqxdhPhase2LiveFinish.install, Function.update_self] using changed
      · simpa only [PqxdhPhase2LiveFinish.install, Function.update_of_ne same] using valid position

/-- The complete adaptive source schedule preserves the original designated generation on every supported result and live poststate. -/
theorem compiler_valid {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (index : Nat) (publicKey : TargetKemPublicKey)
    (client : OracleComp (Spec baseSpec S B) Result) (state : State M P I D K A S B)
    (valid : Family index publicKey state) (result : Result × State M P I D K A S B)
    (supported : result ∈ support ((simulateQ (compiler source writer senderId route decodeFrame localImpl) client).run state)) :
    Family index publicKey result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    exact valid
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨intermediate, first, rest⟩ := supported
    exact ih intermediate.1 intermediate.2
      (compiler_step_valid source writer senderId route decodeFrame localImpl index publicKey
        query state valid intermediate first) result rest

/-- The same designated family survives the concrete ordinary scheduler and its current identity state, using the full compiler equality. -/
theorem ordinary_valid {Result : Type}
    (attachedVerify : PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : PqxdhJointIdentity.Primitives) (count : Nat)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (index : Nat) (publicKey : TargetKemPublicKey)
    (client : OracleComp (Spec baseSpec S B) Result) (state : State M P I D K A S B)
    (identities : PqxdhPhase1AcceptanceOracle.BareState count)
    (valid : Family index publicKey state)
    (result : Result × State M P I D K (A × PqxdhPhase1AcceptanceOracle.BareState count) S B)
    (supported : result ∈ support ((simulateQ
      (ordinary attachedVerify primitives count source writer senderId route decodeFrame localImpl) client).run
        (PqxdhPhase2OldSource.packState state identities))) :
    Family index publicKey result.2 := by
  rw [← compiler_complete, support_map] at supported
  obtain ⟨original, originalSupport, rfl⟩ := supported
  have sourceSupport := support_simulateQ_run'_subset
    (PqxdhPrivateKemSource.borrowedSelector attachedVerify primitives count)
    ((simulateQ (compiler source writer senderId route decodeFrame localImpl) client).run state) identities
    (show original.1 ∈ support ((simulateQ (PqxdhPrivateKemSource.borrowedSelector attachedVerify primitives count)
      ((simulateQ (compiler source writer senderId route decodeFrame localImpl) client).run state)).run' identities) from by
      rw [StateT.run'_eq, support_map]
      exact Set.mem_image_of_mem _ originalSupport)
  exact compiler_valid source writer senderId route decodeFrame localImpl index publicKey client state valid original.1 sourceSupport

set_option backward.isDefEq.respectTransparency false in
/-- Actual optional publication installs the designated generated owner before every supported adaptive driver result. -/
theorem driver_valid
    {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (env : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (index : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (generated : Generated setup Unit) (transcript : PqxdhEd25519EufCma.Phase1PublicTranscript setup.Context)
    (result : PqxdhEd25519EufCma.Phase1Candidate × (PqxdhPhase2GeneratedDriver.driver env program).State)
    (supported : result ∈ support ((PqxdhPhase2GeneratedDriver.driver env program).main index publicIdentity generated transcript)) :
    Family index generated.target result.2.2 := by
  simp only [PqxdhPhase2GeneratedDriver.driver, mem_support_bind_iff] at supported
  obtain ⟨started, startSupport, selected, selectedSupport, finalSupport⟩ := supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ finalSupport
  have initial := PqxdhPhase2KemProvenance.start_valid setup env.phase1Writer index publicIdentity generated
    env.binding (PqxdhGeneratedBeaconSelector.bundle transcript) env.initial started (support_simulation _ _ startSupport)
  exact compiler_valid env.source env.recordWriter env.senderId env.route env.decode env.localImpl
    index generated.target _ started.2 initial selected selectedSupport

set_option backward.isDefEq.respectTransparency false in
/-- The original private-prefix execution supplies the designated generation internally and establishes the family invariant on its same supported result. -/
theorem program_supported {KemSK : Type}
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
    ∃ output, result.1 = some output ∧ output.context.index = 0 ∧
      (output.context.generated.target, output.context.generated.secret) ∈ support
        (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen) ∧
      Family output.context.index output.context.generated.target output.context.selection.2 := by
  rw [PqxdhGeneratedPhase1Prefix.program_complete] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨seed, _, generated, generatedSupport, selected, selectedSupport, finalSupport⟩ := supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ finalSupport
  have localSupport := support_state_simulation _ _ _ selected selectedSupport
  have originalSupport := support_simulation _ _ localSupport
  have kept := driver_valid env program 0 (primitives.publicKeys seed) (PqxdhPrivateRootSource.eraseGenerated generated) _ selected.1 originalSupport
  exact ⟨_, rfl, rfl, generate_key_support baseImpl kem setup _ generated generatedSupport, kept⟩

end BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance.compiler_step_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance.compiler_step_valid
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance.compiler_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance.compiler_valid
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance.ordinary_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance.ordinary_valid
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance.driver_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance.driver_valid
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance.program_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedProvenance.program_supported
