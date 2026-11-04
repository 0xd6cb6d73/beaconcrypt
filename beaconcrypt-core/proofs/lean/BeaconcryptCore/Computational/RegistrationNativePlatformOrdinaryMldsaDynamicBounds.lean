-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicGame
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateStoppedBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGenerateBounds

/-! The ordinal-only dynamic source game has its finite generation tape derived from actual source callbacks and the original raw-adversary creation budget. Target-first transfer is applied to this fixed ordinal-only program, so no future adaptive public key is supplied to the sampler proof. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicBounds
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformOrdinaryMldsaDynamicGame (program continued observe)
open RegistrationNativeMldsaGhostState (track)
open RegistrationNativeMldsaEager (IsGenerate)
variable {n : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)

variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

omit primitive in
private theorem predicate (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) :
    RegistrationNativeMldsaGenerateBounds.IsGenerate query ↔ IsGenerate source query := by
  cases query with
  | inl coin => simp only [RegistrationNativeMldsaGenerateBounds.IsGenerate, RegistrationNativeMldsaNoGenerate.Allowed, IsGenerate, not_true_eq_false]
  | inr query => cases query <;> simp only [RegistrationNativeMldsaGenerateBounds.IsGenerate,
      RegistrationNativeMldsaNoGenerate.Allowed, IsGenerate, not_true_eq_false, not_false_eq_true]

private theorem callback (selected : Nat) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativePlatformOrdinaryMldsaDynamicGame.State (n := n) (KemSK := KemSK) (Platform := Platform) source) :
    ((track source selected (RegistrationNativePlatformOrdinaryMldsaCountStop.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)).run before).IsQueryBoundP
      (IsGenerate source) (if RegistrationNativeRawAdapter.kind query = (1 : Fin 12) then 1 else 0) := by
  simp only [track, StateT.run, isQueryBoundP_map_iff]
  apply RegistrationNativeMldsaGenerationGhost.bounded
  exact (isQueryBoundP_congr_pred (predicate source)).mp
    (by
      simpa only [RegistrationNativePlatformOrdinaryMldsaCountStop.handler, RegistrationNativePlatformPackedState.pack,
        StateT.run, isQueryBoundP_map_iff] using
        RegistrationNativePlatformOrdinaryMldsaGenerateBounds.handler setup checks wire route representation created credential
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1.1 before.1.2)

private theorem stopped (previous : Platform) (selected : Nat) (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (ghost : RegistrationNativeMldsaGenerationGhost.State) :
    ((simulateQ (RegistrationNativeMldsaStop.freeze
      (fun query => track source selected (RegistrationNativePlatformOrdinaryMldsaCountStop.handler setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query))
      (observe source) RegistrationNativeMldsaTableStop.defaultReply) work).run (((initial.state, previous), ghost), none)).IsQueryBoundP
        (IsGenerate source) cap := by
  apply bounded.simulateQ_run_StateT_of_step _ (((initial.state, previous), ghost), none)
  intro query current
  rcases current with ⟨current, previous⟩
  cases previous with
  | none =>
      simpa only [RegistrationNativeMldsaStop.freeze, RegistrationNativeMldsaStop.monitor,
        StateT.run, bind_pure_comp, isQueryBoundP_map_iff] using
        callback source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected initial.created initial.credential query current
  | some candidate => exact isQueryBoundP_pure _ _ _

/-- The complete tracked ordinal-only source game has at most one startup generation plus its actual typed creation slots. -/
theorem typed (previous : Platform) (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    (program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous selected ensureInit identityIndex serverKeyId).IsQueryBoundP
      (IsGenerate source) (cap + 1) := by
  unfold program
  rw [Nat.add_comm cap 1]
  apply isQueryBoundP_bind
    (RegistrationNativeMldsaGenerationGhost.bounded source selected _ (IsGenerate source) 1
      ((isQueryBoundP_congr_pred (predicate source)).mp
        (RegistrationNativeMldsaGenerateBounds.start (n := n) (source := handleSource source) setup ensureInit identityIndex serverKeyId)) {})
  intro initialized _possible
  cases initial_eq : initialized.1 with
  | none =>
      simp only [continued, initial_eq]
      exact isQueryBoundP_pure _ _ _
  | some initial =>
      simp only [continued, initial_eq, isQueryBoundP_map_iff]
      exact stopped source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous selected initial (adversary initial.public) cap
        (bounded initial.public) initialized.2

/-- The actual original raw compiler derives the finite ordinal-only generation cap budget.create+1 in every native mode. -/
theorem compiled (previous : Platform) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    (program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
      previous selected ensureInit identityIndex serverKeyId).IsQueryBoundP (IsGenerate source) (budget.create + 1) := by
  apply typed source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous _ budget.create _ selected ensureInit identityIndex serverKeyId
  intro publicValue
  simpa only [RegistrationNativeIdentityProfileCreateCaps.wrap_create_sum] using
    RegistrationNativeFullCompiler.compile_bound setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode
      (adversary publicValue) budget (bounded publicValue) (1 : Fin 12)

/-- Moving the selected attempt first preserves the complete true-count native candidate/private-prefix distribution, for the fixed ordinal-only program. -/
theorem target_first (previous : Platform) (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = (1 : Fin 12)) cap)
    (target : Fin (cap + 1)) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    EvalDistEq (RegistrationNativeMldsaTableProgram.evaluate source
      (program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous target.val ensureInit identityIndex serverKeyId) {})
      (do
        let generated ← RegistrationNativeMldsa.generate source
        let others ← RegistrationNativeMldsaEager.family source cap
        (simulateQ (RegistrationNativeMldsaEager.handler source (List.ofFn (target.insertNth generated others)))
          (program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous target.val ensureInit identityIndex serverKeyId)).run {}) := by
  rw [← RegistrationNativePlatformOrdinaryMldsaDynamicGame.zero]
  exact RegistrationNativeMldsaEager.complete_target_first source _ cap
    (typed source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous adversary cap bounded target.val ensureInit identityIndex serverKeyId) target
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicBounds


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicBounds.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicBounds.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicBounds.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicBounds.compiled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicBounds.target_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaDynamicBounds.target_first
