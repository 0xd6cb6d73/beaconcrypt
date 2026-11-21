-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler

/-! Complete source startup and the unchanged raw native ledger compile to the actual counted indexed KEM program. The executable initial client has no private KEM pool; its separate private interpreter starts empty because that fact follows from the literal native startup body. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProfile
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemServerState (ofNative toNative)
open RegistrationNativeKemCountedProgram (Spec)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (FreshBounds Mode)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}

structure Initial (n : Nat) (source : RegistrationNativeMldsa.Source) where
  created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)
  credential : RegistrationNativeMldsa.Credential source
  state : RegistrationNativeKemServerState.State n source

def ofInitial {source : RegistrationNativeMldsa.Source} (before : RegistrationNativeExperiment.Initial n KemSK source) : Initial n source :=
  ⟨before.created, before.credential, ofNative before.state⟩

def Initial.public {source : RegistrationNativeMldsa.Source} (before : Initial n source) : RegistrationNativeExperiment.Public :=
  ⟨before.created.publicIdentity, before.credential.publicKey, before.created.server.server.metadata.sender⟩

noncomputable def start (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) : ProbComp (Option (Initial n source)) :=
  Option.map ofInitial <$> RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId

noncomputable def program (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    StateT Platform (OracleComp (Spec KemSK)) (Option ((Value × RegistrationNativeLedger.State) × RegistrationNativeKemServerState.State n source)) := do
  let initialized ← StateT.lift (RegistrationNativeKemCountedProgram.lift (start setup source ensureInit identityIndex serverKeyId))
  match initialized with
  | none => pure none
  | some initial => do
      let result ← (simulateQ (RegistrationNativePlatformKemCountedHandler.handler setup checks wire route representation initial.created
        initial.credential view failure allocation reserveRegistration reservePeer erased helper implementation)
        (RegistrationNativeFullCompiler.compile setup.source.crypto wire initial.created.server.server.metadata.sender bounds mode
          (adversary initial.public))).run initial.state
      pure (some result)

omit primitives in
/-- Actual native startup cannot have generated a Beacon recipient row. This is a source control fact, independent of primitive security or correctness. -/
theorem start_empty (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    initial.state.pool = PqxdhLiveKemBirth.empty := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructorSupport, continued⟩ := supported
  cases constructor : constructed.1.1 with
  | none => simp [constructor] at continued
  | some created =>
      simp only [constructor, mem_support_bind_iff] at continued
      obtain ⟨generated, _sampled, continued⟩ := continued
      cases generation : generated.1 with
      | none => simp [generation] at continued
      | some credential =>
          simp only [generation, mem_support_bind_iff] at continued
          obtain ⟨initialized, _native, returned⟩ := continued
          cases native : initialized.1 with
          | fail error | div => simp [native] at returned
          | ok reply => cases reply with
            | none => simp [native] at returned
            | some state =>
                simp only [native, support_pure, Set.mem_singleton_iff, Option.some.injEq] at returned
                cases returned
                rfl

def observe {source : RegistrationNativeMldsa.Source}
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)
    (result : ((Option ((Value × RegistrationNativeLedger.State) × RegistrationNativeKemServerState.State n source) × Platform) × PqxdhLiveKemBirth.Pool KemSK)) : Bool × Platform :=
  (match result.1.1 with
   | none => false
   | some ((value, ledger), native) => event (value, (ledger, toNative native result.2)), result.1.2)

omit primitives in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

omit primitives in
private theorem evaluate_bind {A B : Type} (setup : Setup base KemSK) (work : OracleComp (Spec KemSK) A)
    (next : A → OracleComp (Spec KemSK) B) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (work >>= next) pool = (do
      let result ← RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work pool
      RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (next result.1) result.2) := by
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_bind, StateT.run_bind]

omit primitives in
private theorem evaluate_lift_bind {A B : Type} (setup : Setup base KemSK) (work : ProbComp A)
    (next : A → OracleComp (Spec KemSK) B) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
      (RegistrationNativeKemCountedProgram.lift work >>= next) pool = (do
      let value ← work
      RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (next value) pool) := by
  rw [evaluate_bind, RegistrationNativeKemCountedProgram.ordinary_source]
  simp only [bind_map_left]

private theorem program_run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform) :
    (program setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper implementation bounds mode adversary).run previous = (do
      let initialized ← RegistrationNativeKemCountedProgram.lift (start setup source ensureInit identityIndex serverKeyId)
      match initialized with
      | none => pure (none, previous)
      | some initial => (fun result : ((Value × RegistrationNativeLedger.State) × RegistrationNativeKemServerState.State n source) × Platform => (some result.1, result.2)) <$>
          (((simulateQ (RegistrationNativePlatformKemCountedHandler.handler setup checks wire route representation initial.created
            initial.credential view failure allocation reserveRegistration reservePeer erased helper implementation)
            (RegistrationNativeFullCompiler.compile setup.source.crypto wire initial.created.server.server.metadata.sender bounds mode
              (adversary initial.public))).run initial.state).run previous)) := by
  unfold program
  simp only [StateT.monad_bind_def, StateT.bind, StateT.lift, StateT.run, bind_assoc, pure_bind]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some initial =>
      unfold StateT.bind
      exact bind_pure_comp _ _

/-- The complete initialized source profile, unchanged adaptive native ledger and every native/platform poststate are recovered from the actual counted indexed program. -/
theorem source_profile (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)
    (previous : Platform) :
    observe event <$> RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
      ((program setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer erased helper implementation bounds mode adversary).run previous) PqxdhLiveKemBirth.empty =
      (RegistrationNativePlatformExperiment.profile coins setup checks wire route representation source ensureInit identityIndex serverKeyId
        view failure allocation reserveRegistration reservePeer erased helper implementation bounds mode adversary event).run previous := by
  rw [program_run, evaluate_lift_bind]
  simp only [start, map_bind, bind_map_left, RegistrationNativePlatformExperiment.profile,
    RegistrationNativePlatformMldsaProgram.lift_coins, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro initialized supported
  cases initialized with
  | none =>
      simp only [Option.map_none, RegistrationNativeKemCountedProgram.evaluate, simulateQ_pure,
        StateT.run_pure, map_pure, observe]
  | some initial =>
      have law := congrArg (fun distribution => (fun result => (event (result.1.1, (result.1.2, result.2.1)), result.2.2)) <$> distribution)
        (RegistrationNativePlatformKemCountedHandler.native_source setup checks wire route representation initial.created initial.credential
          view failure allocation reserveRegistration reservePeer erased helper implementation
          (RegistrationNativeFullCompiler.compile setup.source.crypto wire initial.created.server.server.metadata.sender bounds mode
            (adversary initial.public)) initial.state previous)
      simp only [RegistrationNativePlatformKemCountedBundle.project] at law
      rw [start_empty setup source ensureInit identityIndex serverKeyId initial supported] at law
      simp only [Option.map_some, ofInitial, Initial.public, RegistrationNativeExperiment.Initial.public,
        RegistrationNativePlatformKemCountedProgram.execute, RegistrationNativePlatformKemCountedProgram.runState,
        RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, map_apply, Functor.map_map,
        RegistrationNativePlatformKemCountedProgram.arrange,
        RegistrationNativePlatformKemCountedBundle.restore, RegistrationNativePlatformPackedState.pack,
        RegistrationNativePlatformExperiment.run, StateT.run, observe, Prod.map, id_eq] at law ⊢
      exact law

end BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProfile.start_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProfile.start_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProfile.source_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProfile.source_profile
