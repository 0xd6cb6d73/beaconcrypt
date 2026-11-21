-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle
import BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree
/-! SDK object installation changes the analysis representation of protocol ownership. Its backend projection retains every physical primitive coordinate, private KEM pool, actual auxiliary state and persistent platform state. The source finish environment is committed explicitly; it is never identified with the preterminal auxiliary state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
open PqxdhRecordLiftInterface (EffectKind)
variable {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

/-- Remove only the protocol-owner representation and administrative instrumentation. Coin/hash effects, native/uniform counts, CTX cache, record server, produced frames and seed-use tables remain exact. -/
def worldBackend (world : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  {world with owners := [], primitive :=
    ({world.primitive.1 with effects := Function.update world.primitive.1.effects .administrative 0}, world.primitive.2)}

structure Backend (n : Nat) (KemSK : Type) where
  auxiliary : RegistrationServerRoleBackend.State
  pool : PqxdhLiveKemBirth.Pool KemSK
  world : PqxdhRecordLiftWorld.State n

def backend (state : Native) : Backend n KemSK :=
  ⟨state.server.world.auxiliary, state.pool, worldBackend state.server.world.world.1⟩

def persistent (state : Native ×Platform) : Backend n KemSK ×Platform :=
  (backend state.1,state.2)

/-- Local source EnvState is an actual returned component of finish, not ghost data reconstructed from the native outcome. -/
def commitEnvironment (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (state : Native) : Native :=
  {state with server := {state.server with world :=
    RegistrationWorldAgreementCompiler.join environment state.server.world.world.1}}

theorem environment_backend (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (owners : List (RegistrationNativeBeaconFrontend.Owner source)) (state : Native) :
    backend (RegistrationNativeFinishTerminalTree.assemble owners environment state)=
      backend (commitEnvironment environment state) := by rfl

private theorem administrative_backend (world : PqxdhRecordLiftWorld.State n)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (administrative : PqxdhRecordLiftInterface.effectKind query=.administrative) :
    worldBackend (PqxdhRecordLiftWorld.chargeEffect query world)=worldBackend world := by
  simp only [worldBackend, PqxdhRecordLiftWorld.chargeEffect, administrative, Function.update_idem]

theorem bundle_backend (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (pending : registration.BeaconPending) (scalar : PqxdhJointGapDh.ScalarBytes) (state : Native) :
    backend (RegistrationNativeBundleTerminal.after index owner pending scalar state)=backend state := by
  unfold backend RegistrationNativeBundleTerminal.after RegistrationNativeBundleTerminal.advancedWorld
  congr 1
  simpa only [worldBackend] using administrative_backend state.server.world.world.1
    (.inr (.advanceOwner owner.worldOwner .initSent)) rfl

theorem publication_backend (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (publication : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) (state : Native) :
    backend (RegistrationNativeBundleLifecycle.after index owner scalar publication state)=backend state := by
  cases publication with
  | fail error | div => rfl
  | ok result => cases result with
    | Err previous => rfl
    | Ok finished => exact bundle_backend index owner finished.pending scalar state

theorem installed_backend (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (completed : registration.CompletedBeacon) (state : Native) :
    backend (RegistrationNativeFinishTerminal.installed index owner completed state)=backend state := by
  unfold backend RegistrationNativeFinishTerminal.installed BeaconcryptCore.Refinement.AdapterPublicFinishEffectInstall.installed
  congr 1
  simpa only [worldBackend] using administrative_backend state.server.world.world.1
    (.inr (.installBeacon owner.worldOwner
      ⟨completed.binding.assigned_key_id,completed.control,completed.binding.associated_data⟩ (.known completed.kernel))) rfl

theorem aborted_backend (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (control : pqxdh.BeaconAborted) (state : Native) :
    backend (RegistrationNativeFinishTerminal.aborted index owner control state)=backend state := by
  unfold backend RegistrationNativeFinishTerminal.aborted RegistrationNativeFinishTerminal.abortedWorld
  congr 1
  simpa only [worldBackend] using administrative_backend state.server.world.world.1
    (.inr (.advanceOwner owner.worldOwner .aborted)) rfl

theorem finish_backend (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (control : pqxdh.BeaconAborted) (reply : RustM (Option registration.CompletedBeacon))
    (owners : List (RegistrationNativeBeaconFrontend.Owner source))
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (state : Native) :
    backend (RegistrationNativeFinishTerminalTree.after index owner control reply
      (RegistrationNativeFinishTerminalTree.assemble owners environment state))=
      backend (commitEnvironment environment state) := by
  cases reply with
  | fail error | div => exact (aborted_backend index owner control _).trans (environment_backend environment owners state)
  | ok result => cases result with
    | none => exact (aborted_backend index owner control _).trans (environment_backend environment owners state)
    | some completed => exact (installed_backend index owner completed _).trans (environment_backend environment owners state)

theorem worldBackend_idempotent (world : PqxdhRecordLiftWorld.State n) :
    worldBackend (worldBackend world)=worldBackend world := by
  simp only [worldBackend, Function.update_idem]

variable {I : Type} {base : OracleSpec I}

abbrev KemSpec (KemSK : Type) :=
  RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK
abbrev LeafSpec (KemSK : Type) := unifSpec + ((Pqxdh.Bytes →ₒ CtxRomAuth.CtxDigest) + KemSpec KemSK)

/-- Only primitive requests occur here. Source protocol ownership is supplied by the returned SDK objects, separately from this private backend. -/
noncomputable def leaf (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (LeafSpec KemSK) (RegistrationNativeExperiment.M n KemSK source)
  | .inl coin => RegistrationNativeExperiment.trusted setup checks representation created source (.inl (.inl coin))
  | .inr (.inl bytes) => RegistrationNativeExperiment.trusted setup checks representation created source (.inl (.inr (.hash bytes)))
  | .inr (.inr kem) => RegistrationNativeExperiment.trusted setup checks representation created source (.inr kem)

noncomputable def backendLeaf (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (LeafSpec KemSK) (StateT (Backend n KemSK) ProbComp)
  | .inl coin => fun before =>
      (fun result => (result.1,{before with world := worldBackend result.2})) <$>
        (PqxdhRecordLiftWorld.effects (.inl coin)).run before.world
  | .inr (.inl bytes) => fun before =>
      (fun result => (result.1,{before with world := worldBackend result.2})) <$>
        (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before.world
  | .inr (.inr kem) => fun before => do
      let result ← (PqxdhRecordLiftWorld.sampled
        ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
          (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) kem).run
            (before.auxiliary,before.pool))).run before.world
      pure (result.1.1,⟨result.1.2.1,result.1.2.2,worldBackend result.2⟩)

private theorem sampled_worldBackend {A : Type} (work : ProbComp A) (world : PqxdhRecordLiftWorld.State n) :
    Prod.map id worldBackend <$> (PqxdhRecordLiftWorld.sampled work).run world=
      (PqxdhRecordLiftWorld.sampled work).run (worldBackend world) := by
  simp only [PqxdhRecordLiftWorld.sampled,worldBackend,StateT.run,Functor.map_map,bind_pure_comp]
  rfl

theorem kem_backend (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (kem : (KemSpec KemSK).Domain) (before : Native) :
    Prod.map id backend <$> (leaf setup checks representation created (.inr (.inr kem))).run before=
      (backendLeaf setup checks representation created (.inr (.inr kem))).run (backend before) := by
  simp only [leaf,backendLeaf,RegistrationNativeExperiment.trusted,StateT.run]
  simp only [backend,PqxdhRecordLiftWorld.sampled,worldBackend,StateT.run,bind_pure_comp,Functor.map_map]
  dsimp only [Prod.map,backend,worldBackend,id_eq]
  simp only [Function.update_idem]

theorem coin_backend (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (coin : unifSpec.Domain) (before : Native) :
    Prod.map id backend <$> (leaf setup checks representation created (.inl coin)).run before=
      (backendLeaf setup checks representation created (.inl coin)).run (backend before) := by
  simp only [leaf,backendLeaf,RegistrationNativeExperiment.trusted,RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server,PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.chargeEffect,
    PqxdhRecordLiftInterface.effectKind,PqxdhRecordLiftWorld.sampled,StateT.run,bind_pure_comp,Functor.map_map]
  dsimp only [Prod.map,backend,worldBackend,id_eq]
  congr 1
  funext result
  congr 3
  congr 2
  funext kind
  cases kind <;> simp

theorem hash_backend (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (bytes : Pqxdh.Bytes) (before : Native) :
    Prod.map id backend <$> (leaf setup checks representation created (.inr (.inl bytes))).run before=
      (backendLeaf setup checks representation created (.inr (.inl bytes))).run (backend before) := by
  simp only [leaf,backendLeaf,RegistrationNativeExperiment.trusted,RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server,PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.chargeEffect,
    PqxdhRecordLiftInterface.effectKind,PqxdhRecordLiftWorld.capability,PqxdhRecordLiftWorld.sampled,
    StateT.run,bind_pure_comp,Functor.map_map]
  dsimp only [Prod.map,backend,worldBackend,id_eq]
  congr 1
  funext result
  congr 3
  congr 2
  funext kind
  cases kind <;> simp

theorem query_backend (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (LeafSpec KemSK).Domain) (before : Native) :
    Prod.map id backend <$> (leaf setup checks representation created query).run before=
      (backendLeaf setup checks representation created query).run (backend before) := by
  cases query with
  | inl coin => exact coin_backend setup checks representation created coin before
  | inr query => cases query with
    | inl bytes => exact hash_backend setup checks representation created bytes before
    | inr kem => exact kem_backend setup checks representation created kem before

/-- Every adaptive source primitive request program, with repeated calls and arbitrary stopping, factors through the persistent backend. This does not assume that source protocol objects equal the native bookkeeping. -/
theorem program_backend {A : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (LeafSpec KemSK) A) (before : Native) :
    Prod.map id backend <$> (simulateQ (leaf setup checks representation created) work).run before=
      (simulateQ (backendLeaf setup checks representation created) work).run (backend before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query state
  exact query_backend setup checks representation created query state

/-- Interpreting the same source primitive program through an arbitrary persistent platform keeps its complete poststate jointly with the primitive backend. -/
theorem program_platform {A : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (LeafSpec KemSK) A) (before : Native) (previous : Platform) :
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((simulateQ (leaf setup checks representation created) work).run before)).run previous=
      (simulateQ coins ((simulateQ (backendLeaf setup checks representation created) work).run (backend before))).run previous := by
  rw [←program_backend setup checks representation created work before,simulateQ_map,StateT.run_map]
  congr 1

/-- Reifying the returned pending source object cannot change any subsequent source primitive request program. Source storage supplies its new phase; physical backend and platform state persist. -/
theorem bundle_continuation {A : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (LeafSpec KemSK) A) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (publication : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) (before : Native) (previous : Platform) :
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((simulateQ (leaf setup checks representation created) work).run
        (RegistrationNativeBundleLifecycle.after index owner scalar publication before))).run previous=
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((simulateQ (leaf setup checks representation created) work).run before)).run previous := by
  rw [program_platform,program_platform,publication_backend]

/-- Finish commits its actual returned environment before reifying the returned source object. No preterminal auxiliary state is revived. -/
theorem finish_continuation {A : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (LeafSpec KemSK) A) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (control : pqxdh.BeaconAborted) (reply : RustM (Option registration.CompletedBeacon))
    (owners : List (RegistrationNativeBeaconFrontend.Owner source))
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : Native) (previous : Platform) :
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((simulateQ (leaf setup checks representation created) work).run
        (RegistrationNativeFinishTerminalTree.after index owner control reply
          (RegistrationNativeFinishTerminalTree.assemble owners environment before)))).run previous=
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((simulateQ (leaf setup checks representation created) work).run
        (commitEnvironment environment before))).run previous := by
  rw [program_platform,program_platform,finish_backend]

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.environment_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.environment_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.bundle_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.bundle_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.publication_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.publication_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.installed_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.installed_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.aborted_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.aborted_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.finish_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.finish_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.worldBackend_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.worldBackend_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.kem_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.kem_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.coin_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.coin_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.hash_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.hash_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.query_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.query_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.program_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.program_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.program_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.program_platform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.bundle_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.bundle_continuation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.finish_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification.finish_continuation
