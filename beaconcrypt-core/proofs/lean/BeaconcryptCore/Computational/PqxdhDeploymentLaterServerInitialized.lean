-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerReserve

/-! LQ-F: the logged command compiler under the actual encapsulator and the actual private pools is the logged annotated source, and the logged initialized source has the distribution of the selected-first game of the logged source. `openPrepare` and `openAccept` are the exposed logged preparation and accept with the encapsulation interpreted by the actual encapsulator (`prepare_actual`, `accept_actual`); under the actual pools, at the Server's seed slot, they are the annotated logged preparation and accept of the source (`prepare_pool`, `accept_pool`), by the existing generic program lemmas `KemEncapsulation.prefix_program`, `OpenBackend.prefix_program` and `ServerPrefix.program_source` applied to the logged collector. `execute` runs a logged program through the logged command compiler, the actual encapsulator and the actual pools from an encoded state and a log. Every request (`generic_step` through the existing per-request `ServerClient.query_source`, `OpenBackend.program_run` and `KemEncapsulation.program_actual`; `accept_step`; `later_step`) and every program (`program_source`, with the Server-slot invariant carried by `LaterServerSource.query_owned`) has the same result, encoded state and log under `execute` as under the logged annotated source. `commands`, `reserved` and `selectedFirst` are `KemInitialization.commands`, `reserved` and `selectedFirst` with the logged commands; `initialized` (with the reservation of `LaterServerReserve.selected_source` and a creation cap derived from the program) and `constructor_order` give `actual_source_first`, the logged counterpart of `KemInitialization.actual_source_first`. No assumption is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhServerRootPreparation (Inputs Verified Ephemeral)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhRegistrationJointKemCommands (Outcome)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry EncodedState encodeState)
open PqxdhRegistrationJointPreparation (Pool)
open PqxdhDeploymentLaterServerSource (Log Spec collectLogged)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result Next : Type}

/-- The logged preparation with the encapsulation interpreted by the actual encapsulator and the private identity and KEM requests left open. -/
noncomputable def openPrepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) :
    StateT (NativeState KemSK) (OracleComp (PqxdhLiveKemBirth.Spec KemSK))
      ((Option (Inputs Reader ScalarBytes Word32) × List Pqxdh.Bytes) × Option ScalarBytes) := fun state =>
  (fun result => (((result.1.1, result.2), result.1.2), state)) <$>
    (simulateQ (PqxdhRegistrationJointOpenBackend.prefixImpl setup codec checks)
      (simulateQ (PqxdhRegistrationJointServerPrefix.compiler identityIndex) (collectLogged raw))).run
        state.2.server.consumed

/-- The logged accept with the encapsulation interpreted by the actual encapsulator and the private requests left open. -/
noncomputable def openAccept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) :
    StateT (NativeState KemSK) (OracleComp (PqxdhLiveKemBirth.Spec KemSK)) (Option Nat × Option ScalarBytes) := do
  let before ← PqxdhRegistrationJointOpenBackend.native nativeGet
  let collected ← openPrepare setup codec checks identityIndex raw
  let reply ← PqxdhRegistrationJointOpenBackend.native
    (PqxdhRegistrationJointServerAccept.tail setup publicIdentity before collected.1)
  pure (reply, collected.2)

/-- Interpreting the exposed logged preparation by the actual encapsulator gives the open logged preparation. -/
theorem prepare_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((PqxdhDeploymentLaterServerCommands.prepare setup codec checks identityIndex raw).run state) =
      (openPrepare setup codec checks identityIndex raw).run state := by
  have same := PqxdhRegistrationJointKemEncapsulation.prefix_program setup codec checks raw
    (simulateQ (PqxdhRegistrationJointServerPrefix.compiler identityIndex) (collectLogged raw))
    state.2.server.consumed
  change simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((fun result => (((result.1.1, result.2), result.1.2), state)) <$>
        (simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
          (collectLogged raw)).run state.2.server.consumed) =
    (fun result => (((result.1.1, result.2), result.1.2), state)) <$>
      (simulateQ (PqxdhRegistrationJointOpenBackend.prefixImpl setup codec checks)
        (simulateQ (PqxdhRegistrationJointServerPrefix.compiler identityIndex) (collectLogged raw))).run
          state.2.server.consumed
  rw [simulateQ_map, PqxdhRegistrationJointKemSourceSuffix.handler, QueryImpl.simulateQ_compose, same]

/-- Interpreting the exposed logged accept by the actual encapsulator gives the open logged accept. -/
theorem accept_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw).run state) =
      (openAccept setup codec checks identityIndex publicIdentity raw).run state := by
  simp only [PqxdhDeploymentLaterServerCommands.accept, openAccept, StateT.run_bind, simulateQ_bind,
    PqxdhRegistrationJointKemEncapsulation.lift_actual, prepare_actual, StateT.run_pure, simulateQ_pure]

/-- Under the actual private pools, at a state whose Server slot holds `seed`, the open logged preparation is the annotated logged preparation of the source. -/
theorem prepare_pool (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointFinish.State KemSK)
    (owned : state.1.1.seeds[identityIndex]? = some seed) :
    PqxdhRegistrationJointOpenBackend.run setup (openPrepare setup codec checks identityIndex raw) state =
      (PqxdhDeploymentLaterServerSource.sourcePrepare setup codec checks seed identityIndex raw).run state := by
  have opened := PqxdhRegistrationJointOpenBackend.prefix_program setup codec checks
    (simulateQ (PqxdhRegistrationJointServerPrefix.compiler identityIndex) (collectLogged raw))
    (state.1, state.2.2.server.consumed)
  rw [PqxdhRegistrationJointServerPrefix.program_source setup (serverAux setup codec checks) seed identityIndex
    (collectLogged raw) (state.1, state.2.2.server.consumed) owned] at opened
  simp only [PqxdhRegistrationJointOpenBackend.run] at opened
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
      (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        ((fun result => (((result.1.1, result.2), result.1.2), state.2)) <$>
          (simulateQ (PqxdhRegistrationJointOpenBackend.prefixImpl setup codec checks)
            (simulateQ (PqxdhRegistrationJointServerPrefix.compiler identityIndex) (collectLogged raw))).run
              state.2.2.server.consumed)).run state.1 =
    (fun result => (((result.1.1, result.2.2), result.1.2), (result.2.1, state.2))) <$>
      (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
        (serverAux setup codec checks)) (collectLogged raw)).run (state.1, state.2.2.server.consumed)
  rw [← opened, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]

/-- Under the actual private pools, at a state whose Server slot holds `seed`, the open logged accept with the Server's public identity is the logged annotated accept of the source. -/
theorem accept_pool (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointFinish.State KemSK)
    (owned : state.1.1.seeds[identityIndex]? = some seed) :
    PqxdhRegistrationJointOpenBackend.run setup
      (openAccept setup codec checks identityIndex (setup.joint.publicKeys seed) raw) state =
      (PqxdhDeploymentLaterServerSource.acceptSource setup codec checks seed identityIndex raw).run state := by
  simp only [openAccept, PqxdhDeploymentLaterServerSource.acceptSource, PqxdhRegistrationJointOpenBackend.run_bind,
    PqxdhRegistrationJointOpenBackend.native_run, StateT.run_bind]
  simp only [PqxdhRegistrationJointServerPrefix.onAux, PqxdhRegistrationJointFinish.onNative, nativeGet, localState,
    StateT.run, map_pure, pure_bind]
  rw [show PqxdhRegistrationJointOpenBackend.run setup (openPrepare setup codec checks identityIndex raw) state =
      (PqxdhDeploymentLaterServerSource.sourcePrepare setup codec checks seed identityIndex raw).run state from
    prepare_pool setup codec checks seed identityIndex raw state owned]
  rfl

/-- The logged command run under the actual encapsulator and the actual private pools, from an encoded state and a log; the result, the encoded state and the log are returned. -/
noncomputable def execute (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (state : EncodedState KemSK) (log : Log) : ProbComp (Result × (EncodedState KemSK × Log)) :=
  (fun result => (result.1.1.1, (⟨result.2, result.1.2, result.1.1.2.1⟩, result.1.1.2.2))) <$>
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
        (PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity work state.owners log
          state.shared))).run state.pool

/-- The interpreted logged run of a sequential program is the run of its first part followed by the run of the rest from the reached encoded state and log. -/
theorem execute_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (next : Result → OracleComp (Spec KemSK) Next) (state : EncodedState KemSK) (log : Log) :
    execute setup codec checks identityIndex publicIdentity (work >>= next) state log =
      (execute setup codec checks identityIndex publicIdentity work state log >>= fun result =>
        execute setup codec checks identityIndex publicIdentity (next result.1) result.2.1 result.2.2) := by
  simp only [execute, PqxdhDeploymentLaterServerCommands.run_bind, simulateQ_bind, StateT.run_bind, map_bind,
    bind_map_left]

/-- A source14 request other than a raw accept, run by both handlers through their unchanged source14 branches, has the same reply and encoded state, and both keep the log. -/
theorem generic_core (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state) :
    (fun result => (result.1.1.1, ((⟨result.2, result.1.2, result.1.1.2.1⟩ : EncodedState KemSK), result.1.1.2.2))) <$>
      (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (((fun held : PqxdhDeploymentLaterServerCommands.Local =>
            (fun result => (result.1, (result.2, held.2))) <$>
              simulateQ (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex
                (setup.joint.publicKeys seed))
                ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run held.1))
            ((encodeState setup state).owners, log)).run state.shared))).run state.pool =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        ((fun result => (result.1, (result.2, log))) <$>
          (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state) := by
  have client := PqxdhRegistrationJointServerClient.query_source setup codec checks seed identityIndex query state owned
  have opened := PqxdhRegistrationJointOpenBackend.program_run setup codec checks identityIndex
    (setup.joint.publicKeys seed)
    ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run (encodeState setup state).owners)
    ((encodeState setup state).pool, (encodeState setup state).shared)
  simp only [PqxdhRegistrationJointServerClient.execute] at client
  rw [← opened] at client
  simp only [PqxdhRegistrationJointOpenBackend.run] at client
  have rhs : (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
      ((fun result => (result.1, (result.2, log))) <$>
        (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state) =
      (fun result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × EncodedState KemSK =>
        (result.1, (result.2, log))) <$>
        ((fun result => (result.1, encodeState setup result.2)) <$>
          (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state) := by
    simp only [Functor.map_map]
  rw [rhs, ← client]
  rw [StateT.run_map, simulateQ_map, PqxdhRegistrationJointKemEncapsulation.program_actual, simulateQ_map,
    StateT.run_map]
  simp only [Functor.map_map]
  rfl

/-- A source14 request whose two handlers take their unchanged source14 branches: the interpreted logged command step equals the logged source step on the encoded state, and the log is kept. -/
theorem generic_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state)
    (branch : PqxdhDeploymentLaterServerCommands.impl setup codec checks identityIndex (setup.joint.publicKeys seed)
      (.inl query) = fun held => (fun result => (result.1, (result.2, held.2))) <$>
        simulateQ (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex
          (setup.joint.publicKeys seed)) ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run held.1))
    (sourceBranch : PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex (.inl query) =
      fun state => (fun result => (result.1, (result.2, state.2))) <$>
        (PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state.1) :
    execute setup codec checks identityIndex (setup.joint.publicKeys seed) ((Spec KemSK).query (.inl query))
      (encodeState setup state) log =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex (.inl query)).run (state, log) := by
  simp only [execute, PqxdhDeploymentLaterServerCommands.run, simulateQ_spec_query]
  rw [branch, sourceBranch]
  exact generic_core setup codec checks seed identityIndex query state log owned

/-- A raw accept: the interpreted exposed logged accept equals the logged annotated accept of the source on the encoded state, with the same logged entry appended. -/
theorem accept_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state) :
    execute setup codec checks identityIndex (setup.joint.publicKeys seed)
      ((Spec KemSK).query (.inl (.inl (.inr (.accept raw))))) (encodeState setup state) log =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex
          (.inl (.inl (.inr (.accept raw))))).run (state, log) := by
  have pooled := accept_pool setup codec checks seed identityIndex raw (state.pool, state.shared) owned.2
  simp only [PqxdhRegistrationJointOpenBackend.run] at pooled
  simp only [execute, PqxdhDeploymentLaterServerCommands.run, simulateQ_spec_query]
  rw [PqxdhDeploymentLaterServerCut.impl_accept, simulateQ_map, accept_actual, simulateQ_map, StateT.run_map]
  change _ = (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
    ((fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
      ((fun result => (result.1, { state with pool := result.2.1, shared := result.2.2 })) <$>
        (PqxdhDeploymentLaterServerSource.acceptSource setup codec checks seed identityIndex raw).run
          (state.pool, state.shared)))
  rw [← pooled]
  simp only [Functor.map_map]
  rfl

/-- The Server read: the interpreted identity-pool reveal of the Server's slot equals the source's Server read on the encoded state, and both return the log. -/
theorem later_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (read : Unit)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log) :
    execute setup codec checks identityIndex (setup.joint.publicKeys seed) ((Spec KemSK).query (.inr read))
      (encodeState setup state) log =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex (.inr read)).run (state, log) := by
  simp only [execute, PqxdhDeploymentLaterServerCommands.run, simulateQ_spec_query]
  change (fun result => (result.1.1.1, ((⟨result.2, result.1.2, result.1.1.2.1⟩ : EncodedState KemSK), result.1.1.2.2))) <$>
      (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          ((fun seed => (((seed, log), ((encodeState setup state).owners, log)), state.shared)) <$>
            ((PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query (.inl (.inl (.inr (.reveal identityIndex)))) :
              OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Option IdentitySeed))))).run
        state.pool =
    (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
      ((fun result => ((result.1, log), (result.2, log))) <$>
        ((fun result => (result.1, { state with pool := result.2.1, shared := result.2.2 })) <$>
          ((fun result => (result.1, (result.2, state.shared))) <$>
            (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem (.inl (.inr (.reveal identityIndex)))).run
              state.pool)))
  rw [simulateQ_map, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  simp only [PqxdhRegistrationJointKemEncapsulation.actual, simulateQ_spec_query, Functor.map_map]
  rfl

/-- Every logged-source request, at a state that satisfies the Server-slot and owner invariant, has the same reply, encoded state and log under the interpreted logged command compiler as under the logged annotated source. -/
theorem query_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state) :
    execute setup codec checks identityIndex (setup.joint.publicKeys seed) ((Spec KemSK).query query)
      (encodeState setup state) log =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex query).run (state, log) := by
  rcases query with ((coin | request) | read) | later
  · exact generic_step setup codec checks seed identityIndex _ state log owned rfl rfl
  · cases request
    case accept raw => exact accept_step setup codec checks seed identityIndex raw state log owned
    all_goals exact generic_step setup codec checks seed identityIndex _ state log owned rfl rfl
  · exact generic_step setup codec checks seed identityIndex _ state log owned rfl rfl
  · exact later_step setup codec checks seed identityIndex later state log

/-- Every logged-source program, from a state that satisfies the Server-slot and owner invariant, has the same result, encoded final state and final log under the interpreted logged command compiler as under the logged annotated source. -/
theorem program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (work : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (owned : PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state) :
    execute setup codec checks identityIndex (setup.joint.publicKeys seed) work (encodeState setup state) log =
      (fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$>
        (simulateQ (PqxdhDeploymentLaterServerSource.source setup codec checks seed identityIndex) work).run
          (state, log) := by
  induction work using OracleComp.inductionOn generalizing state log with
  | pure value =>
    simp [execute, PqxdhDeploymentLaterServerCommands.run, encodeState]
  | query_bind query next ih =>
    rw [execute_bind, query_source setup codec checks seed identityIndex query state log owned, bind_map_left]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    exact ih middle.1 middle.2.1 middle.2.2
      (PqxdhDeploymentLaterServerSource.query_owned setup codec checks seed identityIndex query state log middle owned
        reached)

/-- The logged monitored commands after the actual initializer: `KemInitialization.commands` with the logged command program, from no owner and the empty log. -/
noncomputable def commands (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (client : OracleComp (Spec KemSK) Result)
    (joint : PqxdhDynamicIdentityPool.SourceState) (runtime : A) (selected : Nat)
    (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) :
    ProbComp (Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A) :=
  PqxdhRegistrationJointKemInitialization.finish created runtime <$>
    (Prod.map id (PqxdhDynamicKemJointSource.project pairs) <$>
      (((simulateQ (PqxdhDynamicKemJointSource.normal setup.baseImpl setup.joint setup.kem selected pairs)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (PqxdhDeploymentLaterServerCommands.commands setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity client [] [] (PqxdhRegistrationJointInitializedAccept.initial created)))).run).run
              (joint, PqxdhDynamicKemRouter.empty)))

/-- The bounded reservation after the actual initializer, with the logged commands. -/
noncomputable def reserved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (client : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (count : Nat) (selected : Fin (count + 1)) :
    ProbComp (Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A) := do
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created => do
    let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
    let others ← PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
    commands setup codec checks created client born.2.1.1 born.2.2 selected.val
      (List.ofFn (selected.insertNth chosen others))

/-- The selected-key-first game of the logged source: the selected key pair is drawn first, then the actual initializer, the other reserved pairs and the logged commands. -/
noncomputable def selectedFirst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (client : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (count : Nat) (selected : Fin (count + 1)) :
    ProbComp (Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A) := do
  let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run state
  match born.1 with
  | none => pure (none, born.2)
  | some created => do
    let others ← PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
    commands setup codec checks created client born.2.1.1 born.2.2 selected.val
      (List.ofFn (selected.insertNth chosen others))

/-- Encoding a logged initialized outcome and forgetting its log factors through the encoded final state. -/
theorem encode_factor (setup : Setup baseSpec KemSK) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (runtime : A) (work : ProbComp (Result × (PqxdhRegistrationJointSchedule.State KemSK × Log))) :
    (fun result => (result.1.map fun outcome => PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1,
        result.2)) <$>
      ((fun result => (some ((created, result.1, result.2.1), result.2.2), (result.2.1.pool, runtime))) <$> work) =
      (fun result : Result × (EncodedState KemSK × Log) =>
        ((some (created, result.1, result.2.1) : Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result)),
          (result.2.1.pool, runtime))) <$>
        ((fun result => (result.1, (encodeState setup result.2.1, result.2.2))) <$> work) := by
  simp only [Functor.map_map]
  rfl

/-- The interpreted logged run from the initialized Server, with its outcome installed, is the reinstalled logged command program under the actual KEM pool. -/
theorem execute_commands (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (client : OracleComp (Spec KemSK) Result) (pool : Pool KemSK) (runtime : A)
    (empty : pool.2 = PqxdhLiveKemBirth.empty) :
    (fun result : Result × (EncodedState KemSK × Log) =>
        ((some (created, result.1, result.2.1) : Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result)),
          (result.2.1.pool, runtime))) <$>
      execute setup codec checks identityIndex publicIdentity client
        (PqxdhRegistrationJointInitializedSchedule.initial pool created) [] =
      (fun result => PqxdhRegistrationJointKemInitialization.finish created runtime (some result.1, result.2)) <$>
        (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
          (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
            (PqxdhDeploymentLaterServerCommands.commands setup codec checks identityIndex
              publicIdentity client [] [] (PqxdhRegistrationJointInitializedAccept.initial created)))).run
          (pool.1, PqxdhLiveKemBirth.empty) := by
  rw [← empty]
  simp only [execute, PqxdhDeploymentLaterServerCommands.commands, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

set_option linter.deprecated false in
/-- The logged initialized source, with the log forgotten and the outcome encoded, has the distribution of the bounded reservation with the logged commands. The constructor's empty KEM pool, the Server-slot invariant and the creation cap are derived, not assumed. -/
theorem initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (client : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (empty : state.1.2 = PqxdhLiveKemBirth.empty)
    (count : Nat) (selected : Fin (count + 1))
    (bounded : client.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some (.inl 1)) (count + 1)) :
    𝒮[(fun result => (result.1.map fun outcome => PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1,
        result.2)) <$>
      (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied client).run state] =
      𝒮[reserved setup codec checks ensureInit supplied client state count selected] := by
  simp only [PqxdhDeploymentLaterServerSource.initialized, reserved, StateT.run, map_bind]
  have born := PqxdhRegistrationJointServerBirth.client_source (P := Unit) setup ensureInit setup.serverKeyId supplied
    state
  simp only [StateT.run] at born
  rw [born, bind_map_left]
  apply evalSPMF_bind_congr
  rintro ⟨(_ | created), after⟩ supported
  · simp
  · dsimp only [Option.map_some]
    have constructor := PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit setup.serverKeyId
      supplied state after created supported
    have emptyAfter : after.1.2 = PqxdhLiveKemBirth.empty := by rw [constructor.1]; exact empty
    have owned : PqxdhRegistrationJointServerSchedule.Owned created.seed created.server.server.metadata.identityIndex
        (PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared) :=
      ⟨by simp [PqxdhRegistrationJointSchedule.Invariant, PqxdhRegistrationJointSchedule.initial],
        PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit setup.serverKeyId supplied state after
          created supported⟩
    have published := PqxdhRegistrationJointInitializedAccept.source_public setup.joint ensureInit setup.serverKeyId
      supplied state after created supported
    have same := program_source setup codec checks created.seed created.server.server.metadata.identityIndex client
      (PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared) [] owned
    simp only [StateT.run] at same
    have source := PqxdhDeploymentLaterServerReserve.selected_source setup codec checks
      created.server.server.metadata.identityIndex (setup.joint.publicKeys created.seed) client count bounded [] []
      (PqxdhRegistrationJointInitializedAccept.initial (PqxdhRegistrationJointServerBirth.encode created)) after.1.1
      selected
    have mapped := congrArg (fun distribution =>
      PqxdhRegistrationJointKemInitialization.finish (PqxdhRegistrationJointServerBirth.encode created) after.2 <$>
        distribution) source
    simp only [← evalSPMF_map, Functor.map_map] at mapped
    rw [encode_factor, ← same, ← published]
    rw [show PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared =
        PqxdhRegistrationJointSchedule.initial after.1 (PqxdhRegistrationSchedule.initial created).shared from rfl,
      ← PqxdhRegistrationJointInitializedSchedule.initial_encode setup after.1 created]
    rw [execute_commands setup codec checks (PqxdhRegistrationJointServerBirth.encode created)
      created.server.server.metadata.identityIndex created.publicIdentity client after.1 after.2 emptyAfter]
    rw [published]
    refine mapped.trans ?_
    simp only [commands, map_bind]
    rw [show (PqxdhRegistrationJointServerBirth.encode created).server.server.metadata.identityIndex =
        created.server.server.metadata.identityIndex from rfl,
      show (PqxdhRegistrationJointServerBirth.encode created).publicIdentity = created.publicIdentity from rfl, published]

set_option linter.deprecated false in
/-- The selected key pair can be drawn before the actual initializer: a failed initializer only discards a lossless extra draw. -/
theorem constructor_order (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (client : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (count : Nat) (selected : Fin (count + 1)) :
    𝒮[reserved setup codec checks ensureInit supplied client state count selected] =
      𝒮[selectedFirst setup codec checks ensureInit supplied client state count selected] := by
  rw [selectedFirst, ← PqxdhSecretInputKdf.evalSPMF_sample_comm_vcvioLegacy]
  unfold reserved
  apply evalSPMF_bind_congr'
  rintro ⟨(_ | created), after⟩
  · exact (OracleComp.ProgramLogic.Relational.evalSPMF_bind_const_of_no_failure _ _).symm
  · rfl

set_option linter.deprecated false in
/-- The logged initialized source, with the log forgotten and the outcome encoded, has the distribution of the selected-first game of the logged source: the logged counterpart of `KemInitialization.actual_source_first`. -/
theorem actual_source_first (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (client : OracleComp (Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (empty : state.1.2 = PqxdhLiveKemBirth.empty)
    (count : Nat) (selected : Fin (count + 1))
    (bounded : client.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some (.inl 1)) (count + 1)) :
    𝒮[(fun result => (result.1.map fun outcome => PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1,
        result.2)) <$>
      (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied client).run state] =
      𝒮[selectedFirst setup codec checks ensureInit supplied client state count selected] :=
  (initialized setup codec checks ensureInit supplied client state empty count selected bounded).trans
    (constructor_order setup codec checks ensureInit supplied client state count selected)

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.prepare_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.prepare_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.accept_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.accept_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.prepare_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.prepare_pool

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.accept_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.accept_pool

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.execute_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.execute_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.generic_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.generic_core

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.generic_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.generic_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.accept_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.accept_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.later_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.later_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.encode_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.encode_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.execute_commands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.execute_commands

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.initialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.constructor_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.constructor_order

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.actual_source_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized.actual_source_first
