-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun

/-! Original native startup uses the literal Server installation and cached ML fingerprint before returning public initialization. Its returned private native state is projected explicitly; optional ML generation and every original constructor branch remain in the free program. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaCountMap (transform)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def initialProject (before : RegistrationNativeExperiment.Initial n KemSK source) : RegistrationNativeExperiment.Initial n KemSK source :=
  ⟨before.created, before.credential, RegistrationNativeMldsaMainView.project before.state⟩

private noncomputable def initializeWorld (created : PqxdhLiveServerConstruction.Created Unit)
    (publicKey : Std.Array U8 1952#usize) : StateT (PqxdhRecordLiftWorld.State n) ProbComp CtxRomAuth.CtxDigest := do
  PqxdhRecordLiftWorld.initializeServer created
  PqxdhRecordLiftWorld.effects (.inr (.hash (PqxdhRefinement.absBytes publicKey)))

private def initialized (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (result : CtxRomAuth.CtxDigest × PqxdhRecordLiftWorld.State n) :
    RegistrationNativeExperiment.Initial n KemSK source :=
  ⟨created, credential,
    ⟨⟨created.control, ⟨⟨created.server.server.identity, created.server.server.metadata.sender⟩,
      credential.publicKey, RegistrationAuthenticationShared.digestArray result.1⟩, created.consumed, [],
      ⟨RegistrationServerRoleBackend.empty, [], [], (result.2, [])⟩⟩,
    [], PqxdhLiveKemBirth.empty, 0⟩⟩

private theorem initialize_server_stable (created : PqxdhLiveServerConstruction.Created Unit) :
    RegistrationNativeKemCounterIndependence.Stable (RegistrationNativeMldsaWorldView.project (n := n))
      (PqxdhRecordLiftWorld.initializeServer created) := by
  intro before
  cases stored : before.server <;>
    simp only [PqxdhRecordLiftWorld.initializeServer, StateT.run, stored, map_pure, Prod.map, id_eq,
      RegistrationNativeMldsaWorldView.project, RegistrationNativeKemWorldUniform.mask,
      RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
      RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]

private theorem initialize_stable (created : PqxdhLiveServerConstruction.Created Unit) (publicKey : Std.Array U8 1952#usize) :
    RegistrationNativeKemCounterIndependence.Stable (RegistrationNativeMldsaWorldView.project (n := n))
      (initializeWorld created publicKey) :=
  RegistrationNativeKemCounterIndependence.bind_stable _ _ _ (initialize_server_stable created)
    (fun _ => RegistrationNativeMldsaWorldView.effects _)

private theorem initialized_project (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (result : CtxRomAuth.CtxDigest × PqxdhRecordLiftWorld.State n) :
    initialProject (initialized (n := n) (KemSK := KemSK) created credential result) =
      initialized created credential (result.1, RegistrationNativeMldsaWorldView.project result.2) := rfl

/-- The final actual native initializer equals its literal Server installation and same-cache public-key fingerprint sequence. -/
theorem initialize_source (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (before : PqxdhRecordLiftWorld.State n) :
    (fun result => some (initialized (KemSK := KemSK) created credential result)) <$>
      (initializeWorld created credential.publicKey).run before = (do
        let result ← (RegistrationWorldServerFrontend.start created credential.publicKey RegistrationServerRoleBackend.empty).run before
        pure (match result.1 with
          | .ok (.Some native) => some ⟨created, credential,
              ⟨RegistrationServerFrontendCompiler.erase native, [], PqxdhLiveKemBirth.empty, 0⟩⟩
          | _ => none)) := by
  simp only [initializeWorld, StateT.run_bind, map_bind]
  simp only [RegistrationWorldServerFrontend.start, StateT.run, bind_assoc]
  apply bind_congr
  intro installed
  have pin := RegistrationWorldServerFrontend.initializePin_native (n := n)
    ⟨created.server.server.identity, created.server.server.metadata.sender⟩ credential.publicKey
    (PqxdhJointDhExtractFamily.empty, (⟨RegistrationServerRoleBackend.empty, [], [], (installed.2, [])⟩ :
      RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State))
  simp only [StateT.run] at pin
  rw [pin]
  simp only [StateT.run, RegistrationWorldServerCompletion.capability, bind_map_left,
    bind_pure_comp, Functor.map_map]
  rw [← bind_pure_comp]
  apply bind_congr
  intro hashed
  simp only [map_pure, initialized, RegistrationServerFrontendCompiler.erase]
  rfl

/-- Both actual initializer inputs and its returned private state obey the explicitly named accounting view. -/
theorem initialize_input (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (before : PqxdhRecordLiftWorld.State n) :
    (Option.map initialProject) <$>
        ((fun result => some (initialized (KemSK := KemSK) created credential result)) <$>
          (initializeWorld created credential.publicKey).run before) =
      (Option.map initialProject) <$>
        ((fun result => some (initialized (KemSK := KemSK) created credential result)) <$>
          (initializeWorld created credential.publicKey).run (RegistrationNativeMldsaWorldView.project before)) := by
  have same := congrArg (fun computation => (fun result => some (initialized (KemSK := KemSK) created credential result)) <$> computation)
    (initialize_stable created credential.publicKey before)
  simp only [Functor.map_map, Prod.map, id_eq, Option.map_some, initialized_project] at same ⊢
  exact same

private noncomputable def alternate (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) : OracleComp (Spec source) (Option (RegistrationNativeExperiment.Initial n KemSK source)) := do
  let constructed ← RegistrationNativeMldsaProgram.lift ((PqxdhRecordLiftWorld.sampled
    ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ())).run
      (PqxdhRecordLiftWorld.initial : PqxdhRecordLiftWorld.State n))
  match constructed.1.1 with
  | none => pure none
  | some created =>
      let generated ← (RegistrationNativeMldsaProgram.call .native .generate).run constructed.2
      match generated.1 with
      | none => pure none
      | some credential =>
          RegistrationNativeMldsaProgram.lift
            ((fun result => some (initialized created credential result)) <$>
              (initializeWorld created credential.publicKey).run generated.2)

private theorem alternate_source (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) :
    RegistrationNativeMldsaCreation.start (n := n) (source := source) setup ensureInit identityIndex serverKeyId =
      alternate setup ensureInit identityIndex serverKeyId := by
  unfold RegistrationNativeMldsaCreation.start alternate
  apply bind_congr
  intro constructed
  cases built : constructed.1.1 with
  | none => rfl
  | some created =>
      simp only
      apply bind_congr
      intro generated
      cases chosen : generated.1 with
      | none => rfl
      | some credential =>
          simp only
          have actual := congrArg (RegistrationNativeMldsaProgram.lift (source := source))
            (initialize_source (KemSK := KemSK) created credential generated.2)
          simp only [RegistrationNativeMldsaProgram.lift, simulateQ_map, simulateQ_bind, simulateQ_pure] at actual
          simp only [RegistrationNativeMldsaProgram.lift, simulateQ_map]
          apply Eq.trans ?_ actual.symm
          apply bind_congr
          intro result
          cases result.1 with
          | fail error | div => rfl
          | ok option => cases option <;> rfl

/-- The startup accounting view preserves its exact original public input. -/
theorem initial_public (before : RegistrationNativeExperiment.Initial n KemSK source) :
    (initialProject before).public = before.public := rfl

/-- Reapplying the startup view leaves the retained native state unchanged. -/
theorem initial_idempotent (before : RegistrationNativeExperiment.Initial n KemSK source) :
    initialProject (initialProject before) = initialProject before := by
  simp only [initialProject, RegistrationNativeMldsaMainView.idempotent]

private theorem initialized_advance (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (before : PqxdhRecordLiftWorld.State n) (count : Nat) :
    (Option.map initialProject) <$>
        RegistrationNativeMldsaProgram.lift (source := source)
          ((fun result => some (initialized (KemSK := KemSK) created credential result)) <$>
            (initializeWorld created credential.publicKey).run
              (RegistrationNativeMldsaCapability.advance .native before count)) =
      (Option.map initialProject) <$>
        RegistrationNativeMldsaProgram.lift (source := source)
          ((fun result => some (initialized (KemSK := KemSK) created credential result)) <$>
            (initializeWorld created credential.publicKey).run before) := by
  have first := initialize_input (KemSK := KemSK) created credential
    (RegistrationNativeMldsaCapability.advance .native before count)
  have second := initialize_input (KemSK := KemSK) created credential before
  rw [RegistrationNativeMldsaWorldView.advance] at first
  have same := congrArg (RegistrationNativeMldsaProgram.lift (source := source)) (first.trans second.symm)
  simp only [RegistrationNativeMldsaProgram.lift, simulateQ_map] at same ⊢
  exact same


/-- Normalizing the startup ML generation receipt preserves its optional initialized state and exact public input under the explicit accounting view. -/
theorem start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) :
    (Option.map initialProject) <$>
        transform (RegistrationNativeMldsaCreation.start (n := n) (source := source) setup ensureInit identityIndex serverKeyId) =
      (Option.map initialProject) <$>
        RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId := by
  rw [alternate_source]
  unfold alternate
  simp only [transform, simulateQ_bind]
  rw [← transform, RegistrationNativeMldsaCountMap.lift]
  simp only [map_bind]
  apply bind_congr
  intro constructed
  cases built : constructed.1.1 with
  | none => simp only [simulateQ_pure, map_pure]
  | some created =>
      simp only
      simp only [simulateQ_bind, RegistrationNativeMldsaProgram.call, StateT.run, bind_pure_comp,
        simulateQ_spec_query, RegistrationNativeMldsaCountMap.translation,
        bind_map_left, map_bind]
      apply bind_congr
      intro reply
      rcases reply with ⟨generated, count⟩
      cases generated with
      | none => simp only [simulateQ_pure, map_pure]
      | some credential =>
          simp only
          rw [← transform, RegistrationNativeMldsaCountMap.lift]
          exact (initialized_advance (KemSK := KemSK) created credential constructed.2 0).trans
            (initialized_advance created credential constructed.2 count).symm

end BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart.initialize_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart.initialize_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart.initialize_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart.initialize_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart.initial_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart.initial_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart.initial_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart.initial_idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountStart.start
