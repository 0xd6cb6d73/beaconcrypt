-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityRealization

/-! Source simulation for native operations that use existing indexed identities. Both executions retain the complete mutable owner roster, environment and native context. The fixed seed prefix is interpreter-private, and its preservation is proved from actual source operations before binding their continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value Other : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem state_bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem state_lift_apply {m : Type → Type} [Monad m] {S A : Type}
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (do let value ← work; pure (value, before)) := rfl

private theorem state_pure_apply {m : Type → Type} [Monad m] {S A : Type}
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem state_map_apply {m : Type → Type} [Monad m] [LawfulMonad m] {S A B : Type}
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = (fun result => (change result.1, result.2)) <$> work before := by
  change (change <$> work).run before = _
  rw [StateT.run_map]
  rfl

abbrev NewState (n : Nat) (KemSK Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  (RegistrationNativeIdentityFrontend.State source × EnvState Auxiliary) × RegistrationNativeIdentityWorld.State n KemSK

abbrev OldState (n : Nat) (KemSK Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  (RegistrationNativeBeaconFrontend.State source × EnvState Auxiliary) × RegistrationNativeIdentityWorld.Context n KemSK

def view (seeds : List IdentitySeed) (before : NewState n KemSK Auxiliary source) : OldState n KemSK Auxiliary source :=
  ((RegistrationNativeIdentityRealization.owners ⟨seeds, []⟩ before.1.1, before.1.2), before.2.context)

noncomputable def runNew (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (before : NewState n KemSK Auxiliary source) : ProbComp (Value × NewState n KemSK Auxiliary source) :=
  (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
    (simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created)
      ((work.run before.1.1).run before.1.2)).run before.2

noncomputable def runOld (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value)
    (before : OldState n KemSK Auxiliary source) : ProbComp (Value × OldState n KemSK Auxiliary source) :=
  (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
    (simulateQ (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created)
      ((work.run before.1.1).run before.1.2)).run before.2

def Related (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List IdentitySeed)
    (next : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (original : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) : Prop :=
  ∀ before, before.2.identities.seeds = seeds →
    Prod.map id (view seeds) <$> runNew setup checks representation created next before =
      runOld setup checks representation created original (view seeds before)

def Keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value) : Prop :=
  ∀ before result, result ∈ support (runNew setup checks representation created work before) →
    result.2.2.identities.seeds = before.2.identities.seeds

theorem runNew_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (next : Value → RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Other)
    (before : NewState n KemSK Auxiliary source) :
    runNew setup checks representation created (work >>= next) before =
      (do let reached ← runNew setup checks representation created work before
          runNew setup checks representation created (next reached.1) reached.2) := by
  simp only [runNew, StateT.run_bind, simulateQ_bind, bind_map_left, map_bind]

theorem runOld_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value)
    (next : Value → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Other)
    (before : OldState n KemSK Auxiliary source) :
    runOld setup checks representation created (work >>= next) before =
      (do let reached ← runOld setup checks representation created work before
          runOld setup checks representation created (next reached.1) reached.2) := by
  simp only [runOld, StateT.run_bind, simulateQ_bind, bind_map_left, map_bind]

/-- Sequencing source-related operations transports the private-prefix fact from the actual reached first operation. -/
theorem related_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List IdentitySeed)
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (original : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value)
    (next : Value → RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Other)
    (oldNext : Value → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Other)
    (first : Related setup checks representation created seeds work original)
    (keeps : Keeps setup checks representation created work)
    (later : ∀ value, Related setup checks representation created seeds (next value) (oldNext value)) :
    Related setup checks representation created seeds (work >>= next) (original >>= oldNext) := by
  intro before prior
  rw [runNew_bind, runOld_bind, map_bind]
  calc
    _ = (do let reached ← runNew setup checks representation created work before
            runOld setup checks representation created (oldNext reached.1) (view seeds reached.2)) := by
      apply bind_congr_of_forall_mem_support
      intro reached supported
      exact later reached.1 reached.2 ((keeps before reached supported).trans prior)
    _ = _ := by
      rw [← first before prior]
      simp only [bind_map_left, Prod.map_def, id_eq]

/-- Prefix preservation is compositional on every supported actual source outcome. -/
theorem keeps_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (next : Value → RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Other)
    (first : Keeps setup checks representation created work)
    (later : ∀ value, Keeps setup checks representation created (next value)) :
    Keeps setup checks representation created (work >>= next) := by
  intro before result supported
  rw [runNew_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (later middle.1 middle.2 result continued).trans (first before middle reached)

theorem related_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List IdentitySeed) (value : Value) :
    Related (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
      (pure value) (pure value) := by
  intro before _prior
  simp only [runNew, runOld, StateT.run_pure, simulateQ_pure, map_pure, Prod.map_def, id_eq]

theorem keeps_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (value : Value) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created (pure value) := by
  intro before result supported
  simp only [runNew, StateT.run_pure, simulateQ_pure, map_pure,
    mem_support_pure_iff] at supported
  cases supported
  rfl

noncomputable def liftAmbient
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK)) Value) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value :=
  StateT.lift fun env => simulateQ RegistrationNativeIdentityFrontend.ambientLift (work.run env)

theorem runNew_lift (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK)) Value)
    (before : NewState n KemSK Auxiliary source) :
    runNew setup checks representation created (liftAmbient work) before =
      (fun result => (result.1.1, ((before.1.1, result.1.2),
        (⟨result.2, before.2.identities⟩ : RegistrationNativeIdentityWorld.State n KemSK)))) <$>
        (simulateQ (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created)
          (work.run before.1.2)).run before.2.context := by
  have law := congrArg (fun evaluated =>
    (fun (result : (Value × EnvState Auxiliary) × RegistrationNativeIdentityWorld.State n KemSK) =>
      (result.1.1, ((before.1.1, result.1.2), result.2))) <$> evaluated)
    (RegistrationNativeIdentitySourceFrame.ambient_program (source := source) setup checks representation created (work.run before.1.2) before.2)
  simp only [runNew, liftAmbient, bind_pure_comp,
    simulateQ_map, Functor.map_map, StateT.run, state_bind_apply, state_lift_apply,
    state_pure_apply, state_map_apply, ] at law ⊢
  exact law

theorem related_lift (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List IdentitySeed)
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK)) Value) :
    Related (source := source) setup checks representation created seeds (liftAmbient work) (StateT.lift work) := by
  intro before _prior
  rw [runNew_lift]
  simp only [runOld, StateT.run_lift, StateT.run_map, bind_pure_comp, simulateQ_map,
    Functor.map_map, view, Prod.map_def, id_eq]

theorem keeps_lift (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK)) Value) :
    Keeps (source := source) setup checks representation created (liftAmbient work) := by
  intro before result supported
  rw [runNew_lift, support_map] at supported
  obtain ⟨middle, _reached, returned⟩ := supported
  cases returned
  rfl

theorem related_program {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List IdentitySeed)
    (next : QueryImpl spec (RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source))
    (original : QueryImpl spec (RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary))
    (first : ∀ query, Related setup checks representation created seeds (next query) (original query))
    (keeps : ∀ query, Keeps setup checks representation created (next query))
    (work : OracleComp spec Value) :
    Related setup checks representation created seeds (simulateQ next work) (simulateQ original work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using related_pure setup checks representation created seeds value
  | query_bind query rest ih =>
      rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query]
      exact related_bind setup checks representation created seeds _ _ _ _ (first query) (keeps query) ih

theorem keeps_program {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (next : QueryImpl spec (RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source))
    (keeps : ∀ query, Keeps setup checks representation created (next query))
    (work : OracleComp spec Value) : Keeps setup checks representation created (simulateQ next work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using keeps_pure setup checks representation created value
  | query_bind query rest ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact keeps_bind setup checks representation created _ _ (keeps query) ih

theorem related_modify (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List IdentitySeed)
    (next : RegistrationNativeIdentityFrontend.State source → RegistrationNativeIdentityFrontend.State source)
    (original : RegistrationNativeBeaconFrontend.State source → RegistrationNativeBeaconFrontend.State source)
    (law : ∀ current, RegistrationNativeIdentityRealization.owners ⟨seeds, []⟩ (next current) =
      original (RegistrationNativeIdentityRealization.owners ⟨seeds, []⟩ current)) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds (modify next) (modify original) := by
  intro before _prior
  simp only [runNew, runOld, StateT.run_modify, StateT.run_pure, simulateQ_pure,
    map_pure, Prod.map_def, id_eq, view, law]

theorem keeps_modify (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (next : RegistrationNativeIdentityFrontend.State source → RegistrationNativeIdentityFrontend.State source) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (modify next) := by
  intro before result supported
  simp only [runNew, StateT.run_modify, StateT.run_pure, simulateQ_pure,
    map_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.runNew_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.runNew_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.runOld_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.runOld_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.related_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.related_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.keeps_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.keeps_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.related_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.related_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.keeps_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.keeps_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.runNew_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.runNew_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.related_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.related_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.keeps_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.keeps_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.related_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.related_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.keeps_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.keeps_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.related_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.related_modify
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.keeps_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation.keeps_modify
