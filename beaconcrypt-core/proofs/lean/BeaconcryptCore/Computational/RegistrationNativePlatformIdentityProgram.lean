-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication

/-! Opaque generated Ed credentials and ordinary external platform randomness use separate branches of one free request language. External allocator/writer sampling retains its complete P state without charging native World counters; native signing/hash/DH work retains its original counted interpreter. This additive language does not assert whole-runtime security or identify the old pure-writer profile with the selected runtime. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativeIdentitySourceSimulation (NewState OldState view)
variable {n : Nat} {ι KemSK Auxiliary Platform Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Spec (n : Nat) (KemSK : Type) := unifSpec + RegistrationNativeIdentityFrontend.Trusted n KemSK
abbrev OriginalSpec (n : Nat) (KemSK : Type) := unifSpec + RegistrationNativeBeaconFrontend.Trusted n KemSK
abbrev M (n : Nat) (KemSK Auxiliary Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (RegistrationNativeIdentityFrontend.State source) (StateT (RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (StateT Platform (OracleComp (Spec n KemSK))))
abbrev Original (n : Nat) (KemSK Auxiliary Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (RegistrationNativeBeaconFrontend.State source) (StateT (RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (StateT Platform (OracleComp (OriginalSpec n KemSK))))

def nativeLift : QueryImpl (RegistrationNativeIdentityFrontend.Trusted n KemSK) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inr query)
def originalLift : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (OracleComp (OriginalSpec n KemSK)) :=
  fun query => (OriginalSpec n KemSK).query (.inr query)
def externalLift : QueryImpl unifSpec (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inl query)
def externalOriginalLift : QueryImpl unifSpec (OracleComp (OriginalSpec n KemSK)) :=
  fun query => (OriginalSpec n KemSK).query (.inl query)

/-- Keep the original opaque-credential native tree unchanged, adding only an external platform coordinate. -/
def native (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value) : M n KemSK Auxiliary Platform source Value :=
  fun owners env platform =>
    (fun result => (result, platform)) <$>
      simulateQ (nativeLift (n := n) (KemSK := KemSK)) ((work.run owners).run env)

def original (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) : Original n KemSK Auxiliary Platform source Value :=
  fun owners env platform =>
    (fun result => (result, platform)) <$>
      simulateQ (originalLift (n := n) (KemSK := KemSK)) ((work.run owners).run env)

/-- External allocation/writer effects use their actual adaptive P program and never masquerade as native counted World requests. -/
def external (work : StateT Platform ProbComp Value) : M n KemSK Auxiliary Platform source Value :=
  fun owners env platform =>
    (fun result => (((result.1, owners), env), result.2)) <$>
      simulateQ (externalLift (n := n) (KemSK := KemSK)) (work.run platform)

def externalOriginal (work : StateT Platform ProbComp Value) : Original n KemSK Auxiliary Platform source Value :=
  fun owners env platform =>
    (fun result => (((result.1, owners), env), result.2)) <$>
      simulateQ (externalOriginalLift (n := n) (KemSK := KemSK)) (work.run platform)

noncomputable def implementation (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (Spec n KemSK) (StateT (RegistrationNativeIdentityWorld.State n KemSK) ProbComp)
  | .inl query => StateT.lift (unifSpec.query query)
  | .inr query => RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created query

noncomputable def originalImplementation (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (OriginalSpec n KemSK) (StateT (RegistrationNativeIdentityWorld.Context n KemSK) ProbComp)
  | .inl query => StateT.lift (unifSpec.query query)
  | .inr query => RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created query

noncomputable def runNew (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK Auxiliary Platform source Value) (before : NewState n KemSK Auxiliary source × Platform) :
    ProbComp (Value × (NewState n KemSK Auxiliary source × Platform)) :=
  (fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.2), result.1.2))) <$>
    (simulateQ (implementation (source := source) setup checks representation created)
      (((work.run before.1.1.1).run before.1.1.2).run before.2)).run before.1.2

noncomputable def runOld (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : Original n KemSK Auxiliary Platform source Value) (before : OldState n KemSK Auxiliary source × Platform) :
    ProbComp (Value × (OldState n KemSK Auxiliary source × Platform)) :=
  (fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.2), result.1.2))) <$>
    (simulateQ (originalImplementation (source := source) setup checks representation created)
      (((work.run before.1.1.1).run before.1.1.2).run before.2)).run before.1.2

def project (seeds : List IdentitySeed) (before : NewState n KemSK Auxiliary source × Platform) :
    OldState n KemSK Auxiliary source × Platform := (view seeds before.1, before.2)

def Related (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed) (next : M n KemSK Auxiliary Platform source Value) (actual : Original n KemSK Auxiliary Platform source Value) : Prop :=
  ∀ before, before.1.2.identities.seeds = seeds →
    Prod.map id (project seeds) <$> runNew setup checks representation created next before =
      runOld setup checks representation created actual (project seeds before)

def Keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK Auxiliary Platform source Value) : Prop :=
  ∀ before result, result ∈ support (runNew setup checks representation created work before) →
    result.2.1.2.identities.seeds = before.1.2.identities.seeds

private theorem map_apply {State A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT State m A) (before : State) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

/-- Native subtrees retain their exact counted World and add no external-state effect. -/
theorem native_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value) (before : NewState n KemSK Auxiliary source × Platform) :
    runNew setup checks representation created (native work) before =
      (fun result => (result.1, (result.2, before.2))) <$>
        RegistrationNativeIdentitySourceSimulation.runNew setup checks representation created work before.1 := by
  simp only [runNew, native, StateT.run, simulateQ_map]
  have composite : implementation (source := source) setup checks representation created ∘ₛ
      (nativeLift (n := n) (KemSK := KemSK)) =
      RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created := by
    funext query
    simp only [QueryImpl.apply_compose, nativeLift, simulateQ_spec_query, implementation]
  rw [← QueryImpl.simulateQ_compose, composite]
  simp only [map_apply, RegistrationNativeIdentitySourceSimulation.runNew, Functor.map_map, Prod.map, id_eq]
  rfl

theorem original_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) (before : OldState n KemSK Auxiliary source × Platform) :
    runOld setup checks representation created (original work) before =
      (fun result => (result.1, (result.2, before.2))) <$>
        RegistrationNativeIdentitySourceSimulation.runOld setup checks representation created work before.1 := by
  simp only [runOld, original, StateT.run, simulateQ_map]
  have composite : originalImplementation (source := source) setup checks representation created ∘ₛ
      (originalLift (n := n) (KemSK := KemSK)) =
      RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created := by
    funext query
    simp only [QueryImpl.apply_compose, originalLift, simulateQ_spec_query, originalImplementation]
  rw [← QueryImpl.simulateQ_compose, composite]
  simp only [map_apply, RegistrationNativeIdentitySourceSimulation.runOld, Functor.map_map, Prod.map, id_eq]
  rfl

/-- Existing actual native per-leaf correspondence is lifted without any writer-purity or whole-controller premise. -/
theorem native_related (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed)
    (next : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (actual : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value)
    (law : RegistrationNativeIdentitySourceSimulation.Related setup checks representation created seeds next actual) :
    Related setup checks representation created seeds (native (Platform := Platform) next) (original actual) := by
  intro before prior
  rw [native_run, original_run, Functor.map_map]
  have same := congrArg (fun distribution => (fun result => (result.1, (result.2, before.2))) <$> distribution) (law before.1 prior)
  simpa only [Functor.map_map, Prod.map, id_eq, project] using same

/-- The native prefix preservation receipt retains all generated opaque rows through this lifting. -/
theorem native_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (law : RegistrationNativeIdentitySourceSimulation.Keeps setup checks representation created work) :
    Keeps setup checks representation created (native (Platform := Platform) work) := by
  intro before result supported
  rw [native_run, support_map] at supported
  obtain ⟨middle, reached, same⟩ := supported
  cases same
  exact law before.1 middle reached

private theorem lift_probability {State : Type} (work : ProbComp Value) (before : State) :
    (simulateQ (fun query => StateT.lift (unifSpec.query query : ProbComp _) : QueryImpl unifSpec (StateT State ProbComp)) work).run before =
      (fun value => (value, before)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_lift,
      bind_pure_comp, bind_map_left, ih, map_bind]

private theorem lift_probability_apply {State : Type} (work : ProbComp Value) (before : State) :
    (simulateQ (fun query => StateT.lift (unifSpec.query query : ProbComp _) : QueryImpl unifSpec (StateT State ProbComp)) work) before =
      (fun value => (value, before)) <$> work := lift_probability work before

/-- External source effects retain the entire native counted state, while sampling exactly their actual P program. -/
theorem external_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT Platform ProbComp Value) (before : NewState n KemSK Auxiliary source × Platform) :
    runNew setup checks representation created (external work) before =
      (fun result => (result.1, (before.1, result.2))) <$> work.run before.2 := by
  simp only [runNew, external, StateT.run, simulateQ_map]
  have composite : implementation (source := source) setup checks representation created ∘ₛ externalLift =
      (fun query => StateT.lift (unifSpec.query query : ProbComp _) : QueryImpl unifSpec (StateT (RegistrationNativeIdentityWorld.State n KemSK) ProbComp)) := by
    funext query
    simp only [QueryImpl.apply_compose, externalLift, simulateQ_spec_query, implementation]
  rw [← QueryImpl.simulateQ_compose, composite]
  simp only [map_apply, lift_probability_apply, Functor.map_map, Prod.map, id_eq]

/-- Original source effects have the identical external P transition and no hidden native counter mask. -/
theorem external_original_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT Platform ProbComp Value) (before : OldState n KemSK Auxiliary source × Platform) :
    runOld setup checks representation created (externalOriginal work) before =
      (fun result => (result.1, (before.1, result.2))) <$> work.run before.2 := by
  simp only [runOld, externalOriginal, StateT.run, simulateQ_map]
  have composite : originalImplementation (source := source) setup checks representation created ∘ₛ externalOriginalLift =
      (fun query => StateT.lift (unifSpec.query query : ProbComp _) : QueryImpl unifSpec (StateT (RegistrationNativeIdentityWorld.Context n KemSK) ProbComp)) := by
    funext query
    simp only [QueryImpl.apply_compose, externalOriginalLift, simulateQ_spec_query, originalImplementation]
  rw [← QueryImpl.simulateQ_compose, composite]
  simp only [map_apply, lift_probability_apply, Functor.map_map, Prod.map, id_eq]

/-- Actual external writers and allocators preserve source realization while retaining every failure and its P poststate. -/
theorem external_related (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed) (work : StateT Platform ProbComp Value) :
    Related (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
      (external work) (externalOriginal work) := by
  intro before _prior
  rw [external_run, external_original_run, Functor.map_map]
  rfl

theorem external_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT Platform ProbComp Value) :
    Keeps (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) setup checks representation created (external work) := by
  intro before result supported
  rw [external_run, support_map] at supported
  obtain ⟨middle, _reached, same⟩ := supported
  cases same
  rfl

/-- Actual stateful source sequencing retains all frontend, environment, private-table and external coordinates. -/
theorem runNew_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK Auxiliary Platform source Value) (next : Value → M n KemSK Auxiliary Platform source Next)
    (before : NewState n KemSK Auxiliary source × Platform) :
    runNew setup checks representation created (work >>= next) before = (do
      let middle ← runNew setup checks representation created work before
      runNew setup checks representation created (next middle.1) middle.2) := by
  simp only [runNew, StateT.run_bind, simulateQ_bind, bind_map_left, map_bind]

theorem runOld_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : Original n KemSK Auxiliary Platform source Value) (next : Value → Original n KemSK Auxiliary Platform source Next)
    (before : OldState n KemSK Auxiliary source × Platform) :
    runOld setup checks representation created (work >>= next) before = (do
      let middle ← runOld setup checks representation created work before
      runOld setup checks representation created (next middle.1) middle.2) := by
  simp only [runOld, StateT.run_bind, simulateQ_bind, bind_map_left, map_bind]

theorem related_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed) (value : Value) :
    Related (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) setup checks representation created seeds (pure value) (pure value) := by
  intro before _prior
  simp only [runNew, runOld, StateT.run_pure, simulateQ_pure, map_pure, Prod.map, id_eq]

theorem keeps_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (value : Value) :
    Keeps (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) setup checks representation created (pure value) := by
  intro before result supported
  simp only [runNew, StateT.run_pure, simulateQ_pure, map_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

/-- Adaptive source continuation uses the actual preceding private-row preservation receipt, including failure poststates. -/
theorem related_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed) (first : M n KemSK Auxiliary Platform source Value) (actual : Original n KemSK Auxiliary Platform source Value)
    (next : Value → M n KemSK Auxiliary Platform source Next) (oldNext : Value → Original n KemSK Auxiliary Platform source Next)
    (law : Related setup checks representation created seeds first actual) (keeps : Keeps setup checks representation created first)
    (later : ∀ value, Related setup checks representation created seeds (next value) (oldNext value)) :
    Related setup checks representation created seeds (first >>= next) (actual >>= oldNext) := by
  intro before prior
  rw [runNew_bind, runOld_bind, map_bind]
  calc
    _ = (do let middle ← runNew setup checks representation created first before
            runOld setup checks representation created (oldNext middle.1) (project seeds middle.2)) := by
      apply bind_congr_of_forall_mem_support
      intro middle supported
      exact later middle.1 middle.2 ((keeps before middle supported).trans prior)
    _ = _ := by
      rw [← law before prior]
      simp only [bind_map_left, Prod.map, id_eq]

theorem keeps_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (first : M n KemSK Auxiliary Platform source Value) (next : Value → M n KemSK Auxiliary Platform source Next)
    (keeps : Keeps setup checks representation created first) (later : ∀ value, Keeps setup checks representation created (next value)) :
    Keeps setup checks representation created (first >>= next) := by
  intro before result supported
  rw [runNew_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (later middle.1 middle.2 result continued).trans (keeps before middle reached)

/-- A complete adaptive controller is transported from its actual per-request source laws. -/
theorem related_program {K : Type} {spec : OracleSpec K} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed) (next : QueryImpl spec (M n KemSK Auxiliary Platform source))
    (actual : QueryImpl spec (Original n KemSK Auxiliary Platform source))
    (law : ∀ query, Related setup checks representation created seeds (next query) (actual query))
    (keeps : ∀ query, Keeps setup checks representation created (next query)) (work : OracleComp spec Value) :
    Related setup checks representation created seeds (simulateQ next work) (simulateQ actual work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using related_pure setup checks representation created seeds value
  | query_bind query following ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact related_bind setup checks representation created seeds _ _ _ _ (law query) (keeps query) ih

theorem keeps_program {K : Type} {spec : OracleSpec K} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (next : QueryImpl spec (M n KemSK Auxiliary Platform source)) (keeps : ∀ query, Keeps setup checks representation created (next query))
    (work : OracleComp spec Value) : Keeps setup checks representation created (simulateQ next work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using keeps_pure setup checks representation created value
  | query_bind query following ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact keeps_bind setup checks representation created _ _ (keeps query) ih

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.native_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.original_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.original_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.native_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.native_related

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.native_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.native_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.external_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.external_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.external_original_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.external_original_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.external_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.external_related

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.external_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.external_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.runNew_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.runNew_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.runOld_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.runOld_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.related_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.related_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.keeps_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.keeps_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.related_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.related_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.keeps_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.keeps_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.related_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.related_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.keeps_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram.keeps_program
