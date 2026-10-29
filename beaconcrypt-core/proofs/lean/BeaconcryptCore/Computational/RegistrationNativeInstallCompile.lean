-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallTrace
import BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource

/-! Actual current-environment publication preserves the complete original Word chronology. Every supported compiled material result has the same raw material result and trace, including all failures and every original descriptor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallCompile
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativePublicFrontend (Spec)
abbrev PublicSpec (n : Nat) := RegistrationNativePairedServerService.PublicSpec n
open RegistrationNativeG2Trace (State handler begin finish)
open RegistrationNativePairedMaterialSource (nativeLift)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {KemSK Value : Type}

def effects : QueryImpl (EnvEffects n) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inl (.inr (.inl (.inr (.inr query)))))

noncomputable def service (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (PublicSpec n) (StateT Environment (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)))
  | .inl message => StateT.lift (RegistrationServerOpenReferenceCompiler.demand message)
  | .inr common => RegistrationNativeCommonCompiler.common RegistrationBeaconReferenceCompiler.effect source writer sign common

noncomputable def compile (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (PublicSpec n) Value) (before : Environment) : OracleComp (Spec n KemSK) (Value × Environment) :=
  simulateQ (RegistrationNativePublicFrontend.liftLocal false)
    ((simulateQ (service source writer sign) work).run before)

def step (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (reply : (RegistrationNativePublicFrontend.Spec n KemSK).Range query) (before : State) : State :=
  finish query reply (begin query before)

private theorem effects_step (query : (EnvEffects n).Domain) (reply : (EnvEffects n).Range query)
    (before : State) (quiet : ∀ role, ¬ InstallEnv role query) :
    step (KemSK := KemSK) (.inl (.inr (.inl (.inr (.inr query))))) reply before = before := by
  cases query with
  | inl coin => cases before; simp [step, begin, finish]
  | inr capability => cases capability with
    | installServer keyId binding kernel => exact False.elim (quiet .server rfl)
    | installBeacon owner shell kernel => exact False.elim (quiet .beacon rfl)
    | _ => cases before; simp [step, begin, finish]

/-- Actual publication effects with zero role bills retain every coordinate of the paired monitor. -/
theorem effects_source (work : OracleComp (EnvEffects n) Value)
    (bounded : ∀ role, work.IsQueryBoundP (InstallEnv role) 0) (before : State) :
    (simulateQ handler (simulateQ (effects (KemSK := KemSK)) work)).run before =
      (fun value => (value, before)) <$> simulateQ effects work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      have head := fun role => (isQueryBoundP_query_bind_iff _ _ _ _).mp (bounded role)
      have quiet : ∀ role, ¬ InstallEnv role query := fun role => (head role).1.resolve_right (by omega)
      simp only [simulateQ_bind, simulateQ_spec_query, effects]
      rw [StateT.run_bind]
      simp only [handler, StateT.run, bind_map_left, map_bind]
      apply bind_congr
      intro reply
      rw [show finish _ _ (begin _ before) = before from effects_step query reply before quiet]
      exact ih reply (fun role => by simpa only [Nat.zero_sub, ite_self] using (head role).2 reply) before

variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)

private theorem publication_run (query : RegistrationBoundPublication.Spec.Domain) (env : Environment) :
    compile (n := n) (KemSK := KemSK) source writer sign
      (((PublicSpec n).query (.inr (.inl query))) : OracleComp (PublicSpec n) _) env =
      (fun result => (result.1, { env with receipts := result.2 })) <$>
        simulateQ effects ((RegistrationBoundSourceCompiler.compiler source writer sign query).run env.receipts) := by
  simp only [compile, simulateQ_spec_query, service,
    RegistrationNativeCommonCompiler.common, RegistrationNativeCommonCompiler.publication,
    StateT.run, simulateQ_map, ← QueryImpl.simulateQ_compose]
  rfl

/-- The actual inlined publication keeps the full monitor while appending its literal current-environment receipts. -/
theorem publication_source (query : RegistrationBoundPublication.Spec.Domain) (env : Environment) (before : State) :
    (simulateQ handler (compile (KemSK := KemSK) source writer sign
      (((PublicSpec n).query (.inr (.inl query))) : OracleComp (PublicSpec n) _) env)).run before =
      (fun value => (value, before)) <$> compile (KemSK := KemSK) source writer sign
        (((PublicSpec n).query (.inr (.inl query))) : OracleComp (PublicSpec n) _) env := by
  rw [publication_run]
  simp only [simulateQ_map, StateT.run_map]
  rw [effects_source _ (fun role => RegistrationNativeSecretWordAtomInstallCompiler.publication_free role source writer sign query env.receipts)]
  simp only [Functor.map_map]

private theorem demand_run (message : RegistrationNativeRelatedFamily.Message) (env : Environment) :
    compile (n := n) (KemSK := KemSK) source writer sign
      (((PublicSpec n).query (.inl message)) : OracleComp (PublicSpec n) _) env =
      (fun reply => (reply, env)) <$> nativeLift (.inl message) := by
  simp only [compile, simulateQ_spec_query, service,
    StateT.run_lift, bind_pure_comp, simulateQ_map, RegistrationServerOpenReferenceCompiler.demand,
    RegistrationNativePublicFrontend.liftLocal, nativeLift, RegistrationNativePairedMaterialSource.nativeLift]

private theorem effect_run (query : (EnvEffects n).Domain) (env : Environment) :
    compile (KemSK := KemSK) source writer sign
      (((PublicSpec n).query (.inr (.inr query))) : OracleComp (PublicSpec n) _) env =
      (fun reply => (reply, env)) <$> nativeLift (.inr (.inr query)) := by
  simp only [compile, simulateQ_spec_query, service,
    RegistrationNativeCommonCompiler.common, StateT.run_lift, bind_pure_comp,
    simulateQ_map, RegistrationBeaconReferenceCompiler.effect, RegistrationNativePublicFrontend.liftLocal, nativeLift, RegistrationNativePairedMaterialSource.nativeLift]

/-- Every actual compiled material callback has the same supported paired-monitor result as its original raw callback. -/
theorem query_support (query : (PublicSpec n).Domain) (env : Environment) (before : State)
    (result : ((PublicSpec n).Range query × Environment) × State)
    (supported : result ∈ support ((simulateQ handler (compile (KemSK := KemSK) source writer sign
      (((PublicSpec n).query query) : OracleComp (PublicSpec n) _) env)).run before)) :
    (result.1.1, result.2) ∈ support ((simulateQ handler (nativeLift (KemSK := KemSK) query)).run before) := by
  cases query with
  | inl message =>
      rw [demand_run, simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨reached, actual, rfl⟩ := supported
      exact actual
  | inr common => cases common with
    | inr query =>
        rw [effect_run, simulateQ_map, StateT.run_map, support_map] at supported
        obtain ⟨reached, actual, rfl⟩ := supported
        exact actual
    | inl publication =>
        rw [publication_source, support_map] at supported
        obtain ⟨reached, _actual, rfl⟩ := supported
        simp only [nativeLift, RegistrationNativePairedMaterialSource.nativeLift,
          simulateQ_spec_query, handler, StateT.run, support_map]
        refine ⟨reached.1, mem_support_query _ _, ?_⟩
        cases before
        simp [begin, finish]

private theorem compile_bind {Next : Type} (work : OracleComp (PublicSpec n) Value)
    (next : Value → OracleComp (PublicSpec n) Next) (env : Environment) :
    compile (KemSK := KemSK) source writer sign (work >>= next) env = (do
      let reached ← compile source writer sign work env
      compile source writer sign (next reached.1) reached.2) := by
  simp only [compile, simulateQ_bind, StateT.run_bind]

/-- Every complete actual compiled material execution refines its original raw paired program on the same complete chronological monitor. -/
theorem program_support (work : OracleComp (PublicSpec n) Value) (env : Environment) (before : State)
    (result : (Value × Environment) × State)
    (supported : result ∈ support ((simulateQ handler (compile (KemSK := KemSK) source writer sign work env)).run before)) :
    (result.1.1, result.2) ∈ support ((simulateQ handler (simulateQ (nativeLift (KemSK := KemSK)) work)).run before) := by
  induction work using OracleComp.inductionOn generalizing env before with
  | pure value =>
      simp only [compile, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff]
  | query_bind query next ih =>
      rw [compile_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, actual, continued⟩ := supported
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      exact ⟨(middle.1.1, middle.2), query_support source writer sign query env before middle actual,
        ih middle.1.1 middle.1.2 middle.2 continued⟩

end BeaconcryptCore.Computational.RegistrationNativeInstallCompile
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallCompile.effects_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallCompile.effects_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallCompile.publication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallCompile.publication_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallCompile.query_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallCompile.query_support
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallCompile.program_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallCompile.program_support
