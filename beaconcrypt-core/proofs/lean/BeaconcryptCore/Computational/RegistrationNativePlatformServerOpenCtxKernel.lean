-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxEffects
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The OPEN accept dictionary routes every ordinary environment effect through the explicit CTX backend. Indexed generation/identity/KEM and root-reference preparation remain separate typed leaves. Physical source correspondence is required only for those reachable individual leaves; demand/publication callbacks are excluded by the actual accept syntax. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxKernel
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativePlatformCtxRunner (M Full interpret)
open RegistrationNativePlatformServerOpenCtxEffects (realize)
variable {n : Nat} {ι KemSK Extra Platform : Type} {base : OracleSpec ι}

structure Callbacks (n : Nat) (KemSK Extra Platform : Type) where
  prepare : QueryImpl RegistrationServerReferenceRoot.PrepareSpec (M (Private n KemSK Extra) Platform)
  demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (M (Private n KemSK Extra) Platform)
  publication : QueryImpl RegistrationBoundPublication.Spec (M (Private n KemSK Extra) Platform)
  indexed : QueryImpl (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK) (M (Private n KemSK Extra) Platform)

noncomputable def handler (callbacks : Callbacks n KemSK Extra Platform) :
    QueryImpl (RegistrationNativeKemReferenceCompiler.Spec n KemSK) (M (Private n KemSK Extra) Platform)
  | .inl query => callbacks.prepare query
  | .inr (.inl (.inl query)) => callbacks.demand query
  | .inr (.inl (.inr (.inl query))) => callbacks.publication query
  | .inr (.inl (.inr (.inr query))) => RegistrationNativePlatformServerOpenCtxEffects.effect query
  | .inr (.inr query) => callbacks.indexed query

structure Transport (setup : Setup base KemSK) (free : Callbacks n KemSK Extra Platform)
    (native : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra (StateT Platform ProbComp)) : Prop where
  prepare : ∀ query before,
    Prod.map id realize <$> (interpret (free.prepare query)).run before =
      (RegistrationAgreementNestedState.flatten (native.prepare query)).run (realize before)
  indexed : ∀ query before,
    Prod.map id realize <$> (interpret (free.indexed query)).run before =
      (RegistrationAgreementNestedState.flatten (RegistrationNativePlatformInterpret.state RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeKemReferenceWorld.kem setup native.other query))).run (realize before)

theorem query (setup : Setup base KemSK) (free : Callbacks n KemSK Extra Platform)
    (native : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra (StateT Platform ProbComp))
    (transport : Transport setup free native) (request : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Domain)
    (before : Full (Private n KemSK Extra) Platform)
    (allowed : ¬ RegistrationNativePlatformServerOpenServiceFree.IsService (n := n) (KemSK := KemSK) request) :
    Prod.map id realize <$> (interpret (handler free request)).run before =
      (RegistrationAgreementNestedState.flatten (RegistrationNativePlatformServerOpenKernel.handler
        RegistrationNativePlatformMldsaProgram.coins setup native request)).run (realize before) := by
  cases request with
  | inl query => exact transport.prepare query before
  | inr request => cases request with
    | inr query => exact transport.indexed query before
    | inl request => cases request with
      | inl query => exact False.elim (allowed trivial)
      | inr request => cases request with
        | inl query => exact False.elim (allowed trivial)
        | inr query => exact RegistrationNativePlatformServerOpenCtxEffects.query query before

noncomputable def extended (callbacks : Callbacks n KemSK Extra Platform) (reserve : StateT Platform ProbComp Bool) :
    QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) (M (Private n KemSK Extra) Platform)
  | .inl query => handler callbacks query
  | .inr _ => RegistrationNativePlatformCtxRunner.publicWork reserve

noncomputable def nativeExtended (setup : Setup base KemSK)
    (native : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) :
    QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) (StateT (Private n KemSK Extra) (StateT Platform ProbComp))
  | .inl query => RegistrationNativePlatformServerOpenKernel.handler RegistrationNativePlatformMldsaProgram.coins setup native query
  | .inr _ => StateT.lift reserve

theorem reserve_source (reserve : StateT Platform ProbComp Bool) (before : Full (Private n KemSK Extra) Platform) :
    Prod.map id realize <$> (interpret (RegistrationNativePlatformCtxRunner.publicWork reserve)).run before =
      (RegistrationAgreementNestedState.flatten (StateT.lift reserve : StateT (Private n KemSK Extra) (StateT Platform ProbComp) Bool)).run (realize before) := by
  rw [RegistrationNativePlatformCtxRunner.public_run]
  change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (((StateT.lift reserve : StateT (Private n KemSK Extra) (StateT Platform ProbComp) Bool).run (realize before).1).run (realize before).2)
  simp only [Functor.map_map, StateT.run_lift, bind_pure_comp, StateT.run_map, realize, Prod.map_def, id_eq]

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxKernel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxKernel.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxKernel.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxKernel.reserve_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxKernel.reserve_source
