-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicBuildObservedExtraction
import BeaconcryptCore.Refinement.AdapterPublicServerBuildWithRecord
/-! A checked single-subtree annotation of the actual extracted Builder replaces only its reserved-success record suffix. The normalization below is proved directly on that annotated AST, and the literal specialization restores the original SDK body. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicServerBuildObservedBody
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
universe u v w
private theorem call_apply {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := m) source arg = call (m := m) (source arg) := rfl
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl
private theorem call_result {m : Type → Type} [LiftRust m] {A : Type} (source : RustM A) :
    call (m := m) source = liftRust source := rfl
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [containers : ContainerOperations (RustT m)]
variable [children : ChildOperations (RustT m)]

open AdapterPublicServerBuildBody (Server Reply)
variable (completion :Server → registration.ServerInitialKdf → RustT m Reply)

theorem source (self :Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :
    AdapterPublicBuildObservedRequest.run (m:=RustT m) completion self token data=
      AdapterPublicServerBuildWithRecord.build (fun current initial=>(completion current initial).run) self token data :=by
  simp only [AdapterPublicBuildObservedRequest.run,AdapterPublicServerBuildWithRecord.build,
    AdapterPublicServerBuildWithRecord.lookup,AdapterPublicServerBuildWithRecord.reserved,
    AdapterPublicServerBuildBody.checked,call_apply,call_result]
  apply bind_congr
  intro application
  apply bind_congr
  intro plaintext
  apply bind_congr
  intro pin
  cases pin with
  | none =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
  | some pin =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, lift_ok, pure_bind]
    apply bind_congr
    intro lookupResult
    cases lookupResult with
    | Err prior =>
      simp only [core.result.Result.ok,

        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
    | Ok pending =>
      simp only [core.result.Result.ok,
         lift_ok, pure_bind]
      apply bind_congr
      intro identifier
      apply bind_congr
      intro size
      apply bind_congr
      intro admitted
      cases admitted with
      | none =>
        simp only [

          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
      | some capacity =>
        simp only [
           lift_ok, pure_bind]
        apply bind_congr
        intro occupied
        apply bind_congr
        intro pendingResult
        cases pendingResult with
        | Err prior =>
          simp only [

            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
        | Ok initial =>
          simp only [
             lift_ok, pure_bind]
          apply bind_congr
          rintro ⟨allocation, known⟩
          cases allocation with
          | Err prior =>
            simp only [

              core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
          | Ok unitValue =>
            cases unitValue
            simp only [
               lift_ok, pure_bind]

omit completion in
theorem literal (self :Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :
    AdapterPublicBuildObservedRequest.run (m:=RustT m) AdapterPublicServerBuildBody.record self token data=
      beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m:=RustT m) self token data :=by
  rw [source]
  apply RustT.ext
  exact (AdapterPublicServerBuildWithRecord.source self token data).symm
end BeaconcryptCore.Refinement.AdapterPublicServerBuildObservedBody

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildObservedBody.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildObservedBody.source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildObservedBody.literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildObservedBody.literal
