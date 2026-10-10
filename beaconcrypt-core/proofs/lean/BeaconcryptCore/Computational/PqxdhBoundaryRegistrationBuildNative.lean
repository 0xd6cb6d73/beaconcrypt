-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuild
import BeaconcryptCore.Computational.PqxdhDeploymentNative
import BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts

/-! Exact native pending-token settlement and CE build lift for the extracted Server builder. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative
open PqxdhBoundaryRegistrationBuild PqxdhServerAuthExperiment PqxdhServerAuthNative
variable {Reader Response KemSK ι : Type} {baseSpec : OracleSpec ι}

/-- The original native token wrapper with only its build program replaced by the equal extracted executor. -/
noncomputable def executeNativeBuild (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (session : Nat) (payload : Option Pqxdh.Bytes) :
    NativeGame KemSK (Option PqxdhServerRegistrationPublication.Response) := do
  let state ← nativeGet
  match state.pending session with
  | none => pure none
  | some token => do
      let result ← nativeCoins ((simulateQ (tailImpl setup codec checks)
        (executeBuild setup token.pending token.root payload () state.server)).run ([], state.ctx))
      let settled := settle state.server result.1
      nativeSet { state with
        pending := Function.update state.pending session none
        server := settled.2
        ctx := result.2.2
        ghost := { state.ghost with seals := state.ghost.seals ++ result.2.1.map (fun context => (session, context)) } }
      pure settled.1

/-- The complete native build computation retains the existing token consumption, full shared cache and literal successful-inner-seal log. -/
theorem native_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (session : Nat) (payload : Option Pqxdh.Bytes) :
    executeNativeBuild setup codec checks session payload = nativeBuild setup codec checks session payload := by
  simp only [executeNativeBuild, nativeBuild, build_exact]
  rfl

/-- A present pending token runs the complete extracted builder and settles exactly its returned Server state, primitive cache and seal log, preserving every other native field. -/
theorem native_present (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (session : Nat) (payload : Option Pqxdh.Bytes) (state : NativeState KemSK)
    (token : PqxdhServerRelatedRootConsumer.Returned) (found : state.2.pending session = some token) :
    (executeNativeBuild setup codec checks session payload).run state =
      (fun result =>
        let settled := settle state.2.server result.1
        (settled.1, (state.1, { state.2 with
          pending := Function.update state.2.pending session none
          server := settled.2
          ctx := result.2.2
          ghost := { state.2.ghost with seals := state.2.ghost.seals ++ result.2.1.map (fun context => (session, context)) } }))) <$>
      (simulateQ (tailImpl setup codec checks)
        (executeBuild setup token.pending token.root payload () state.2.server)).run ([], state.2.ctx) := by
  change executeNativeBuild setup codec checks session payload state = _
  unfold executeNativeBuild
  rw [nativeGet_bind, found]
  dsimp only
  rw [nativeCoins_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  rfl

/-- A missing token produces no response and changes no field, cache or log. -/
theorem native_missing (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (session : Nat) (payload : Option Pqxdh.Bytes) (state : NativeState KemSK)
    (missing : state.2.pending session = none) :
    (executeNativeBuild setup codec checks session payload).run state = pure (none, state) := by
  change executeNativeBuild setup codec checks session payload state = _
  unfold executeNativeBuild
  rw [nativeGet_bind, missing]
  rfl

/-- Every supported outcome consumes the addressed token, including absent tokens, all ordinary rejections and both writer failures. No allocation or success premise is needed. -/
theorem token_consumed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (session : Nat) (payload : Option Pqxdh.Bytes) (state : NativeState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × NativeState KemSK)
    (supported : result ∈ support ((executeNativeBuild setup codec checks session payload).run state)) :
    result.2.2.pending session = none := by
  cases found : state.2.pending session with
  | none =>
    rw [native_missing setup codec checks session payload state found] at supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact found
  | some token =>
    rw [native_present setup codec checks session payload state token found] at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨actual, _, rfl⟩ := supported
    simp only [Function.update_self]

/-- The exact extracted executor is the build branch of the original shared registration scheduler; owner records and the original root-family state remain intact. -/
theorem scheduler_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) (session : Nat) (payload : Option Pqxdh.Bytes) :
    PqxdhRegistrationSchedule.handler setup codec checks seed (.inr (.build session payload)) =
      PqxdhRegistrationSchedule.onShared (executeNativeBuild setup codec checks session payload) := by
  rw [native_exact]
  rfl

/-- The frozen CE native build uses that same computation, preserving full caches, owners, raw-attempt counters and the separate produced-record list. -/
theorem deployment_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (session : Nat) (payload : Option Pqxdh.Bytes) :
    PqxdhDeploymentNative.handler setup codec checks route seed (.inr (.build session payload)) =
      PqxdhDeploymentNative.onNative
        (PqxdhRegistrationSchedule.onShared (executeNativeBuild setup codec checks session payload)) := by
  rw [native_exact]
  rfl

/-- Full evaluated CE build equality survives every continuation on the complete result and deployment state, including all failure outcomes and native work. -/
theorem deployment_complete {Result : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (seed : PqxdhJointIdentity.IdentitySeed) (session : Nat) (payload : Option Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK)
    (next : Option PqxdhServerRegistrationPublication.Response × PqxdhDeploymentNative.State KemSK → ProbComp Result) :
    (PqxdhDeploymentNative.handler setup codec checks route seed (.inr (.build session payload))).run state >>= next =
      (executeNativeBuild setup codec checks session payload).run state.native.shared >>= fun result =>
        next (result.1, { state with native := { state.native with shared := result.2 } }) := by
  rw [deployment_build]
  simp only [PqxdhDeploymentNative.onNative, PqxdhRegistrationSchedule.onShared, StateT.run]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

/-- The existing actual native build budget transfers unchanged: at most one 64-byte CTX table miss, with zero draws on a hit. Real initializer, HKDF, AEAD, writer and local work are separate from this uniform-query count. -/
theorem native_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (session : Nat) (payload : Option Pqxdh.Bytes) (state : NativeState KemSK) :
    ((executeNativeBuild setup codec checks session payload).run state).IsTotalQueryBound 64 := by
  rw [native_exact]
  exact PqxdhServerAuthNativeUniformCosts.native_build_uniform setup codec checks session payload state

end BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.native_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.native_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.native_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.native_present

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.native_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.native_missing

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.token_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.token_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.scheduler_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.scheduler_build

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.deployment_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.deployment_build

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.deployment_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.deployment_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.native_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationBuildNative.native_uniform
