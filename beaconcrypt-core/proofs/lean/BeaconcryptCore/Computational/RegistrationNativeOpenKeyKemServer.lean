-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler
import BeaconcryptCore.Computational.RegistrationServerReferenceCaps
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon
import BeaconcryptCore.Computational.RegistrationServerMaterialCaps

/-! Actual mandatory-authentication Server reference acceptance never creates or reveals a private KEM key. Its exposed encapsulation, shared-cache authentication, replay gates, root preparation and full failure states remain present. These structural zero bills hold before any candidate or real interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer
open RegistrationServerOpenReferenceCompiler
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (Spec effect prepare)
open RegistrationNativeKemReferenceCompiler (backend collect visit)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {kind : RegistrationNativeKemBeaconFootprint.Kind}

abbrev IsPrivate := RegistrationNativeOpenKeyKemBeacon.IsPrivate (n := n) (KemSK := KemSK) kind

private theorem environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate, isQueryBoundP_query_iff]

private theorem lift_free (work : OracleComp (RegistrationServerReferenceCompiler.Spec n) Value) :
    (simulateQ (RegistrationNativeKemReferenceCompiler.lift (KemSK := KemSK)) work).IsQueryBoundP
      (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro query
  rcases query with _ | _ | _ <;>
    simp [RegistrationNativeKemReferenceCompiler.lift, IsPrivate,
      RegistrationNativeOpenKeyKemBeacon.IsPrivate, isQueryBoundP_query_iff]

private theorem backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    ((backend (n := n) setup checks query).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  cases query with
  | encapsulate key =>
      cases key <;>
        simp [backend, StateT.run, RegistrationNativeKemInterface.server,
          RegistrationNativeKemInterface.encapsulate, simulateQ_map,
          RegistrationBeaconReferenceCompiler.indexed, IsPrivate, isQueryBoundP_map_iff]
      split <;> simp [isQueryBoundP_map_iff, RegistrationNativeOpenKeyKemBeacon.IsPrivate, RegistrationNativeKemCompilerFootprint.predicate,
        isQueryBoundP_query_iff]
  | _ => exact lift_free _

private theorem backend_program_free (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : Environment) :
    ((simulateQ (backend (n := n) setup checks) work).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query counted
    contradiction
  · intro query free state
    exact backend_free setup checks query state

private theorem prefix_free (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    ((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (backend (n := n) setup checks)) visit query).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact backend_program_free setup checks _ before
    | trivial

/-- The entire actual local prefix, including all optional primitive failures, makes zero material demands. -/
theorem collect_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Environment) :
    ((collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  unfold RegistrationNativeKemReferenceCompiler.collect
  apply (isQueryBoundP_false _ 0).simulateQ_run_of_step
  · intro query counted
    contradiction
  · intro query free state
    exact prefix_free setup checks query state


private theorem prepare_free (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate, isQueryBoundP_query_iff]

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Root preparation returns only its public reference and never consumes a later material allowance. -/
theorem agreement_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((agreement (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  simp only [agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some input => simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using
      (prepare_free (n := n) (KemSK := KemSK) (RegistrationServerReferenceRoot.client authenticated.binding input))


private theorem bind_free {X Y : Type} (work : M n KemSK X) (next : X → M n KemSK Y)
    (first : ∀ before env, ((work.run before).run env).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0)
    (later : ∀ value before env, (((next value).run before).run env).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((work >>= next).run before).run env).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  simp only [StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (first before env)
  intro result _
  exact later result.1.1 result.1.2 result.2

private theorem retain_free (ready : RegistrationServerReferenceRoot.Ready)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((retain (n := n) (KemSK := KemSK) ready).run before).run env).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  simp only [retain, StateT.run]
  cases RegistrationServerMaterialFrontend.retain ready before with
  | fail error => trivial
  | div => trivial
  | ok result => rcases result with ⟨reply, after⟩; trivial

/-- Owned replay lookup, reservation and retained native capability insertion never consume a later material demand. -/
theorem afterAuthentication_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  simp only [afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · split
    · apply bind_free _ _ (fun before env => agreement_free setup checks packet authenticated before env)
      intro value state current
      cases value with
      | fail error => trivial
      | div => trivial
      | ok value => cases value with
        | none => trivial
        | some ready => exact retain_free ready state current
    · trivial



attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- Mandatory native authentication and owned root preparation neither create nor reveal a KEM key, on every success or failure path. -/
theorem accept_free (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((accept (n := n) setup checks verify packet).run before).run env).IsQueryBoundP (IsPrivate (KemSK := KemSK) (kind := kind)) 0 := by
  unfold accept
  apply bind_free
  · intro current env
    simp only [StateT.run_get, StateT.run_pure]
    trivial
  · intro current before env
    apply bind_free
    · intro state env
      simpa only [StateT.run_lift, StateT.run_map, map_state_apply, bind_pure_comp, isQueryBoundP_map_iff] using environment_free (kind := kind)
        (RegistrationAuthenticationCompiler.program setup.source.crypto verify current.pin packet)
    · intro checked state env
      cases checked with
      | fail error | div => trivial
      | ok result =>
          rcases result with ⟨events, reply⟩
          cases reply <;> first
            | exact afterAuthentication_free setup checks packet _ state env
            | trivial

private theorem private_of_kem (query : (Spec n KemSK).Domain) (counted : IsPrivate (kind := kind) query) :
    RegistrationNativeProviderBuildCaps.IsLocalKem query := by
  rcases query with message | (query | query)
  · exact counted.elim
  · exact counted.elim
  · trivial

/-- Actual Server build uses only material, signing and record operations, never private KEM birth or reveal. -/
theorem build_free (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((build (n := n) (KemSK := KemSK) hkdf wire checks sign handle application).run before).run env).IsQueryBoundP
      (IsPrivate (KemSK := KemSK) (kind := kind)) 0 :=
  OracleComp.IsQueryBoundP.of_imp (private_of_kem (kind := kind) (KemSK := KemSK))
    (RegistrationNativeProviderBuildCaps.build_zero hkdf wire checks sign handle application before env)

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer.collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer.agreement_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer.agreement_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer.afterAuthentication_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer.afterAuthentication_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer.accept_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer.accept_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer.build_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer.build_free
