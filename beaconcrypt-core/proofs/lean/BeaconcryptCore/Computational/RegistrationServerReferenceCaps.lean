-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceCompiler
import BeaconcryptCore.Computational.RegistrationServerMaterialCaps

/-! Structural native service bills count preparations and admitted material demands separately. Hashes, mandatory verification, local primitive callbacks and selected-DH reference collection do not query the hidden material service. Rejected and failed native branches retain the same bills. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceCaps
open RegistrationServerReferenceCompiler
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsDemand : (Spec n).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

instance : DecidablePred (IsDemand (n := n)) := fun query => by
  cases query with
  | inl query => exact isFalse id
  | inr query => cases query with
    | inl query => exact isTrue trivial
    | inr query => exact isFalse id

private theorem environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ effect work).IsQueryBoundP IsDemand 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsDemand, isQueryBoundP_query_iff]

private theorem backend_free (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    ((backend (n := n) setup checks query).run before).IsQueryBoundP IsDemand 0 :=
  environment_free _

private theorem backend_program_free (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : Environment) :
    ((simulateQ (backend (n := n) setup checks) work).run before).IsQueryBoundP IsDemand 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query counted
    contradiction
  · intro query free state
    exact backend_free setup checks query state

private theorem prefix_free (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    ((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (backend (n := n) setup checks)) visit query).run before).IsQueryBoundP IsDemand 0 := by
  cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact backend_program_free setup checks _ before
    | trivial

/-- The entire actual local prefix, including all optional primitive failures, makes zero material demands. -/
theorem collect_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Environment) :
    ((collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP IsDemand 0 := by
  unfold collect
  apply (isQueryBoundP_false _ 0).simulateQ_run_of_step
  · intro query counted
    contradiction
  · intro query free state
    exact prefix_free setup checks query state


private theorem prepare_free (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    (simulateQ (prepare (n := n)) work).IsQueryBoundP IsDemand 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsDemand, isQueryBoundP_query_iff]

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
    (((agreement (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP IsDemand 0 := by
  simp only [agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some input => simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using
      (prepare_free (n := n) (RegistrationServerReferenceRoot.client authenticated.binding input))


private theorem bind_free {X Y : Type} (work : M n X) (next : X → M n Y)
    (first : ∀ before env, ((work.run before).run env).IsQueryBoundP IsDemand 0)
    (later : ∀ value before env, (((next value).run before).run env).IsQueryBoundP IsDemand 0)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((work >>= next).run before).run env).IsQueryBoundP IsDemand 0 := by
  simp only [StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (first before env)
  intro result _
  exact later result.1.1 result.1.2 result.2

private theorem retain_free (ready : RegistrationServerReferenceRoot.Ready)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((retain (n := n) ready).run before).run env).IsQueryBoundP IsDemand 0 := by
  simp only [retain, StateT.run]
  cases RegistrationServerMaterialFrontend.retain ready before with
  | fail error => trivial
  | div => trivial
  | ok result => rcases result with ⟨reply, after⟩; trivial

/-- Owned replay lookup, reservation and retained native capability insertion never consume a later material demand. -/
theorem afterAuthentication_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP IsDemand 0 := by
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


private theorem lift_free (work : OracleComp (Spec n) Value) (free : work.IsQueryBoundP IsDemand 0)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((StateT.lift (StateT.lift work) : M n Value).run before).run env).IsQueryBoundP IsDemand 0 := by
  simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using free

attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- Mandatory native authentication and owned root preparation make no material demand, on every success or failure path. -/
theorem accept_free (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((accept (n := n) setup checks verify packet).run before).run env).IsQueryBoundP IsDemand 0 := by
  simp only [accept, StateT.run_bind, StateT.run_get, StateT.run_lift,
    pure_bind, bind_assoc]
  apply isQueryBoundP_bind (m := 0) (environment_free _)
  intro checked _
  cases checked with
  | fail error => trivial
  | div => trivial
  | ok result =>
      rcases result with ⟨events, reply⟩
      cases reply <;> first
        | exact afterAuthentication_free setup checks packet _ before env
        | trivial

/-- The complete public-reference Server build retains its actual single material-demand bill. -/
theorem build_bound (wire : RegistrationNativeWire.Wire) (checks : Checks) (handle : Nat)
    (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    (((build (n := n) wire checks handle application).run before).run env).IsQueryBoundP IsDemand 1 := by
  simp only [build, StateT.run, StateT.lift, bind_pure_comp, isQueryBoundP_map_iff]
  apply RawCtxSourceOpen.simulate_bound service RegistrationServerMaterialCaps.IsDemand IsDemand _ 1
    (RegistrationServerMaterialCaps.build_bound wire checks.reservePeer handle application before)
  intro query
  cases query with
  | inl message => simp [service, IsDemand, RegistrationServerMaterialCaps.IsDemand, isQueryBoundP_query_iff]
  | inr query => simp [service, IsDemand, RegistrationServerMaterialCaps.IsDemand, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationServerReferenceCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceCaps.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceCaps.collect_free

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceCaps.agreement_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceCaps.agreement_free

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceCaps.afterAuthentication_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceCaps.afterAuthentication_free

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceCaps.accept_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceCaps.accept_free

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceCaps.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceCaps.build_bound
