-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateLocal
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt

/-! The actual symbolic Server accepts consume no material; one-use builds consume at most one. These direct AST bills retain mandatory authentication, replay, request logging, current chronological signing receipts and all allocator/codec failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer
open RegistrationNativeSecretWordServerCompiler
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare demand)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
abbrev Spec := LocalSpec
abbrev IsCreate := RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (n := n) (KemSK := KemSK)

private theorem environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 :=
  RegistrationNativeSecretWordTargetNoCreateLocal.effect_free work

/-- The actual ordered symbolic Server collector makes zero private KEM birth requests. -/
theorem collect_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Environment) :
    ((collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 :=
  RegistrationNativeSecretWordTargetNoCreateLocal.server_collect_free setup checks packet authenticated before

private theorem prepare_free (work : OracleComp RegistrationNativeSecretWordMessage.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Root preparation returns only its public reference and never consumes a later private KEM birth allowance. -/
theorem agreement_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((agreement (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  simp only [agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some input => simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using
      (prepare_free (n := n) (KemSK := KemSK) (RegistrationNativeSecretWordServerRoot.client authenticated.binding input))


private theorem bind_free {X Y : Type} (work : M n KemSK X) (next : X → M n KemSK Y)
    (first : ∀ before env, ((work.run before).run env).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0)
    (later : ∀ value before env, (((next value).run before).run env).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0)
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((work >>= next).run before).run env).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  simp only [StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (first before env)
  intro result _
  exact later result.1.1 result.1.2 result.2

private theorem retain_free (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((retain (n := n) (KemSK := KemSK) ready).run before).run env).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  simp only [retain, StateT.run]
  cases RegistrationNativeSecretWordServerMaterial.retain ready before with
  | fail error => trivial
  | div => trivial
  | ok result => rcases result with ⟨reply, after⟩; trivial

/-- Owned replay lookup, reservation and retained native capability insertion never consume a later private KEM birth. -/
theorem afterAuthentication_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
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



private theorem select_free {Index S Result : Type} {spec : OracleSpec Index}
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (checked : RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication))
    (failed : Error → StateT S (OracleComp spec) Result) (diverged absent : StateT S (OracleComp spec) Result)
    (accepted : registration.AuthenticatedInit → StateT S (OracleComp spec) Result) (before : S)
    (failureFree : ∀ error, ((failed error).run before).IsQueryBoundP predicate 0)
    (divergenceFree : (diverged.run before).IsQueryBoundP predicate 0)
    (absenceFree : (absent.run before).IsQueryBoundP predicate 0)
    (acceptedFree : ∀ authenticated, ((accepted authenticated).run before).IsQueryBoundP predicate 0) :
    (((match checked with
      | .fail error => failed error
      | .div => diverged
      | .ok (_events, .Accepted authenticated) => accepted authenticated
      | .ok _ => absent) : StateT S (OracleComp spec) Result).run before).IsQueryBoundP predicate 0 := by
  cases checked with
  | fail error => exact failureFree error
  | div => exact divergenceFree
  | ok checked => rcases checked with ⟨events, stage⟩; cases stage <;> first | exact acceptedFree _ | exact absenceFree

attribute [local irreducible] RegistrationAuthenticationCompiler.program

private theorem free_of_eq {Index Result : Type} {spec : OracleSpec Index}
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (first second : OracleComp spec Result) (same : first = second)
    (bounded : second.IsQueryBoundP predicate 0) : first.IsQueryBoundP predicate 0 := same ▸ bounded

private noncomputable def acceptBody (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationNativeSecretWordMessage.ServerState) := (do
      let checked ← StateT.lift (simulateQ (effect (n := n) (KemSK := KemSK))
        (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.pin packet))
      match checked with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok (_events, .Accepted authenticated) => (afterAuthentication setup checks packet authenticated).run before
      | .ok _ => pure (.ok none, before) : StateT Environment (OracleComp (LocalSpec n KemSK)) _)

set_option maxRecDepth 4096 in
private theorem acceptBody_free (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    ((acceptBody (n := n) setup checks verify packet before).run env).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  simp only [acceptBody, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0) (environment_free _)
  intro checked _
  apply select_free
  · intro error
    simp only [StateT.run_pure]
    trivial
  · simp only [StateT.run_pure]
    trivial
  · simp only [StateT.run_pure]
    trivial
  · intro authenticated
    exact afterAuthentication_free setup checks packet authenticated before env

/-- Mandatory native authentication and owned root preparation make no private KEM birth, on every success or failure path. -/
theorem accept_free (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((accept (n := n) setup checks verify packet).run before).run env).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  have same : (accept (n := n) setup checks verify packet).run before =
      acceptBody setup checks verify packet before :=
    RegistrationNativeSecretWordTargetServerReceipt.accept_program_source setup checks verify packet before
  exact free_of_eq _ _ _ (congrArg (fun work => work.run env) same)
    (acceptBody_free setup checks verify packet before env)


private theorem common_free (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain) (env : Environment) :
    ((RegistrationNativeCommonCompiler.common (effect (KemSK := KemSK)) hkdf wire.frameWrite sign query).run env).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeCommonCompiler.common, RegistrationNativeCommonCompiler.publication,
        StateT.run, isQueryBoundP_map_iff]
      exact environment_free _
  | inr query =>
      simp [RegistrationNativeCommonCompiler.common, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, effect, IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]

/-- The complete Server build runs only material/Common callbacks, so it cannot create a private KEM key. -/
theorem build_free (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((build (n := n) (KemSK := KemSK) hkdf wire checks sign handle application).run before).run env).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  change (simulateQ (service hkdf wire sign)
    ((RegistrationNativeSecretWordServerMaterial.build wire checks.reservePeer handle application).run before)).run env |>.IsQueryBoundP _ 0
  apply (isQueryBoundP_false
    ((RegistrationNativeSecretWordServerMaterial.build wire checks.reservePeer handle application).run before) 0).simulateQ_run_of_step
  · intro query impossible current
    exact impossible.elim
  · intro query _ current
    cases query with
    | inl message =>
        simp [service, demand, StateT.run_lift, bind_pure_comp,
          isQueryBoundP_map_iff, IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
    | inr query => exact common_free hkdf wire sign query current

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer.collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer.agreement_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer.agreement_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer.afterAuthentication_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer.afterAuthentication_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer.accept_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer.accept_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer.build_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer.build_free
