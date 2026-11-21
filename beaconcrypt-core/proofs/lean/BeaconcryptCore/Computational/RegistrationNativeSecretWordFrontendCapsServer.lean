-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsMaterial

/-! The actual symbolic Server accepts consume no material; one-use builds consume at most one. These direct AST bills retain mandatory authentication, replay, request logging, current chronological signing receipts and all allocator/codec failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer
open RegistrationNativeSecretWordServerCompiler
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare demand)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
abbrev Spec := LocalSpec
abbrev IsDemand := RegistrationNativeSecretWordFrontendCapsLocal.IsDemand (n := n) (KemSK := KemSK)

private theorem environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 :=
  RegistrationNativeSecretWordFrontendCapsLocal.effect_free work

/-- The actual ordered symbolic Server collector makes zero deferred material requests. -/
theorem collect_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Environment) :
    ((collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 :=
  RegistrationNativeSecretWordFrontendCapsLocal.server_collect_free setup checks packet authenticated before

private theorem prepare_free (work : OracleComp RegistrationNativeSecretWordMessage.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsDemand, RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, isQueryBoundP_query_iff]

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Root preparation returns only its public reference and never consumes a later material allowance. -/
theorem agreement_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((agreement (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  simp only [agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0) (collect_free setup checks packet authenticated env)
  intro result _
  cases result.1 with
  | none => trivial
  | some input => simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, isQueryBoundP_map_iff] using
      (prepare_free (n := n) (KemSK := KemSK) (RegistrationNativeSecretWordServerRoot.client authenticated.binding input))


private theorem bind_free {X Y : Type} (work : M n KemSK X) (next : X → M n KemSK Y)
    (first : ∀ before env, ((work.run before).run env).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0)
    (later : ∀ value before env, (((next value).run before).run env).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0)
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((work >>= next).run before).run env).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  simp only [StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (first before env)
  intro result _
  exact later result.1.1 result.1.2 result.2

private theorem retain_free (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((retain (n := n) (KemSK := KemSK) ready).run before).run env).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  simp only [retain, StateT.run]
  cases RegistrationNativeSecretWordServerMaterial.retain ready before with
  | fail error => trivial
  | div => trivial
  | ok result => rcases result with ⟨reply, after⟩; trivial

/-- Owned replay lookup, reservation and retained native capability insertion never consume a later material demand. -/
theorem afterAuthentication_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
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
/-- Mandatory native authentication and owned root preparation make no material demand, on every success or failure path. -/
theorem accept_free (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((accept (n := n) setup checks verify packet).run before).run env).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
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

private theorem common_free (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain) (env : Environment) :
    ((RegistrationNativeCommonCompiler.common (effect (KemSK := KemSK)) hkdf wire.frameWrite sign query).run env).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeCommonCompiler.common, RegistrationNativeCommonCompiler.publication,
        StateT.run, isQueryBoundP_map_iff]
      exact environment_free _
  | inr query =>
      simp [RegistrationNativeCommonCompiler.common, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, effect, IsDemand, RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, isQueryBoundP_query_iff]

/-- The complete public-reference Server build retains its actual single material-demand bill and current chronological signing receipts. -/
theorem build_bound (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativeSecretWordMessage.ServerState) (env : Environment) :
    (((build (n := n) (KemSK := KemSK) hkdf wire checks sign handle application).run before).run env).IsQueryBoundP (IsDemand (KemSK := KemSK)) 1 := by
  change (simulateQ (service hkdf wire sign)
    ((RegistrationNativeSecretWordServerMaterial.build wire checks.reservePeer handle application).run before)).run env |>.IsQueryBoundP _ 1
  apply (RegistrationNativeSecretWordFrontendCapsMaterial.build_bound wire checks.reservePeer handle application before).simulateQ_run_of_step
  · intro query counted current
    cases query with
    | inl message =>
        simp [service, demand, StateT.run_lift, bind_pure_comp,
          isQueryBoundP_map_iff, IsDemand, RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, isQueryBoundP_query_iff]
    | inr query => exact counted.elim
  · intro query free current
    cases query with
    | inl message => exact (free trivial).elim
    | inr query => exact common_free hkdf wire sign query current

end BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer.collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer.agreement_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer.agreement_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer.afterAuthentication_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer.afterAuthentication_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer.accept_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer.accept_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer.build_bound
