import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerPin
/-! The corrected OPEN accept controller retains its original configured Server pin. Repeated pin hashing is a local result; reservation, authentication, agreement and retain do not overwrite the stored pin. Every failure and the full common runtime state remain in the supported run. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinOpen
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativePlatformSecretWordOpen
variable {n : Nat} {I KemSK J World : Type} {base : OracleSpec I} {spec : OracleSpec J}
abbrev M (World : Type) (spec : OracleSpec J) := StateT World (OracleComp spec)
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value,before) := rfl
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value,before)) <$> work := bind_pure_comp _ _
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : A → B) (work : StateT S m A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem core_agreement (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment)
    (result : (RustM (Option ServerReady) × ServerState) × Environment)
    (supported : result ∈ support (((RegistrationNativeSecretWordServerCompiler.agreement (n := n) setup checks packet authenticated).run before).run env)) :
    result.1.2=before := by
  simp only [RegistrationNativeSecretWordServerCompiler.agreement,StateT.run_bind,StateT.run_lift,
    bind_assoc,pure_bind,mem_support_bind_iff] at supported
  obtain ⟨collected,_possible,supported⟩ := supported
  cases formed : collected.1 with
  | none =>
    simp only [formed,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    rfl
  | some pending =>
    simp only [formed,StateT.run,lift_apply,map_apply,Functor.map_map,support_map] at supported
    obtain ⟨returned,_possible,equal⟩ := supported
    exact (congrArg (fun result => result.1.2) equal).symm

private theorem agreement_pin
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (M World spec))
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment) (previous : World)
    (result : ((RustM (Option ServerReady) × ServerState) × Environment) × World)
    (supported : result ∈ support ((((agreement implementation setup checks packet authenticated).run before).run env).run previous)) :
    result.1.1.2=before := by
  apply core_agreement setup checks packet authenticated before env result.1
  apply OracleComp.support_simulateQ_run'_subset implementation _ previous
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst supported

private theorem retain_pin (ready : ServerReady) (before : ServerState) (env : Environment) (previous : World)
    (result : ((RustM (Option Nat) × ServerState) × Environment) × World)
    (supported : result ∈ support ((((retain (m := M World spec) ready).run before).run env).run previous)) :
    result.1.1.2.pin=before.pin := by
  cases consumed : RegistrationReplaySchedule.consume
      (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.consumed with
  | fail error | div =>
      simp only [retain,RegistrationNativeSecretWordServerMaterial.retain,consumed,StateT.run,pure_apply,mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok pair => rcases pair with ⟨entry,history⟩; cases entry <;>
      simp only [retain,RegistrationNativeSecretWordServerMaterial.retain,consumed,StateT.run,pure_apply,mem_support_pure_iff] at supported <;>
      cases supported <;> rfl

private theorem after_authentication
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (M World spec))
    (reserve : M World spec Bool) (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : ServerState) (env : Environment) (previous : World)
    (result : ((RustM (Option Nat) × ServerState) × Environment) × World)
    (supported : result ∈ support ((((afterAuthentication implementation reserve setup checks packet authenticated).run before).run env).run previous)) :
    result.1.1.2.pin=before.pin := by
  simp only [afterAuthentication,StateT.run_bind,StateT.run_get,pure_bind] at supported
  split at supported
  · simp only [StateT.run,pure_apply,mem_support_pure_iff] at supported
    cases supported
    rfl
  · simp only [StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,mem_support_bind_iff] at supported
    obtain ⟨allowed,_reserved,supported⟩ := supported
    cases chosen : allowed.1 with
    | false =>
      simp only [chosen,Bool.false_eq_true,ite_false,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      rfl
    | true =>
      simp only [chosen,ite_true,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨accepted,called,supported⟩ := supported
      have same := agreement_pin implementation setup checks packet authenticated before env allowed.2 accepted called
      cases formed : accepted.1.1.1 with
      | fail error | div =>
        simp only [formed,StateT.run_pure,mem_support_pure_iff] at supported
        cases supported
        exact congrArg (fun server => server.pin) same
      | ok optional => cases optional with
        | none =>
          simp only [formed,StateT.run_pure,mem_support_pure_iff] at supported
          cases supported
          exact congrArg (fun server => server.pin) same
        | some ready =>
          simp only [formed] at supported
          exact (retain_pin ready accepted.1.1.2 accepted.1.2 accepted.2 result supported).trans (congrArg (fun server => server.pin) same)

attribute [local irreducible] RegistrationAuthenticationCompiler.program

private theorem after_pin
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (M World spec))
    (reserve : M World spec Bool) (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (current : RegistrationNativeServerPinRecompute.PinReply)
    (before : ServerState) (env : Environment) (previous : World)
    (result : ((RustM (Option Nat) × ServerState) × Environment) × World)
    (supported : result ∈ support ((((afterPin implementation reserve setup checks verify packet current).run before).run env).run previous)) :
    result.1.1.2.pin=before.pin := by
  cases current with
  | fail error | div =>
      simp only [afterPin,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok optional => cases optional with
    | none =>
      simp only [afterPin,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      rfl
    | some pin =>
      simp only [afterPin,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,mem_support_bind_iff] at supported
      obtain ⟨checked,_verified,supported⟩ := supported
      cases verdict : checked.1 with
      | fail error | div =>
        simp only [verdict,StateT.run_pure,mem_support_pure_iff] at supported
        cases supported
        rfl
      | ok value => rcases value with ⟨events,verdictValue⟩; cases verdictValue with
        | Accepted authenticated =>
          simp only [verdict] at supported
          exact after_authentication implementation reserve setup checks packet authenticated before env checked.2 result supported
        | _ =>
          simp only [verdict,StateT.run_pure,mem_support_pure_iff] at supported
          cases supported
          rfl

/-- Literal corrected OPEN acceptance retains the stored Server pin under arbitrary source callbacks and common mutable state. -/
theorem accept
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (M World spec))
    (reserve : M World spec Bool) (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : ServerState) (env : Environment) (previous : World)
    (result : ((RustM (Option Nat) × ServerState) × Environment) × World)
    (supported : result ∈ support ((((RegistrationNativePlatformSecretWordOpen.accept implementation reserve setup checks verify packet).run before).run env).run previous)) :
    result.1.1.2.pin=before.pin := by
  simp only [RegistrationNativePlatformSecretWordOpen.accept,StateT.run_bind,StateT.run_get,StateT.run_lift,
    pure_bind,bind_pure_comp,bind_map_left,mem_support_bind_iff] at supported
  obtain ⟨current,_hashed,supported⟩ := supported
  exact after_pin implementation reserve setup checks verify packet current.1 before env current.2 result supported
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinOpen

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinOpen.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinOpen.accept
