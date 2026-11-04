-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishControllerHashBounds
/-! The literal corrected opaque-owner finish uses one response-authentication hash and at most one first-record commitment hash. Every malformed packet, optional primitive rejection, source copy, assigned-ID installation and terminal abort is retained. This is a source syntax bill for the physical shared Env hash backend, with no success, frame or old-whole-handler premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishHashBounds
open RegistrationNativePlatformIdentityFrontendHashBounds
open RegistrationNativeIdentityFrontend (M Owner)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK Auxiliary A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem program_bound {J : Type} {queries : OracleSpec J} (selected : J → Prop) [DecidablePred selected]
    (callback : QueryImpl queries (M n KemSK Auxiliary source))
    (steps : ∀ query, Bounded (callback query) (if selected query then 1 else 0))
    (work : OracleComp queries A) (cap : Nat) (bounded : work.IsQueryBoundP selected cap) :
    Bounded (simulateQ callback work) cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => simpa only [simulateQ_pure] using pure_bound (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) value cap
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query]
      have combined := bind_bound (callback query) (fun value => simulateQ callback (next value))
        (if selected query then 1 else 0) (if selected query then cap - 1 else cap)
        (steps query) (fun value => ih value _ (bounded.2 value))
      have total : (if selected query then 1 else 0) + (if selected query then cap - 1 else cap) = cap := by
        by_cases active : selected query
        · have positive := bounded.1
          simp only [active, not_true_eq_false, false_or] at positive
          simp only [active, ite_true]
          omega
        · simp only [active, ite_false, Nat.zero_add]
      simpa only [total] using combined

private theorem authentication_bound (setup : Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    Bounded (RegistrationNativeIdentityFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source query)
      (if RegistrationAuthenticationHashBounds.IsHash query then 1 else 0) := by
  cases query with
  | hash request => exact bind_bound _ _ 1 0 (hash_bound request) (fun _ => pure_bound _ _)
  | mldsa request | ed25519 request => exact pure_bound _ _

private theorem response_bound (setup : Setup base KemSK) (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket) :
    Bounded (simulateQ (RegistrationNativeIdentityFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source)
      (RegistrationResponseExecutor.begin pending packet)) 1 :=
  program_bound RegistrationAuthenticationHashBounds.IsHash _ (authentication_bound setup) _ 1
    (RegistrationNativePlatformIdentityFinishControllerHashBounds.response_begin pending packet)

private theorem agreement_bound (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec A) :
    Bounded (simulateQ (RegistrationNativeIdentityFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime) work) 0 :=
  program_bound (fun _ => False) _
    (RegistrationNativePlatformIdentityFinishPrimitiveHashBounds.agreement_bound setup owner oneTime) work 0
    (isQueryBoundP_false work 0)

private theorem record_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (completed : agreement.BeaconAgreement) :
    Bounded (simulateQ (RegistrationNativeIdentityFrontend.record (n := n) (Auxiliary := Auxiliary) (source := source) setup wire)
      (RegistrationBeaconRecordExecutor.begin completed)) 1 :=
  program_bound RegistrationNativePlatformIdentityFinishPrimitiveHashBounds.IsRecordHash _
    (RegistrationNativePlatformIdentityFinishPrimitiveHashBounds.record_bound setup wire) _ 1
    (RegistrationNativePlatformIdentityFinishControllerHashBounds.record_begin completed)

private theorem abort_bound (owner : Owner source) (value : A) (cap : Nat) :
    Bounded (RegistrationNativeIdentityFrontend.abort owner *> pure value : M n KemSK Auxiliary source A) cap := by
  simp only [RegistrationNativeIdentityFrontend.abort, seqRight_eq_bind, bind_assoc, pure_bind]
  simpa only [Nat.zero_add] using bind_bound _ _ 0 cap (effect_bound _) (fun _ => pure_bound value cap)

private theorem record_after_bound (index : Nat) (owner : Owner source) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Bounded (RegistrationNativePlatformIdentityFinishRecord.after (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner reply) 0 := by
  cases reply with
  | fail error | div => exact abort_bound owner _ _
  | ok result => cases result with
    | Err aborted => exact abort_bound owner _ _
    | Ok completed =>
        change Bounded (RegistrationNativePlatformIdentityFinishRecord.install index owner completed) 0
        rw [RegistrationNativePlatformIdentityFinishRecord.install_exact]
        apply bind_bound _ _ 0 0 (effect_bound _)
        intro installed
        cases installed with
        | false => exact abort_bound owner _ _
        | true => exact bind_bound _ _ 0 0 (modify_bound _) (fun _ => pure_bound _ _)

private theorem after_agreement_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (reply : RustM agreement.AgreementEffect) :
    Bounded (RegistrationNativePlatformIdentityFinishSteps.afterAgreement (n := n) (Auxiliary := Auxiliary) setup wire index owner reply) 1 := by
  cases reply with
  | fail error | div => exact abort_bound owner _ _
  | ok effect => cases effect with
    | Rejected previous | ConvertPublic pending | ConvertSecret pending | GenerateEphemeral pending | Encapsulate pending
      | Decapsulate pending | Dh pending | RootKdf pending | ServerComplete completed => exact abort_bound owner _ _
    | BeaconComplete completed =>
        exact bind_bound _ _ 1 0 (record_bound setup wire completed) (record_after_bound index owner)

private theorem after_authentication_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Bounded (RegistrationNativePlatformIdentityFinishSteps.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime reply) 1 := by
  cases reply with
  | fail error | div => exact abort_bound owner _ _
  | ok result => cases result with
    | Err aborted => exact abort_bound owner _ _
    | Ok authenticated =>
        exact bind_bound _ _ 0 1 (agreement_bound setup owner oneTime _) (after_agreement_bound setup wire index owner)

/-- The exact active source body retains both hash positions and every abort/install branch, including assigned-ID installation after the actual source copy. -/
theorem begin_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) :
    Bounded (RegistrationNativePlatformIdentityFinishSteps.begin (n := n) (Auxiliary := Auxiliary) setup wire index owner pending oneTime packet) 2 := by
  cases moved : pending.aborted_state with
  | fail error | div =>
      simpa only [RegistrationNativePlatformIdentityFinishSteps.begin, moved] using
        (pure_bound (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) _ 2)
  | ok aborted =>
      simp only [RegistrationNativePlatformIdentityFinishSteps.begin, moved]
      exact bind_bound _ _ 0 2 (modify_bound _) (fun _ => bind_bound _ _ 1 1
        (response_bound setup pending _) (after_authentication_bound setup wire index owner oneTime))

private theorem start_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (packet : Option registration.ResponsePacket) :
    Bounded (RegistrationNativePlatformIdentityFinishRun.start (n := n) (Auxiliary := Auxiliary) setup wire index owner packet) 2 := by
  cases phase : owner.phase with
  | initSent pending oneTime =>
      simpa only [RegistrationNativePlatformIdentityFinishRun.start, phase] using begin_bound setup wire index owner pending oneTime packet
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simp only [RegistrationNativePlatformIdentityFinishRun.start, phase]
      exact pure_bound _ _

/-- The complete literal corrected opaque-owner finish has at most two physical shared Env hash calls, for every owner roster and reached environment. -/
theorem finish_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    Bounded (RegistrationNativePlatformIdentityFinishRun.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) 2 := by
  unfold RegistrationNativePlatformIdentityFinishRun.finish
  apply bind_bound _ _ 0 2 get_bound
  intro owners
  cases owners[index]? with
  | none => exact pure_bound _ _
  | some owner => exact start_bound setup wire index owner packet
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishHashBounds.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishHashBounds.begin_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishHashBounds.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishHashBounds.finish_bound
