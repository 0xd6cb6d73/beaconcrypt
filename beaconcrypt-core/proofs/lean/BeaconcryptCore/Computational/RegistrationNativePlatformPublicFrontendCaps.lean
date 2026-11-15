-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontend
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps
/-! The corrected registration callbacks are constructed over the local reference/effect language. Their type contains no ongoing record query; only the separate typed record branches invoke that surface. This structural fact retains arbitrary dynamic platform computations and failed writer histories. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontendCaps
attribute [local irreducible] RegistrationNativePlatformServerOpenControl.accept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend (Spec LocalSpec State LocalM embedLocal executeLocal)
variable {n : Nat} {E Platform ι KemSK A : Type} {base : OracleSpec ι}

def IsRecord : (Spec n Unit).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred (IsRecord (n := n)) := fun query => by
  rcases query with (query | query) | coin <;> simp only [IsRecord] <;> infer_instance

/-- The complete local language, including its separate public uniform branch, embeds without any ongoing record query. -/
theorem local_zero (work : OracleComp (LocalSpec n KemSK) A) :
    (simulateQ (embedLocal (KemSK := KemSK)) work).IsQueryBoundP IsRecord 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _
  cases query with
  | inl query =>
      simp only [embedLocal, isQueryBoundP_query_iff, IsRecord]
      intro impossible
      exact impossible.elim
  | inr coin =>
      simp only [embedLocal, RegistrationNativePlatformPublicFrontend.publicCoin, isQueryBoundP_query_iff, IsRecord]
      intro impossible
      exact impossible.elim

private theorem execute_zero {source : RegistrationNativeMldsa.Source}
    (work : LocalM n KemSK Platform source A) (before : State source Platform) :
    ((executeLocal (KemSK := KemSK) work).run before).IsQueryBoundP IsRecord 0 :=
  local_zero (KemSK := KemSK) (work.run before)

/-- Every actual corrected typed registration/HMAC callback is structurally record-free, including stateful reserve, source encoding and corrected assigned-ID completion. -/
theorem typed_zero [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (command : RegistrationNativeRawAdapter.Command) (allowed : RegistrationNativeHiddenEnvironmentCaps.IsEnvironment command)
    (before : State source Platform) :
    ((RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation (.inr command)).run before).IsQueryBoundP IsRecord 0 := by
  cases command with
  | create edPin mlPin keyId => exact execute_zero (KemSK := KemSK) _ before
  | bundle index => exact execute_zero (KemSK := KemSK) _ before
  | accept packet => exact execute_zero (KemSK := KemSK) _ before
  | build handle application => exact execute_zero (KemSK := KemSK) _ before
  | finish index packet => exact execute_zero (KemSK := KemSK) _ before
  | hmac key message => exact isQueryBoundP_pure IsRecord _ 0
  | hash bytes | serverSend keyId bytes | serverRaw raw | beaconSend index bytes | beaconRaw index raw => exact allowed.elim

noncomputable def raw [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    : QueryImpl RegistrationNativeInterface.Spec (RegistrationNativePlatformPublicFrontend.M n KemSK Platform source) :=
  (RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation) ∘ₛ
    RegistrationNativeRawAdapter.adapter wire

/-- Parsing a raw registration command retains the same structural boundary, including malformed packets and cancelled handles. -/
theorem raw_zero [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeEntropyInterface.EnvQuery) (before : State source Platform) :
    ((raw (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation (.inr query.val)).run before).IsQueryBoundP IsRecord 0 := by
  rcases query with ⟨command, environment⟩
  cases command with
  | create edPin mlPin keyId =>
      simp only [raw, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter]
      cases edParsed : PqxdhDeploymentInterface.parsePin edPin <;>
        cases mlParsed : RegistrationNativeWire.parseMldsaPin mlPin
      all_goals simp only [simulateQ_pure, StateT.run_pure, isQueryBoundP_pure, simulateQ_map,
        simulateQ_spec_query, StateT.run_map, isQueryBoundP_map_iff]
      apply typed_zero setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation
      trivial
  | accept bytes =>
      simp only [raw, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter]
      cases parsed : RegistrationNativeWire.readInit wire bytes
      · simp only [simulateQ_pure, StateT.run_pure, isQueryBoundP_pure]
      · simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, isQueryBoundP_map_iff]
        apply typed_zero setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation
        trivial
  | bundle owner | build handle application | finish owner bytes | hmac key bytes =>
      simp only [raw, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
        simulateQ_map, simulateQ_spec_query, StateT.run_map, isQueryBoundP_map_iff]
      apply typed_zero setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation
      trivial
  | hash bytes | serverSend keyId bytes | serverRaw bytes | beaconSend owner bytes | beaconRaw owner bytes =>
      exact environment.elim

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontendCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontendCaps.local_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontendCaps.local_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontendCaps.typed_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontendCaps.typed_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontendCaps.raw_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontendCaps.raw_zero
