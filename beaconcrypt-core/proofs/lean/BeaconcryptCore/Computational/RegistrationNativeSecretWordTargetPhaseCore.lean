-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys

/-! Before the selected parsed attempt has been consumed, the concrete early provider's getter marker remains absent. Ordinary routed queries, including early challenge decapsulation, retain the marker. The proof uses the actual symbolic dispatch routing and actual provider transitions, independently of all outer material answers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterface (LocalSpec Spec liftLocal)
open RegistrationNativeSecretWordTargetSource (State)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Selected : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inr (.inr (.inr _)))) => True
  | _ => False
instance : DecidablePred (Selected (n := n) (KemSK := KemSK)) := fun query => by
  unfold Selected
  split <;> infer_instance

/-- Every ordinarily routed local continuation excludes the selected getter, regardless of its replies. -/
theorem ordinary_free (work : OracleComp (LocalSpec n KemSK) Value) :
    (simulateQ (liftLocal false) work).IsQueryBoundP (Selected (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false _ 0)
  intro query
  rcases query with message | paired | other | pool | key
  all_goals simp [liftLocal, RegistrationNativeSecretWordInterface.route,
    RegistrationNativeSecretWordInterface.routedKem, Selected, isQueryBoundP_query_iff]

private theorem server_free (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : RegistrationNativeSecretWordMessage.State source) :
    ((RegistrationNativeSecretWordFrontend.serverOpen false work).run before).IsQueryBoundP (Selected (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact ordinary_free _

private theorem beacon_free
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : RegistrationNativeSecretWordMessage.State source) :
    ((RegistrationNativeSecretWordFrontend.beacon work).run before).IsQueryBoundP (Selected (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordFrontend.beacon, StateT.run, isQueryBoundP_map_iff]
  exact ordinary_free _

private theorem record_free (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : RegistrationNativeSecretWordMessage.State source) :
    ((RegistrationNativeSecretWordFrontend.record (n := n) (KemSK := KemSK) query).run before).IsQueryBoundP
      (Selected (KemSK := KemSK)) 0 := by
  rcases query with server | ⟨owner, request⟩
  · simp [RegistrationNativeSecretWordFrontend.record, StateT.run, Selected,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · cases request <;> cases found : before.beacons[owner]? <;>
      simp [RegistrationNativeSecretWordFrontend.record, StateT.run, found, Selected,
        isQueryBoundP_map_iff, isQueryBoundP_query_iff]

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build
  RegistrationNativeSecretWordOwners.create RegistrationNativeSecretWordOwners.bundle RegistrationNativeSecretWordOwners.finish

/-- Only the actual selected parsed accept can emit an exposed getter; every other complete typed operation is quiet. -/
theorem handler_free (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : RegistrationNativeSecretWordMessage.State source)
    (quiet : ¬(RegistrationNativeSecretWordTargetCounter.isAccept query = true ∧ before.parsedAccepts = selectedAccept)) :
    ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (Selected (KemSK := KemSK)) 0 := by
  cases query with
  | inl coin => simp [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp,
      isQueryBoundP_map_iff, RegistrationNativeSecretWordFrontend.effect, Selected, isQueryBoundP_query_iff]
  | inr query => cases query with
    | create edPin mlPin keyId => exact beacon_free _ before
    | bundle owner => exact beacon_free _ before
    | finish owner packet => exact beacon_free _ before
    | accept packet =>
        have different : before.parsedAccepts ≠ selectedAccept := fun equal => quiet ⟨rfl, equal⟩
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_bind, StateT.run_get,
          StateT.run_modify, pure_bind, different, decide_false]
        exact server_free _ _
    | build handle application => exact server_free _ before
    | hmac key bytes => trivial
    | hash bytes => simp [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, RegistrationNativeSecretWordFrontend.effect, Selected, isQueryBoundP_query_iff]
    | serverSend keyId plaintext => exact record_free (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact record_free (.inl (.inr raw)) before
    | beaconSend owner plaintext => exact record_free (.inr (owner, .inl plaintext)) before
    | beaconRaw owner raw => exact record_free (.inr (owner, .inr raw)) before

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer

/-- Every actual non-exposed combined callback retains the early provider marker and all ordinary execution effects. -/
theorem query_phase (query : (Spec n KemSK).Domain) (quiet : ¬Selected (KemSK := KemSK) query)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (result : (Spec n KemSK).Range query × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((implementation query).run before)) : result.2.kem.2 = before.kem.2 := by
  have native : result ∈ support
      ((RegistrationNativeSecretWordInterpreter.handler setup wire route sign input inside provider query).run before) := by
    apply PqxdhDeploymentEnvironment.support_simulateQ_subset outer _
    exact supported
  rcases query with (message | (message | common) | routed) | record
  · simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.roots,
      StateT.run, support_map] at native
    obtain ⟨answer, _, equal⟩ := native
    cases equal
    rfl
  · simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.roots,
      StateT.run, support_map] at native
    obtain ⟨answer, _, equal⟩ := native
    cases equal
    rfl
  · simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.ordinary,
      StateT.run, support_map] at native
    obtain ⟨answer, _, equal⟩ := native
    cases equal
    rfl
  · rw [RegistrationNativeSecretWordInterpreter.kem_run, support_map] at native
    obtain ⟨answer, reached, equal⟩ := native
    have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativeSecretWordService.coins _ reached
    have ordinary : ¬RegistrationNativeKemRouting.IsExposed (ambient := RegistrationNativeKemInterface.OtherSpec) (KemSK := KemSK) routed := by
      rcases routed with (other | key) | query | key
      · trivial
      · trivial
      · trivial
      · exact quiet
    cases equal
    exact RegistrationNativeSecretWordKemEarlyKeys.nonexposed_phase setup.baseImpl setup.kem selected pairs publicKey challenge
      routed ordinary before.kem answer actual
  · simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.ordinary,
      StateT.run, support_map] at native
    obtain ⟨answer, _, equal⟩ := native
    cases equal
    rfl

/-- Any actual source continuation with zero selected-getter calls retains the complete current marker. -/
theorem program_phase (work : OracleComp (Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP (Selected (KemSK := KemSK)) 0)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (result : Value × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ implementation work).run before)) : result.2.kem.2 = before.kem.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨first, later⟩ := bounded
      have quiet := first.resolve_right (by omega)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      exact (ih middle.1 (by simpa using later middle.1) middle.2 result continued).trans
        (query_phase setup wire route sign input inside selected pairs publicKey challenge outer query quiet before middle called)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore.ordinary_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore.ordinary_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore.handler_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore.handler_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore.query_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore.query_phase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore.program_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore.program_phase
