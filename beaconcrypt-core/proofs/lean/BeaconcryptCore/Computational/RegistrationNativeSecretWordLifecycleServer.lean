-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServerCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCounter

/-! The actual selected routed Server getter occurs at most once over every adaptive original native client. The parsed ordinal is consumed before authentication, and the one selected controller has only one encapsulation position. A ghost monitor retains the complete original computation and counts actual exposed KEM queries, including all failures and original hidden-ledger draws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServer
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicFrontend (Spec LocalSpec State M handler liftLocal liftRoutedKem)
open RegistrationNativeSecretWordLifecycleCore (monitor)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def IsSelected : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inr (.inr (.inr _)))) => True
  | _ => False
instance : DecidablePred (IsSelected (n := n) (KemSK := KemSK)) := fun query => by
  unfold IsSelected
  split <;> infer_instance

private theorem local_step (selected : Bool) (query : (LocalSpec n KemSK).Domain) :
    (liftLocal (n := n) selected query).IsQueryBoundP (IsSelected (KemSK := KemSK))
      (if selected = true ∧ RegistrationNativeSecretWordLifecycleServerCaps.IsEncap query then 1 else 0) := by
  rcases query with message | (message | query) | query
  · simp [liftLocal, IsSelected, RegistrationNativeSecretWordLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]
  · simp [liftLocal, IsSelected, RegistrationNativeSecretWordLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]
  · simp [liftLocal, IsSelected, RegistrationNativeSecretWordLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]
  · rcases query with other | (pool | key)
    · simp [liftLocal, RegistrationNativeKemRouting.route, liftRoutedKem, IsSelected,
        RegistrationNativeSecretWordLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]
    · cases pool <;> simp [liftLocal, RegistrationNativeKemRouting.route, liftRoutedKem, IsSelected,
        RegistrationNativeSecretWordLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]
    · cases selected <;> simp [liftLocal, RegistrationNativeKemRouting.route, liftRoutedKem, IsSelected,
        RegistrationNativeSecretWordLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]

/-- All ordinary routing excludes the selected getter, even for an arbitrary local continuation. -/
theorem ordinary_free (work : OracleComp (LocalSpec n KemSK) Value) :
    (simulateQ (liftLocal false) work).IsQueryBoundP (IsSelected (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simpa only [Bool.false_eq_true, false_and, ite_false] using local_step false query

private theorem selected_bound (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordLifecycleServerCaps.IsEncap (KemSK := KemSK)) count) :
    (simulateQ (liftLocal true) work).IsQueryBoundP (IsSelected (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  simpa only [true_and] using local_step true query

private theorem server_free (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value) (before : State source) :
    ((RegistrationNativePublicFrontend.serverOpen false work).run before).IsQueryBoundP (IsSelected (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact ordinary_free _

private theorem beacon_free (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : State source) :
    ((RegistrationNativePublicFrontend.beacon work).run before).IsQueryBoundP (IsSelected (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePublicFrontend.beacon, StateT.run, isQueryBoundP_map_iff]
  exact ordinary_free _

private theorem record_free (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source) :
    ((RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) query).run before).IsQueryBoundP
      (IsSelected (KemSK := KemSK)) 0 := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [RegistrationNativePublicFrontend.record, StateT.run]
  all_goals try split
  all_goals simp [IsSelected, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationServerOpenReferenceCompiler.build

/-- Only the actual selected parsed attempt can spend the routed getter credit, and its entire controller costs at most one. -/
theorem handler_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (IsSelected (KemSK := KemSK)) (RegistrationNativeSecretWordLifecycleCounter.cost selectedAccept query before) := by
  cases query with
  | inl coin => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
      RegistrationNativePublicFrontend.effect, liftLocal, IsSelected, isQueryBoundP_query_iff,
      RegistrationNativeSecretWordLifecycleCounter.cost, RegistrationNativeSecretWordLifecycleCounter.increment]
  | inr query => cases query with
    | create edPin mlPin keyId => exact beacon_free _ before
    | bundle index => exact beacon_free _ before
    | finish index packet => exact beacon_free _ before
    | accept packet =>
        simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
        by_cases chosen : before.parsedAccepts = selectedAccept
        · simp only [chosen, decide_true]
          simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run, isQueryBoundP_map_iff]
          simpa only [RegistrationNativeSecretWordLifecycleCounter.cost,
            RegistrationNativeSecretWordLifecycleCounter.increment, chosen, and_self, ite_true, StateT.run] using
            selected_bound _ 1 (RegistrationNativeSecretWordLifecycleServerCaps.accept_bound
              setup checks source.verify packet before.server before.environment)
        · simp only [chosen, decide_false]
          simpa only [RegistrationNativeSecretWordLifecycleCounter.cost,
            RegistrationNativeSecretWordLifecycleCounter.increment, chosen, and_false, ite_false] using
            server_free (RegistrationServerOpenReferenceCompiler.accept setup checks source.verify packet)
              { before with parsedAccepts := before.parsedAccepts + 1 }
    | build handle application => exact server_free _ before
    | hmac key bytes => trivial
    | hash bytes => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
        RegistrationNativePublicFrontend.effect, liftLocal, IsSelected, isQueryBoundP_query_iff,
        RegistrationNativeSecretWordLifecycleCounter.cost, RegistrationNativeSecretWordLifecycleCounter.increment]
    | serverSend keyId plaintext => exact record_free (.inl (.inl (plaintext, keyId))) before
    | serverRaw bytes => exact record_free (.inl (.inr bytes)) before
    | beaconSend index plaintext => exact record_free (.inr (index, .inl plaintext)) before
    | beaconRaw index bytes => exact record_free (.inr (index, .inr bytes)) before

/-- Every actual adaptive typed program has at most one selected Server getter, independently of its query budget and all returned values. -/
theorem program_one (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State source)
    (result : (Value × State source) × Nat)
    (supported : result ∈ support ((simulateQ (monitor (IsSelected (KemSK := KemSK)))
      ((simulateQ (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before)).run 0)) :
    result.2 ≤ 1 := by
  have conserved := RegistrationNativeSecretWordLifecycleCore.program_credit
    (IsSelected (KemSK := KemSK))
    (handler setup checks wire source sign selectedOwner selectedAccept publicPrekey)
    (RegistrationNativeSecretWordLifecycleCounter.credit selectedAccept)
    (RegistrationNativeSecretWordLifecycleCounter.cost selectedAccept)
    (handler_bound setup checks wire sign selectedOwner selectedAccept publicPrekey)
    (RegistrationNativeSecretWordLifecycleCounter.query_credit setup checks wire sign selectedOwner selectedAccept publicPrekey)
    work before 0 result supported
  have cap : RegistrationNativeSecretWordLifecycleCounter.credit selectedAccept before ≤ 1 := by
    unfold RegistrationNativeSecretWordLifecycleCounter.credit RegistrationNativeSecretWordLifecycleCounter.available
    split <;> omega
  omega

/-- The complete original raw secrecy ledger, including hidden-bit/fresh draws and arbitrary invalid commands, retains that same single-getter bound. -/
theorem run_one (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source)
    (result : ((Value × RegistrationNativeLedger.State) × State source) × Nat)
    (supported : result ∈ support ((simulateQ (monitor (IsSelected (KemSK := KemSK)))
      (RegistrationNativePublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work before)).run 0)) : result.2 ≤ 1 :=
  program_one setup checks wire sign selectedOwner selectedAccept publicPrekey _ before result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServer.ordinary_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServer.ordinary_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServer.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServer.handler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServer.program_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServer.program_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServer.run_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleServer.run_one
