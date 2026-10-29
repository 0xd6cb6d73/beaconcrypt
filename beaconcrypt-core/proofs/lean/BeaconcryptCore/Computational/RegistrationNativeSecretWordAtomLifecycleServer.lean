-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServerCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCounter

/-! The actual selected routed Server getter occurs at most once over every adaptive original native client. The parsed ordinal is consumed before authentication, and the one selected controller has only one encapsulation position. A ghost monitor retains the complete original computation and counts actual exposed KEM queries, including all failures and original hidden-ledger draws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServer
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordInterface (Spec LocalSpec liftLocal)
open RegistrationNativeSecretWordMessage (State)
open RegistrationNativeSecretWordFrontend (M handler)
open RegistrationNativeSecretWordLifecycleCore (monitor)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev increment := RegistrationNativeSecretWordTargetCounter.isAccept
abbrev available := RegistrationNativeSecretWordLifecycleCounter.available

def credit (selected : Nat) (before : State source) : Nat := available selected before.parsedAccepts

def cost (selected : Nat) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) : Nat :=
  if (increment query).toNat = 1 ∧ before.parsedAccepts = selected then 1 else 0

private theorem ordinal_credit (before selected step : Nat) (_unit : step = 0 ∨ step = 1) :
    available selected (before + step) + (if step = 1 ∧ before = selected then 1 else 0) ≤ available selected before := by
  simp only [available, RegistrationNativeSecretWordLifecycleCounter.available]
  split_ifs <;> omega

private theorem query_credit (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (supported : result ∈ support ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)) :
    credit selectedAccept result.2 + cost selectedAccept query before ≤ credit selectedAccept before := by
  have advanced := RegistrationNativeSecretWordTargetCounter.typed_counter setup checks wire sign selectedOwner selectedAccept publicPrekey query before result supported
  change available selectedAccept result.2.parsedAccepts +
      (if (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat = 1 ∧ before.parsedAccepts = selectedAccept then 1 else 0) ≤
    available selectedAccept before.parsedAccepts
  rw [advanced]
  apply ordinal_credit
  cases RegistrationNativeSecretWordTargetCounter.isAccept query <;> first | exact Or.inl rfl | exact Or.inr rfl

def IsSelected : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inr (.inr (.inr _)))) => True
  | _ => False
instance : DecidablePred (IsSelected (n := n) (KemSK := KemSK)) := fun query => by
  unfold IsSelected
  split <;> infer_instance

private theorem local_step (selected : Bool) (query : (LocalSpec n KemSK).Domain) :
    (liftLocal (n := n) selected query).IsQueryBoundP (IsSelected (KemSK := KemSK))
      (if selected = true ∧ RegistrationNativeSecretWordAtomLifecycleServerCaps.IsEncap query then 1 else 0) := by
  rcases query with message | (message | query) | query
  · simp [liftLocal, IsSelected, RegistrationNativeSecretWordAtomLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]
  · simp [liftLocal, IsSelected, RegistrationNativeSecretWordAtomLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]
  · simp [liftLocal, IsSelected, RegistrationNativeSecretWordAtomLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]
  · rcases query with other | (pool | key)
    · simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem, IsSelected,
        RegistrationNativeSecretWordAtomLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]
    · cases pool <;> simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem, IsSelected,
        RegistrationNativeSecretWordAtomLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]
    · cases selected <;> simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem, IsSelected,
        RegistrationNativeSecretWordAtomLifecycleServerCaps.IsEncap, isQueryBoundP_query_iff]

/-- All ordinary routing excludes the selected getter, even for an arbitrary local continuation. -/
theorem ordinary_free (work : OracleComp (LocalSpec n KemSK) Value) :
    (simulateQ (liftLocal false) work).IsQueryBoundP (IsSelected (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simpa only [Bool.false_eq_true, false_and, ite_false] using local_step false query

private theorem selected_bound (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordAtomLifecycleServerCaps.IsEncap (KemSK := KemSK)) count) :
    (simulateQ (liftLocal true) work).IsQueryBoundP (IsSelected (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  simpa only [true_and] using local_step true query

private theorem server_free (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value) (before : State source) :
    ((RegistrationNativeSecretWordFrontend.serverOpen false work).run before).IsQueryBoundP (IsSelected (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact ordinary_free _

private theorem beacon_free (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : State source) :
    ((RegistrationNativeSecretWordFrontend.beacon work).run before).IsQueryBoundP (IsSelected (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordFrontend.beacon, StateT.run, isQueryBoundP_map_iff]
  exact ordinary_free _

private theorem record_free (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source) :
    ((RegistrationNativeSecretWordFrontend.record (n := n) (KemSK := KemSK) query).run before).IsQueryBoundP
      (IsSelected (KemSK := KemSK)) 0 := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [RegistrationNativeSecretWordFrontend.record, StateT.run]
  all_goals try split
  all_goals simp [IsSelected, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

/-- Only the actual selected parsed attempt can spend the routed getter credit, and its entire controller costs at most one. -/
theorem handler_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (IsSelected (KemSK := KemSK)) (cost selectedAccept query before) := by
  cases query with
  | inl coin => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
      RegistrationNativeSecretWordFrontend.effect, IsSelected, isQueryBoundP_query_iff,
      cost, RegistrationNativeSecretWordTargetCounter.isAccept]
  | inr query => cases query with
    | create edPin mlPin keyId => exact beacon_free _ before
    | bundle index => exact beacon_free _ before
    | finish index packet => exact beacon_free _ before
    | accept packet =>
        simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
        by_cases chosen : before.parsedAccepts = selectedAccept
        · simp only [chosen, decide_true]
          simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, isQueryBoundP_map_iff]
          simpa [cost, increment, RegistrationNativeSecretWordTargetCounter.isAccept, chosen, StateT.run] using
            selected_bound _ 1 (RegistrationNativeSecretWordAtomLifecycleServerCaps.accept_bound
              setup checks source.verify packet before.server before.environment)
        · simp only [chosen, decide_false]
          simpa only [cost, increment, RegistrationNativeSecretWordTargetCounter.isAccept, chosen, and_false, ite_false] using
            server_free (RegistrationNativeSecretWordServerCompiler.accept setup checks source.verify packet)
              { before with parsedAccepts := before.parsedAccepts + 1 }
    | build handle application => exact server_free _ before
    | hmac key bytes => trivial
    | hash bytes => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
        RegistrationNativeSecretWordFrontend.effect, IsSelected, isQueryBoundP_query_iff,
        cost, RegistrationNativeSecretWordTargetCounter.isAccept]
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
    (credit selectedAccept)
    (cost selectedAccept)
    (handler_bound setup checks wire sign selectedOwner selectedAccept publicPrekey)
    (query_credit setup checks wire sign selectedOwner selectedAccept publicPrekey)
    work before 0 result supported
  have cap : credit selectedAccept before ≤ 1 := by
    simp only [credit, available, RegistrationNativeSecretWordLifecycleCounter.available]
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
      (RegistrationNativeSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work before)).run 0)) : result.2 ≤ 1 :=
  program_one setup checks wire sign selectedOwner selectedAccept publicPrekey _ before result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServer.ordinary_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServer.ordinary_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServer.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServer.handler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServer.program_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServer.program_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServer.run_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomLifecycleServer.run_one
