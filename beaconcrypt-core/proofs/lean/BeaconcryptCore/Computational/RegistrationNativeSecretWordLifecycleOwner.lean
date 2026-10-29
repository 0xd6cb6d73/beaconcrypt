-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps

/-! The actual selected local finish role makes at most one indexed decapsulation over the whole original adaptive ledger. The role tag is erased without changing any source query or final state. Only actual terminal consumption spends its credit; future create/bundle calls cannot restore it. Opaque handle provenance is retained in the concrete getter equation and is not assumed equal to an owner index. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicFrontend (State LocalSpec)
open RegistrationNativeSecretWordLifecycleTags (Spec tag erase handler OwnerDecap)
open RegistrationNativeSecretWordLifecycleCore (monitor)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def NativeDecap : (RegistrationNativePublicFrontend.Spec n KemSK).Domain → Prop
  | .inl (.inr (.inr (.inr (.inl (.decapsulate _ _))))) => True
  | _ => False
instance : DecidablePred (NativeDecap (n := n) (KemSK := KemSK)) := fun query => by
  unfold NativeDecap
  split <;> infer_instance

private theorem tag_predicate (chosen : Bool) (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) :
    OwnerDecap (chosen, query) ↔ chosen = true ∧ NativeDecap query := by
  cases chosen <;> rcases query with (message | (message | query) | ((other | key) | (pool | key))) | record
  all_goals try cases pool
  all_goals simp only [OwnerDecap, NativeDecap, Bool.false_eq_true, false_and, true_and]

private theorem tag_step (chosen : Bool) (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) :
    (tag chosen query).IsQueryBoundP (OwnerDecap (KemSK := KemSK))
      (if chosen = true ∧ NativeDecap query then 1 else 0) := by
  simp only [tag, isQueryBoundP_query_iff, tag_predicate]
  intro charged
  simp only [ite_eq_left charged]
  decide

/-- Queries from every other original command have no selected-owner role tag. -/
theorem other_role_free (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) :
    (simulateQ (tag false) work).IsQueryBoundP (OwnerDecap (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simpa only [Bool.false_eq_true, false_and, ite_false] using tag_step false query

private theorem tag_bound (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (NativeDecap (KemSK := KemSK)) cap) :
    (simulateQ (tag true) work).IsQueryBoundP (OwnerDecap (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  simpa only [true_and] using tag_step true query

private theorem local_step (chosen : Bool) (query : (LocalSpec n KemSK).Domain) :
    (RegistrationNativePublicFrontend.liftLocal chosen query).IsQueryBoundP (NativeDecap (KemSK := KemSK))
      (if RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap query then 1 else 0) := by
  rcases query with message | (message | query) | query
  · simp [RegistrationNativePublicFrontend.liftLocal, NativeDecap,
      RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap, isQueryBoundP_query_iff]
  · simp [RegistrationNativePublicFrontend.liftLocal, NativeDecap,
      RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap, isQueryBoundP_query_iff]
  · simp [RegistrationNativePublicFrontend.liftLocal, NativeDecap,
      RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap, isQueryBoundP_query_iff]
  · rcases query with other | (pool | key)
    · simp [RegistrationNativePublicFrontend.liftLocal, RegistrationNativeKemRouting.route,
        RegistrationNativePublicFrontend.liftRoutedKem, NativeDecap,
        RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap, isQueryBoundP_query_iff]
    · cases pool <;> simp [RegistrationNativePublicFrontend.liftLocal, RegistrationNativeKemRouting.route,
        RegistrationNativePublicFrontend.liftRoutedKem, NativeDecap,
        RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap, isQueryBoundP_query_iff]
    · cases chosen <;> simp [RegistrationNativePublicFrontend.liftLocal, RegistrationNativeKemRouting.route,
        RegistrationNativePublicFrontend.liftRoutedKem, NativeDecap,
        RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap, isQueryBoundP_query_iff]

private theorem local_bound (chosen : Bool) (work : OracleComp (LocalSpec n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap (KemSK := KemSK)) cap) :
    (simulateQ (RegistrationNativePublicFrontend.liftLocal chosen) work).IsQueryBoundP (NativeDecap (KemSK := KemSK)) cap :=
  RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded (local_step chosen)

private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (LocalSpec n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap (KemSK := KemSK)) cap) :
    (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work).IsQueryBoundP
      (RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  cases query with
  | inl message =>
      simp only [RegistrationNativePublicOwners.ordinary, RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap]
      split <;> simp [RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap, isQueryBoundP_query_iff]
  | inr query =>
      simp only [RegistrationNativePublicOwners.ordinary, isQueryBoundP_query_iff]
      intro charged
      simp only [ite_eq_left charged]
      decide

private theorem owners_finish_bound (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run env).IsQueryBoundP
      (RegistrationNativeSecretWordLifecycleBeaconCaps.IsDecap (KemSK := KemSK))
      (match owners[index]? with
        | none => 0
        | some owner => if RegistrationNativeSecretWordLifecycleOwnerCredit.canFinish owner.view.phase then 1 else 0) := by
  simp only [RegistrationNativePublicOwners.finish, StateT.run]
  cases found : owners[index]? with
  | none => trivial
  | some owner =>
      rw [isQueryBoundP_map_iff]
      cases chosen : owner.scalar with
      | none => simpa only [StateT.run] using RegistrationNativeSecretWordLifecycleBeaconCaps.finish_bound setup source packet owner.view env
      | some scalar =>
          apply ordinary_bound setup scalar _ _
          simpa only [StateT.run] using RegistrationNativeSecretWordLifecycleBeaconCaps.finish_bound setup source packet owner.view env

attribute [local irreducible] RegistrationNativePublicFrontend.handler

/-- The actual selected finish command spends one role credit only after its real terminal gate; all other original commands are untagged. -/
theorem handler_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) :
    ((handler (n := n) setup checks wire sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (OwnerDecap (KemSK := KemSK)) (RegistrationNativeSecretWordLifecycleOwnerCredit.cost selectedOwner query before) := by
  cases query with
  | inl coin => exact other_role_free _
  | inr query =>
      cases query with
      | finish index packet =>
          by_cases chosen : index = selectedOwner
          · subst index
            simp only [handler, RegistrationNativeSecretWordLifecycleTags.selectedFinish, decide_true,
              StateT.run, RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon,
              simulateQ_map, isQueryBoundP_map_iff]
            apply tag_bound
            simp only [RegistrationNativeSecretWordLifecycleOwnerCredit.cost, ite_true]
            exact local_bound false _ _ (owners_finish_bound setup selectedOwner packet before.beacons before.environment)
          · simpa only [handler, RegistrationNativeSecretWordLifecycleTags.selectedFinish, chosen, decide_false,
              StateT.run, RegistrationNativeSecretWordLifecycleOwnerCredit.cost, ite_false] using
              other_role_free (n := n) (KemSK := KemSK)
                ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
                  (.inr (.finish index packet))).run before)
      | _ => exact other_role_free _

private theorem handler_credit (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (supported : result ∈ support ((handler (n := n) setup checks wire sign selectedOwner selectedAccept publicPrekey query).run before)) :
    RegistrationNativeSecretWordLifecycleOwnerCredit.credit selectedOwner result.2 +
        RegistrationNativeSecretWordLifecycleOwnerCredit.cost selectedOwner query before ≤
      RegistrationNativeSecretWordLifecycleOwnerCredit.credit selectedOwner before := by
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  exact RegistrationNativeSecretWordLifecycleOwnerCredit.query_credit setup checks wire sign selectedOwner selectedAccept publicPrekey
    query before result original

/-- Every adaptive original typed program makes at most one indexed decapsulation in the selected local owner role. -/
theorem program_one (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State source)
    (result : (Value × State source) × Nat)
    (supported : result ∈ support ((simulateQ (monitor (OwnerDecap (KemSK := KemSK)))
      ((simulateQ (handler (n := n) setup checks wire sign selectedOwner selectedAccept publicPrekey) work).run before)).run 0)) :
    result.2 ≤ 1 := by
  have conserved := RegistrationNativeSecretWordLifecycleCore.program_credit
    (OwnerDecap (KemSK := KemSK)) (handler setup checks wire sign selectedOwner selectedAccept publicPrekey)
    (RegistrationNativeSecretWordLifecycleOwnerCredit.credit selectedOwner)
    (RegistrationNativeSecretWordLifecycleOwnerCredit.cost selectedOwner)
    (handler_bound setup checks wire sign selectedOwner selectedAccept publicPrekey)
    (handler_credit setup checks wire sign selectedOwner selectedAccept publicPrekey)
    work before 0 result supported
  have cap := RegistrationNativeSecretWordLifecycleOwnerCredit.credit_le selectedOwner before
  omega

/-- The whole original secrecy ledger retains that same single selected-owner role cap, with no timing, event or query-budget restriction. -/
theorem run_one (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source)
    (result : ((Value × RegistrationNativeLedger.State) × State source) × Nat)
    (supported : result ∈ support ((simulateQ (monitor (OwnerDecap (KemSK := KemSK)))
      (RegistrationNativeSecretWordLifecycleTags.run (n := n) setup checks wire sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work before)).run 0)) : result.2 ≤ 1 :=
  program_one setup checks wire sign selectedOwner selectedAccept publicPrekey _ before result supported

/-- Dropping only the role counter and ghost tags restores the literal complete original secrecy computation. -/
theorem run_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source) :
    simulateQ erase (Prod.fst <$> (simulateQ (monitor (OwnerDecap (KemSK := KemSK)))
      (RegistrationNativeSecretWordLifecycleTags.run (n := n) setup checks wire sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work before)).run 0) =
      RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work before := by
  rw [RegistrationNativeSecretWordLifecycleCore.erased, RegistrationNativeSecretWordLifecycleTags.run_source]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner.other_role_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner.other_role_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner.handler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner.program_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner.program_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner.run_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner.run_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwner.run_source
