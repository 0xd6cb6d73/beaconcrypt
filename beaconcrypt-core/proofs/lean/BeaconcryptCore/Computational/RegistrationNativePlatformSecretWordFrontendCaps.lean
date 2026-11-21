-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinaryCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCaps
/-! The actual new candidate-independent frontend derives its material bill from the corrected source bodies. Builds and finishes make at most one demand; every other callback makes zero. Raw compilation retains every original mode, decision bit, ledger and mutable platform outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformSecretWordOrdinary (State)
open RegistrationNativePlatformSecretWordFrontend
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
abbrev IsDemand := RegistrationNativeSecretWordFrontendCaps.IsDemand (n := n) (KemSK := KemSK)
abbrev IsMaterial := RegistrationNativeSecretWordFrontendCaps.IsMaterial

private theorem cast_bound (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordInterpreterCaps.IsDemand (KemSK := KemSK)) cap) :
    work.IsQueryBoundP (IsDemand (KemSK := KemSK)) cap := bounded.of_imp (fun _ counted => counted)

private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordFrontendCapsLocal.IsDemand (KemSK := KemSK)) cap) :
    (simulateQ (RegistrationNativeSecretWordOwners.ordinary setup scalar) work).IsQueryBoundP
      (RegistrationNativeSecretWordFrontendCapsLocal.IsDemand (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  cases query with
  | inl message =>
    simp only [RegistrationNativeSecretWordOwners.ordinary, RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, ite_false]
    split <;> simp [RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, isQueryBoundP_query_iff]
  | inr query => rcases query with (_ | _) | _ <;>
    simp [RegistrationNativeSecretWordOwners.ordinary, RegistrationNativeSecretWordFrontendCapsLocal.IsDemand, isQueryBoundP_query_iff]

private theorem server_bound {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePlatformSecretWordOpen.PublicM (Base n KemSK Platform) A) (cap : Nat)
    (bounded : ∀ before env previous, (((work.run before).run env).run previous).IsQueryBoundP
      (RegistrationNativeSecretWordInterpreterCaps.IsDemand (KemSK := KemSK)) cap) (before : State source Platform) :
    ((serverOpen work).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) cap := by
  simp only [serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact cast_bound _ _ (bounded before.1.server before.1.environment before.2)

attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept

private theorem accept_bound (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedAccept : Nat) (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (before : State source Platform) :
    ((accept (n := n) (KemSK := KemSK) setup checks source selectedAccept reserve packet).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  simp only [accept, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
  exact server_bound _ 0 (RegistrationNativePlatformSecretWordAcceptCaps.accept_free
    (decide (before.1.parsedAccepts = selectedAccept)) reserve setup checks source.verify packet) _

private theorem finish_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform) :
    ((finish (n := n) (KemSK := KemSK) setup wire source index packet).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 1 := by
  simp only [finish, StateT.run]
  split
  · trivial
  · rename_i owner found
    rw [isQueryBoundP_map_iff]
    apply cast_bound
    apply RegistrationNativePlatformSecretWordCapsTransport.local_bound false _ 1
    cases own : owner.scalar with
    | none => exact RegistrationNativePlatformSecretWordFinishCaps.finish_bound setup wire source packet owner.view before.1.environment
    | some localScalar =>
      exact ordinary_bound setup localScalar _ 1
        (RegistrationNativePlatformSecretWordFinishCaps.finish_bound setup wire source packet owner.view before.1.environment)

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

private theorem build_bound (handle : Nat) (application : Option (Slice U8)) (before : State source Platform) :
    ((build (n := n) (KemSK := KemSK) setup sign view failure allocation erased helper writer reservePeer handle application source).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 1 := by
  simp only [build, StateT.run, isQueryBoundP_map_iff]
  apply cast_bound
  exact RegistrationNativePlatformSecretWordCapsTransport.build_embedding_bound _ 1
    (RegistrationNativePlatformSecretWordCapsTransport.body_bound setup.source view failure allocation erased helper sign writer reservePeer
      handle application before.1.server (before.1.environment.receipts, before.2))

/-- Only the actual corrected build and finish controllers consume deferred material, at most once each on every input and outcome. -/
theorem handler_bound (query : TypedSpec.Domain) (before : State source Platform) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) (if IsMaterial query then 1 else 0) := by
  by_cases ordinary : RegistrationNativePlatformSecretWordOrdinary.Ordinary query
  · rw [RegistrationNativePlatformSecretWordFrontend.ordinary setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query ordinary]
    have notMaterial : ¬ IsMaterial query := by
      cases query with
      | inl coin => exact id
      | inr query => cases query <;> first | exact id | exact ordinary.elim
    rw [ite_eq_right notMaterial]
    exact cast_bound _ _ (RegistrationNativePlatformSecretWordOrdinaryCaps.handler_free setup source selectedOwner publicPrekey reserveFrame writer query before)
  · cases query with
    | inl coin => exact (ordinary trivial).elim
    | inr query => cases query <;> first
      | exact (ordinary trivial).elim
      | exact accept_bound setup checks source selectedAccept reserveRegistration _ before
      | exact build_bound (setup := setup) (source := source) (sign := sign) (view := view) (failure := failure) (allocation := allocation)
          (erased := erased) (helper := helper) (writer := writer) (reservePeer := reservePeer) _ _ before
      | exact finish_bound setup wire source _ _ before

/-- The actual adaptive Word tree inherits its original material-command cap with full platform state and all failed calls retained. -/
theorem program_bound (work : OracleComp TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP IsMaterial cap) (before : State source Platform) :
    ((simulateQ (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current
  · intro query free current
    simpa only [ite_eq_right free] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current

/-- Canonical raw compilation derives qBuild+qFinish demands from the original native budget, with no new whole-client allowance premise. -/
theorem run_bound (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : State source Platform) :
    (run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
  apply program_bound setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer _ _ _ before
  have bill := RegistrationNativeMaterialBudget.compile_bound setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    serverKeyId bounds mode work budget bounded
  rw [RegistrationNativeMaterialBudget.allowance_eq] at bill
  apply OracleComp.IsQueryBoundP.of_imp _ bill
  intro query counted
  cases query with
  | inl coin => exact counted.elim
  | inr query => cases query <;> simp_all [IsMaterial, RegistrationNativeSecretWordFrontendCaps.IsMaterial,
      RegistrationNativeMaterialBudget.IsMaterial, RegistrationNativeRawAdapter.kind]

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps.handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps.run_bound
