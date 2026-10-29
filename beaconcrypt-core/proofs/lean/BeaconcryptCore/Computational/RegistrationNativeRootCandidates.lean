-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG2Candidates
import BeaconcryptCore.Computational.RegistrationNativePublicPrepareCaps
import BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame
import BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting

/-! The actual G1 frontend yields its chronological supplied-first candidates after generated startup and the original full secrecy ledger. The executable prefix receives only the public challenge; neither selected Server seed nor selected prekey scalar is an argument. Its root preparations and returned candidate count derive from the original accept/finish budget. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRootCandidates
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRelatedRoot (RootSpec)
open RegistrationNativePublicInterpreter (State)
open PqxdhJointIdentity (DhOutput)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsRootDerive : RootSpec.Domain → Prop
  | .inr (.derive _) => True
  | _ => False
instance : DecidablePred IsRootDerive := fun query => by
  cases query with
  | inl _ => exact isFalse id
  | inr request => cases request <;> first | exact isTrue trivial | exact isFalse id

noncomputable def work (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (selectedOwner selectedAccept : Nat)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (started : RegistrationNativePublicStartup.Started source) :
    OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)
      ((Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source) :=
  RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source started.credential)
    selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
    (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) started.frontend

noncomputable def rootClient (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp RootSpec (List DhOutput) := do
  let initialized ← (RegistrationNativePublicStartup.start (n := n) setup source ensureInit identityIndex serverKeyId
    publicValue.identity).run RegistrationNativePublicInterpreter.initial
  match initialized.1 with
  | none => pure []
  | some started =>
      (fun result => RegistrationNativeG2Candidates.candidates result.1.2) <$>
        (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route (RegistrationNativeMldsa.owned source started.credential))
          (RegistrationNativeG2Trace.program
            (work setup checks wire source selectedOwner selectedAccept publicValue serverKeyId bounds mode adversary started))).run initialized.2

noncomputable def familyClient (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp RegistrationNativeRelatedFamily.Spec (List DhOutput) :=
  simulateQ RegistrationNativeRelatedRoot.reduction
    (rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
      bounds mode adversary publicValue)

private theorem derive_of_free {Result : Type} (program : OracleComp RootSpec Result)
    (bounded : program.IsQueryBoundP RegistrationNativePublicRootFrame.IsRoot 0) :
    program.IsQueryBoundP IsRootDerive 0 := by
  apply OracleComp.IsQueryBoundP.of_imp _ bounded
  intro query counted
  cases query with
  | inl coin => exact counted.elim
  | inr request => trivial

private theorem query_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State n KemSK) :
    ((RegistrationNativePublicInterpreter.handler setup wire route sign query).run before).IsQueryBoundP IsRootDerive
      (if RegistrationNativePublicPrepareCaps.IsPrepare (KemSK := KemSK) query then 1 else 0) := by
  rcases query with (message | (message | query) | query) | query
  · rw [RegistrationNativePublicInterpreter.prepare_query]
    simp [IsRootDerive, RegistrationNativePublicPrepareCaps.IsPrepare]
  · simp [RegistrationNativePublicInterpreter.handler, StateT.run_get,
      RegistrationNativePublicPrepareCaps.IsPrepare]
  · exact derive_of_free _ (RegistrationNativePublicRootFrame.common_free setup wire sign query before)
  · exact derive_of_free _ (RegistrationNativePublicRootFrame.routed_free setup query before)
  · exact derive_of_free _ (RegistrationNativePublicRootFrame.world_free _ before)

/-- The actual G1 interpreter queries its root service once per preparation and nowhere else. -/
theorem interpreted_bound {Result : Type} (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (program : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Result) (count : Nat)
    (bounded : program.IsQueryBoundP (RegistrationNativePublicPrepareCaps.IsPrepare (KemSK := KemSK)) count)
    (before : State n KemSK) :
    ((simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) program).run before).IsQueryBoundP
      IsRootDerive count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using query_bound setup wire route sign query current
  · intro query free current
    simpa only [ite_eq_right free] using query_bound setup wire route sign query current

/-- Generated native startup adds no root derives; the full original ledger supplies the actual accept-plus-finish cap. -/
theorem root_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) :
    (rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
      bounds mode adversary publicValue).IsQueryBoundP IsRootDerive (budget.cap 3 + budget.cap 5) := by
  unfold rootClient
  rw [← Nat.zero_add (budget.cap 3 + budget.cap 5)]
  apply isQueryBoundP_bind (n := 0) (m := budget.cap 3 + budget.cap 5)
    (derive_of_free _ (RegistrationNativePublicStartupFrame.start_free setup source ensureInit identityIndex serverKeyId
      publicValue.identity RegistrationNativePublicInterpreter.initial))
  intro initialized _
  cases initialized.1 with
  | none => trivial
  | some started =>
      rw [isQueryBoundP_map_iff]
      apply interpreted_bound
      exact RegistrationNativeG2Trace.program_bound _ _ _
        (RegistrationNativePublicPrepareCaps.run_bound setup checks wire source (RegistrationNativeMldsa.owned source started.credential)
          selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
          (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) budget (bounded _) started.frontend)
        RegistrationNativeG2Trace.initial

/-- Every actual returned candidate is counted by a preparation, even when its native root preparation was rejected. -/
theorem root_length (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) (candidates : List DhOutput)
    (supported : candidates ∈ support (rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary publicValue)) :
    candidates.length ≤ budget.cap 3 + budget.cap 5 := by
  simp only [rootClient, mem_support_bind_iff] at supported
  obtain ⟨initialized, _started, continued⟩ := supported
  cases found : initialized.1 with
  | none => simp only [found, mem_support_pure_iff] at continued; cases continued; exact Nat.zero_le _
  | some started =>
      simp only [found] at continued
      rw [support_map] at continued
      obtain ⟨result, actual, equal⟩ := continued
      cases equal
      have original : result.1 ∈ support (RegistrationNativeG2Trace.program
          (work (n := n) setup checks wire source selectedOwner selectedAccept publicValue serverKeyId bounds mode adversary started)) := by
        apply support_simulateQ_run'_subset (RegistrationNativePublicInterpreter.handler setup wire route
          (RegistrationNativeMldsa.owned source started.credential)) _ initialized.2
        rw [StateT.run'_eq, support_map]
        exact ⟨result, actual, rfl⟩
      exact RegistrationNativeG2Candidates.candidate_bound _ (budget.cap 3 + budget.cap 5)
        (RegistrationNativePublicPrepareCaps.run_bound setup checks wire source (RegistrationNativeMldsa.owned source started.credential)
          selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
          (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) budget (bounded _) started.frontend)
        result.1 original

end BeaconcryptCore.Computational.RegistrationNativeRootCandidates
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCandidates.interpreted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCandidates.interpreted_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCandidates.root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCandidates.root_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCandidates.root_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCandidates.root_length
