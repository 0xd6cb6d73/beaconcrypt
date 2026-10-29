-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBoundSource
import BeaconcryptCore.Computational.RegistrationHiddenInstall

/-! Current-pin, application and allocation admission do not inspect the selected root bytes. The actual native completion gate can therefore be evaluated on public agreement fields before sampling a root PRK; only its successful first-record continuation consumes the key schedule. Failure still returns exactly the native entry control. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationBoundGate
open RegistrationPublicationKernelErasure (mapOk)
open PqxdhSecretInputKdf (RootOutput)

/-- The actual retained post-root agreement fields, excluding its private root chain. -/
structure PublicAgreement where
  pending : pqxdh.PendingServerRegistration
  binding : session.RegistrationBinding

def atRoot (agreement : PublicAgreement) (root : RootOutput) : beaconcrypt_core.agreement.ServerAgreement :=
  ⟨agreement.pending, agreement.binding, ⟨PqxdhRootTableInitialization.rootArray root⟩⟩

def gate (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8) :
    RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState) :=
  mapOk RegistrationBoundKeySchedule.publicInitial <$>
    registration.begin_server_completion control current availability
      (atRoot agreement RegistrationBoundKeySchedule.zero) application

/-- Actual completion admission has the same public result for every private root, including all current-pin and allocator rejection paths. -/
theorem gate_root (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8)
    (root : RootOutput) :
    mapOk RegistrationBoundKeySchedule.publicInitial <$>
        registration.begin_server_completion control current availability (atRoot agreement root) application =
      gate control current availability agreement application := by
  have initial (candidate : pqxdh.ServerRegistrationCandidate) (bytes : Std.Array U8 32#usize) :
      pqxdh.concrete.start_server_candidate_ratchet_kdf candidate bytes =
        .ok (PqxdhInitialRatchetComplementarity.serverPending bytes) := by
    simpa only [pqxdh.concrete.start_server_candidate_ratchet_kdf,
      pqxdh.ServerRegistrationCandidate.ratchet_initialization,
      pqxdh.concrete.start_server_ratchet_kdf, PqxdhInitialRatchetComplementarity.serverPending] using
      pqxdh.concrete.start_server_ratchet_kdf_exact bytes
  obtain ⟨empty, emptyRun⟩ : ∃ value, core.slice.Slice.is_empty application = .ok value := ⟨_, rfl⟩
  obtain ⟨matched, matchedRun⟩ := BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total
    agreement.binding current
  obtain ⟨prepared, preparedRun⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok control
    agreement.pending current.binding availability
  cases empty <;> cases matched <;> cases prepared <;>
    simp only [gate, atRoot, registration.begin_server_completion, emptyRun, matchedRun,
      session.ServerAuthenticationPin.impl.binding, preparedRun, ratchet.RatchetChain.as_bytes,
      initial, bind_tc_ok, Bool.false_eq_true, ite_false, ite_true,
      RawCtxMaterialInterpretation.rust_map_ok, mapOk, RegistrationBoundKeySchedule.publicInitial]

theorem root_value (root : RootOutput) :
    RegistrationBoundSource.rootValue (PqxdhRootTableInitialization.rootArray root) = root := by
  apply List.Vector.toList_injective
  exact PqxdhRootTableInitialization.rootArray_bytes root

/-- The successful public native gate, followed by the actual bound record continuation. -/
def factored (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8)
    (output : PqxdhServerAuthKeySchedule.Output) :
    OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationServerRecordExecutor.continueResult
    (gate control current availability agreement application) fun initial =>
      RegistrationBoundKeySchedule.factored initial output

/-- The source's whole gate/continuation is the public native gate followed by the real selected key schedule, with no assumed gate success. -/
theorem source_begin (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8)
    (root : RootOutput) :
    RegistrationBoundSource.begin source control current availability (atRoot agreement root) application =
      factored control current availability agreement application (PqxdhServerAuthKeySchedule.fromRoot source root) := by
  unfold RegistrationBoundSource.begin factored
  simp only [atRoot, root_value]
  rw [← gate_root control current availability agreement application root]
  cases actual : registration.begin_server_completion control current availability (atRoot agreement root) application with
  | fail error =>
      simp only [atRoot] at actual
      rw [actual]
      rfl
  | div =>
      simp only [atRoot] at actual
      rw [actual]
      rfl
  | ok value =>
      simp only [atRoot] at actual
      rw [actual]
      cases value <;> rfl

/-- Actual current-pin/allocator admission and both actual64/76 callbacks reduce to the same public gate and bound continuation, retaining complete cache and auxiliary state. -/
theorem source_execute {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : PublicAgreement) (application : Slice U8)
    (root : RootOutput) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (RegistrationServerRecordExecutor.execute source writer control current availability (atRoot agreement root) application).run state =
      (simulateQ (RegistrationRecordPrimitives.implementation source writer)
        (factored control current availability agreement application (PqxdhServerAuthKeySchedule.fromRoot source root))).run state := by
  rw [RegistrationBoundSource.execute_source, source_begin]

end BeaconcryptCore.Computational.RegistrationBoundGate

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundGate.gate_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundGate.gate_root

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundGate.root_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundGate.root_value

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundGate.source_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundGate.source_begin

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundGate.source_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundGate.source_execute
