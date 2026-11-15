-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaChronology

/-! Actual reified Server build callbacks preserve the chronological raw primitive-attempt/native-payload relation. Native record, pin, occupancy, moved-token and insertion effects cannot edit prior ML receipts; actual source hash/sign continuations derive the new request alignment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaServerChronology
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaTableProgram (runState evaluate)
open RegistrationNativeMldsaChronology (Aligned)
open RegistrationSigningShared (Receipt)
open PqxdhServerAuthExperiment (Setup Codec Checks)
variable {n : Nat} {State Value Next Auxiliary Encoded ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before
private theorem state_pure_apply {S A : Type} {m : Type → Type} [Monad m]
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl

private def Keeps (receipts : State → List Receipt)
    (work : StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Value) : Prop :=
  ∀ before pool result, Aligned pool.signing (receipts before) →
    result ∈ support (runState source work before pool) → Aligned result.2.signing (receipts result.1.2)
private theorem pure_keeps (receipts : State → List Receipt) (value : Value) :
    Keeps source receipts (pure value : StateT State _ Value) := by
  intro before pool result aligned supported
  rw [RegistrationNativeMldsaTableProgram.run_pure] at supported
  simp only [support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact aligned
private theorem bind_keeps (receipts : State → List Receipt)
    (work : StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Value)
    (next : Value → StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Next)
    (first : Keeps source receipts work) (rest : ∀ value, Keeps source receipts (next value)) : Keeps source receipts (work >>= next) := by
  intro before pool result aligned supported
  rw [RegistrationNativeMldsaTableProgram.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first before pool middle aligned queried) continued
private theorem lift_keeps (receipts : State → List Receipt) (work : StateT State ProbComp Value)
    (same : ∀ before result, result ∈ support (work.run before) → receipts result.2 = receipts before) :
    Keeps source receipts (RegistrationNativeMldsaProgram.liftState work) := by
  intro before pool result aligned supported
  rw [RegistrationNativeMldsaTableProgram.run_liftState, support_map] at supported
  obtain ⟨reached, possible, equality⟩ := supported
  cases equality
  rw [same before reached possible]
  exact aligned

private theorem shared_receipts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : MldsaSharedNative.Spec.Range query × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.shared setup codec query).run before)) :
    result.2.world.2 = before.world.2 := by
  cases query with
  | inl query =>
      simp only [RegistrationWorldRecords.shared, StateT.run, support_map] at supported
      obtain ⟨inner, _possible, same⟩ := supported
      cases same
      rfl
  | inr query =>
      simp only [RegistrationWorldRecords.shared, RegistrationWorldRecords.record, StateT.run, support_map] at supported
      obtain ⟨inner, _possible, same⟩ := supported
      cases same
      rfl
private theorem shared_program_receipts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp MldsaSharedNative.Spec Value) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : Value × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationWorldRecords.shared setup codec) work).run before)) :
    result.2.world.2 = before.world.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact (ih middle.1 middle.2 result continued).trans (shared_receipts setup codec query before middle queried)
private theorem record_receipts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : RegistrationRecordPrimitives.Spec.Range query × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.handler setup codec query).run before)) :
    result.2.world.2 = before.world.2 := by
  simp only [RegistrationWorldRecords.handler, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact shared_program_receipts setup codec (RegistrationRecordPrimitives.callbacks setup.source query) before inner possible
private theorem records_receipts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : Value × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationWorldRecords.handler setup codec) work).run before)) :
    result.2.world.2 = before.world.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact (ih middle.1 middle.2 result continued).trans (record_receipts setup codec query before middle queried)

private theorem capability_receipts (query : PqxdhRecordLiftInterface.Capability n)
    (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : (PqxdhRecordLiftInterface.CapabilitySpec n).Range query × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.capability query).run before)) :
    result.2.world.2 = before.world.2 := by
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl
/-- Response-dependent hashing retain exactly the existing Server signing history. -/
private theorem adHash_receipts (pending : registration.ServerAdHash)
    (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : RustM (core.result.Result registration.ServerInitialKdf pqxdh.ServerState) × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.adHash pending).run before)) :
    result.2.world.2 = before.world.2 := by
  unfold RegistrationWorldServerCompletion.adHash at supported
  cases requested : pending.request with
  | fail error | div =>
      simp only [requested, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok request =>
      simp only [requested, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨hashed, called, returned⟩ := supported
      simp only [StateT.run_pure, mem_support_pure_iff] at returned
      cases returned
      exact capability_receipts _ before hashed called

private theorem install_receipts (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : RustM (RegistrationWorldServerCompletion.Result Encoded) × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.install control published).run before)) :
    result.2.world.2 = before.world.2 := by
  obtain ⟨prepared, preparedRun, _fields⟩ := BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains control published
  cases prepared with
  | Err previous =>
      simp only [RegistrationWorldServerCompletion.install, preparedRun] at supported
      change result ∈ support (pure ((.ok (.Err previous) : RustM (RegistrationWorldServerCompletion.Result Encoded)), before) :
        ProbComp (RustM (RegistrationWorldServerCompletion.Result Encoded) × RegistrationWorldAgreement.State n Auxiliary)) at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | Ok pending =>
      rw [RegistrationWorldServerCompletion.install_native control published pending preparedRun,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, inserted, returned⟩ := supported
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at returned
      cases returned
      exact capability_receipts _ before middle inserted

variable (credential : RegistrationNativeMldsa.Credential (handleSource source))

/-- Actual source response publication derives its request alignment and preserves positionwise raw/native signing history through every outcome. -/
theorem signing (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (before : RegistrationWorldAgreement.State n Auxiliary) (pool : Pool source)
    (result : (RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationWorldAgreement.State n Auxiliary) × Pool source)
    (aligned : Aligned pool.signing before.world.2)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaServer.signing (handleSource source) credential encode pending) before pool)) :
    Aligned result.2.signing result.1.2.world.2 := by
  simp only [RegistrationNativeMldsaServer.signing, StateT.run, runState, evaluate, simulateQ_map, map_apply, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact RegistrationNativeMldsaChronology.Server.program source credential _
    (RegistrationNativeMldsaRequestAlignment.Server.program_all encode pending) before.world pool inner aligned possible

private theorem publish_keeps (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash) :
    Keeps source (fun before : RegistrationWorldAgreement.State n Auxiliary => before.world.2)
      (RegistrationNativeMldsaServer.publish (handleSource source) credential encode control pending) := by
  unfold RegistrationNativeMldsaServer.publish
  apply bind_keeps source _ _ _ (signing source credential encode pending)
  intro reply
  cases reply with
  | fail error | div => exact pure_keeps source _ _
  | ok answer => cases answer with
    | Err previous => exact pure_keeps source _ _
    | Ok published => exact lift_keeps source _ _ (install_receipts control published)

/-- The whole actual initial-record, signing and peer insertion continuation retains every primitive signing attempt/native receipt correspondence. -/
theorem completionFromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) (before : RegistrationWorldAgreement.State n Auxiliary) (pool : Pool source)
    (result : (RustM (RegistrationWorldServerCompletion.Result Encoded) × RegistrationWorldAgreement.State n Auxiliary) × Pool source)
    (aligned : Aligned pool.signing before.world.2)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaServer.completionFromInitial (handleSource source) credential setup codec encode control pending) before pool)) :
    Aligned result.2.signing result.1.2.world.2 := by
  have law : Keeps source (fun before : RegistrationWorldAgreement.State n Auxiliary => before.world.2)
      (RegistrationNativeMldsaServer.completionFromInitial (handleSource source) credential setup codec encode control pending) := by
    unfold RegistrationNativeMldsaServer.completionFromInitial
    apply bind_keeps source _ _ _ (lift_keeps source _ _ (records_receipts setup codec _))
    intro reply
    cases reply with
    | fail error | div => exact pure_keeps source _ _
    | ok answer => cases answer with
      | Err previous => exact pure_keeps source _ _
      | Ok pending => exact publish_keeps source credential encode control pending
  exact law before pool result aligned supported

namespace SDK
private def receipts (before : RegistrationServerFrontendCompiler.State n) : List Receipt := before.world.world.2

private theorem world_keeps
    (work : StateT (RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
      (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Value)
    (law : Keeps source (fun before => before.world.2) work) :
    Keeps source receipts (RegistrationNativeMldsaServer.world (handleSource source) work) := by
  intro before pool result aligned supported
  simp only [RegistrationNativeMldsaServer.world, StateT.run, runState, evaluate,
    simulateQ_map, map_apply, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact law before.world pool inner aligned possible

private theorem commit_receipts (reply : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes))
    (before : RegistrationServerFrontendCompiler.State n)
    (result : RustM (Option (Std.U64 × Pqxdh.Bytes)) × RegistrationServerFrontendCompiler.State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.commit reply).run before)) :
    receipts result.2 = receipts before := by
  cases reply with
  | fail error | div =>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | ok answer => cases answer <;>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at supported <;>
      cases supported <;> rfl

private theorem fromInitial_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Keeps source receipts (RegistrationNativeMldsaServer.fromInitial (n := n) (handleSource source)
      credential setup codec encode control pending) := by
  unfold RegistrationNativeMldsaServer.fromInitial
  apply bind_keeps source _ _ _ (world_keeps source _ (completionFromInitial source credential setup codec encode control pending))
  intro reply
  exact lift_keeps source receipts _ (commit_receipts reply)

private theorem sdk_adHash_receipts (pending : registration.ServerAdHash)
    (before : RegistrationServerFrontendCompiler.State n)
    (result : RustM (core.result.Result registration.ServerInitialKdf pqxdh.ServerState) × RegistrationServerFrontendCompiler.State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.adHash pending).run before)) :
    receipts result.2 = receipts before := by
  simp only [RegistrationServerSdkSource.adHash, RegistrationServerSdkSource.world, StateT.run, support_map] at supported
  obtain ⟨inner, actual, same⟩ := supported
  cases same
  exact adHash_receipts pending before.world inner actual

private theorem afterOccupancy_keeps (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Keeps source receipts (RegistrationNativeMldsaServer.afterOccupancy (n := n) (handleSource source)
      credential setup codec checks encode control lookup occupied) := by
  unfold RegistrationNativeMldsaServer.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_keeps source receipts _
  | ok answer => cases answer with
    | Err previous => exact pure_keeps source receipts _
    | Ok pending =>
        apply bind_keeps source receipts _ _ (lift_keeps source receipts _ (sdk_adHash_receipts pending))
        intro hashed
        cases hashed with
        | fail error | div => exact pure_keeps source receipts _
        | ok result => cases result with
          | Err previous => exact pure_keeps source receipts _
          | Ok initial =>
              cases reserved : checks.reservePeer with
              | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  exact pure_keeps source receipts _
              | true =>
                  simp only [ite_true]
                  exact fromInitial_keeps source credential setup codec encode control initial

private theorem pure_at (value : Value) (current : State) (pool : Pool source)
    (receipts : State → List Receipt)
    (result : (Value × State) × Pool source) (aligned : Aligned pool.signing (receipts current))
    (supported : result ∈ support (evaluate source (pure (value, current)) pool)) :
    Aligned result.2.signing (receipts result.1.2) := by
  simp only [evaluate, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact aligned

private theorem complete_keeps (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Keeps source receipts (RegistrationNativeMldsaServer.complete (n := n) (handleSource source)
      credential setup codec checks encode token application) := by
  intro before pool result aligned supported
  simp only [RegistrationNativeMldsaServer.complete, StateT.run, runState] at supported
  cases looked : peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div =>
      simp only [looked] at supported
      exact pure_at source _ before pool receipts result aligned supported
  | ok answer => cases answer with
    | Err previous =>
        simp only [looked] at supported
        exact pure_at source _ before pool receipts result aligned supported
    | Ok lookup =>
        simp only [looked] at supported
        cases requested : lookup.request with
        | fail error | div =>
            simp only [requested] at supported
            exact pure_at source _ before pool receipts result aligned supported
        | ok keyId =>
            simp only [requested] at supported
            split_ifs at supported with fits
            · change result ∈ support (runState source (do
                let occupied ← RegistrationNativeMldsaServer.world (handleSource source)
                  (RegistrationNativeMldsaProgram.liftState (RegistrationWorldServerCompletion.capability (.peerPresent keyId)))
                RegistrationNativeMldsaServer.afterOccupancy (handleSource source) credential setup codec checks encode before.control lookup occupied)
                  before pool) at supported
              exact bind_keeps source receipts _ _
                (world_keeps source _ (lift_keeps source _ _ (capability_receipts (.peerPresent keyId))))
                (afterOccupancy_keeps source credential setup codec checks encode before.control lookup)
                before pool result aligned supported
            · exact pure_at source _ before pool receipts result aligned supported

private theorem take_receipts (index : Nat) (before : RegistrationServerFrontendCompiler.State n) :
    receipts (RegistrationServerSdkSource.take index before).2 = receipts before := by
  unfold RegistrationServerSdkSource.take
  cases before.sessions[index]? with
  | none => rfl
  | some token => cases token <;> rfl

/-- The complete actual reified SDK build preserves chronological correspondence through moved-token consumption, conversion, lookup, size, occupancy and reservation failure, actual signing and commit. -/
theorem build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (index : Nat) (application : Option (Slice U8))
    (before : RegistrationServerFrontendCompiler.State n) (pool : Pool source)
    (result : (RustM (Option (Std.U64 × Pqxdh.Bytes)) × RegistrationServerFrontendCompiler.State n) × Pool source)
    (aligned : Aligned pool.signing before.world.world.2)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaServer.build (handleSource source) credential setup codec checks encode index application) before pool)) :
    Aligned result.2.signing result.1.2.world.world.2 := by
  have initial : Aligned pool.signing (receipts before) := aligned
  have takenSame := take_receipts index before
  simp only [RegistrationNativeMldsaServer.build, StateT.run, runState] at supported
  cases taken : RegistrationServerSdkSource.take index before with
  | mk token current =>
      simp only [taken] at supported takenSame
      have currentAligned : Aligned pool.signing (receipts current) := takenSame ▸ initial
      cases token with
      | none => exact pure_at source _ current pool receipts result currentAligned supported
      | some token => cases application with
        | none => exact pure_at source _ current pool receipts result currentAligned supported
        | some bytes =>
            exact complete_keeps source credential setup codec checks encode token bytes current pool result currentAligned supported
end SDK

end BeaconcryptCore.Computational.RegistrationNativeMldsaServerChronology
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerChronology.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerChronology.signing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerChronology.completionFromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerChronology.completionFromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerChronology.SDK.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerChronology.SDK.build
