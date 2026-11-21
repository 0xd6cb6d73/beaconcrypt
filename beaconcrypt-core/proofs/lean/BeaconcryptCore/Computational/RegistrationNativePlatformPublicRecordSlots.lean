-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend
/-! A private analysis observer retains only the raw material reply's opaque slot and public installation order. It is interpreted below true/false materialization, so it preserves original slot IDs when the known-side continuation receives reconstructed material instead. The source client and external platform state remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots
open PqxdhRecordLiftInterface (Slot Role)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePlatformRecordSlotGhost (Receipt)
variable {n : Nat} {KemSK A : Type}

structure State (n : Nat) where
  pending : Option (Slot n)
  snapshot : RegistrationNativePlatformRecordSlotGhost.State n

def initial : State n := ⟨none,RegistrationNativePlatformRecordSlotGhost.initial⟩

def choiceSlot : RegistrationNativePairedChoice.Choice n → Option (Slot n)
  | .known _ => none
  | .hidden reference => some reference.slot

def pendingUpdate : (query : (Spec n KemSK).Domain) → (Spec n KemSK).Range query → Option (Slot n) → Option (Slot n)
  | .inl (.inl _), _, _ => none
  | .inl (.inr (.inl (.inl _))), reply, _ => reply.bind choiceSlot
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer ..)))))), _, _ => none
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon ..)))))), _, _ => none
  | _, _, previous => previous

def snapshotUpdate (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (pending : Option (Slot n)) (before : RegistrationNativePlatformRecordSlotGhost.State n) :
    RegistrationNativePlatformRecordSlotGhost.State n :=
  match query with
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId _ _)))))) =>
      if @Eq Bool reply true then
        ⟨{before.origins with peers:=Function.update before.origins.peers keyId pending},
          before.installs++[⟨.server,.peer keyId,pending⟩]⟩ else before
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner _ _)))))) =>
      if @Eq Bool reply true then
        ⟨{before.origins with owners:=Function.update before.origins.owners owner pending},
          before.installs++[⟨.beacon,.owner owner,pending⟩]⟩ else before
  | .inl (.inr (.inl (.inr (.inr (.inr (.appendOwner _ _ _)))))) =>
      ⟨{before.origins with owners:=Function.update before.origins.owners reply none},before.installs⟩
  | _ => before

def step (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query) (before : State n) : State n :=
  ⟨pendingUpdate query reply before.pending,snapshotUpdate query reply before.pending before.snapshot⟩

def handler : QueryImpl (Spec n KemSK) (StateT (State n) (OracleComp (Spec n KemSK))) := fun query before =>
  (fun reply => (reply,step query reply before)) <$> (Spec n KemSK).query query

def program (work : OracleComp (Spec n KemSK) A) (before : State n := initial) : OracleComp (Spec n KemSK) (A × State n) :=
  (simulateQ handler work).run before

theorem query_erase (query : (Spec n KemSK).Domain) (before : State n) :
    Prod.fst <$> (handler query).run before=(Spec n KemSK).query query := by
  simp only [handler,StateT.run,Functor.map_map,id_map']

theorem program_erase (work : OracleComp (Spec n KemSK) A) (before : State n) :
    Prod.fst <$> program work before=work := by
  unfold program
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query continuation ih =>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    simp only [handler,StateT.run,bind_map_left,map_bind]
    apply bind_congr
    intro reply
    exact ih reply _

theorem program_bound (predicate : (Spec n KemSK).Domain → Prop) [DecidablePred predicate]
    (work : OracleComp (Spec n KemSK) A) (count : Nat) (bounded : work.IsQueryBoundP predicate count) (before : State n) :
    (program work before).IsQueryBoundP predicate count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simp [handler,StateT.run,isQueryBoundP_map_iff,isQueryBoundP_query_iff,counted]
  · intro query uncounted current
    simp [handler,StateT.run,isQueryBoundP_map_iff,isQueryBoundP_query_iff,uncounted]

theorem interpreted_erase {I S : Type} {spec : OracleSpec I}
    (implementation : QueryImpl (Spec n KemSK) (StateT S (OracleComp spec)))
    (work : OracleComp (Spec n KemSK) A) (ghost : State n) (before : S) :
    (fun result => (result.1.1,result.2)) <$>
      (simulateQ implementation (program work ghost)).run before =
        (simulateQ implementation work).run before := by
  have erased := congrArg (fun tree => (simulateQ implementation tree).run before) (program_erase work ghost)
  simpa only [simulateQ_map,StateT.run_map] using erased
section Actual
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedLocal (translate)
variable {E Platform I : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "Front" => RegistrationNativePlatformPublicFrontend.State source Platform
local notation "callback" => RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "embed" => RegistrationNativePlatformPublicCoinEmbedding.embed

/-- Actual source callbacks retain the same raw-demand slot observer below both materialization interpretations. The stateful writer and every source failure are the original ones. -/
theorem handler_source (seeds : Seeds n) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : Front) (ghost : State n) :
    program (simulateQ (translate true seeds) (simulateQ embed ((callback query).run before))) ghost =
      program (simulateQ (translate false seeds) (simulateQ embed ((callback query).run before))) ghost := by
  exact congrArg (fun tree => program tree ghost)
    (RegistrationNativePlatformMaterializedFrontend.handler_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer seeds query before)

/-- All adaptive literal source callbacks preserve the same slot/ordinal analysis output and complete returned frontend/P. -/
theorem typed_source (seeds : Seeds n) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (before : Front) (ghost : State n) :
    program (simulateQ (translate true seeds) (simulateQ embed ((simulateQ callback work).run before))) ghost =
      program (simulateQ (translate false seeds) (simulateQ embed ((simulateQ callback work).run before))) ghost := by
  exact congrArg (fun tree => program tree ghost)
    (RegistrationNativePlatformMaterializedFrontend.program_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer seeds work before)

/-- Every original raw mode and full canonical ledger has the same computable material-slot extension, without a caller source/observer correspondence law. -/
theorem run_source (seeds : Seeds n) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Front) (ghost : State n) :
    program (simulateQ (translate true seeds) (simulateQ embed
      (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))) ghost =
      program (simulateQ (translate false seeds) (simulateQ embed
        (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))) ghost := by
  exact congrArg (fun tree => program tree ghost)
    (RegistrationNativePlatformMaterializedFrontend.run_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer seeds serverKeyId bounds mode work before)
end Actual
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.query_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.program_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.interpreted_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.interpreted_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.handler_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.typed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots.run_source
