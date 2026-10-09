-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataNative

/-! Exact receive metadata through the full adaptive ledger and initialized source. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftFlat (KnownAt support_keep_oracle support_run_fst)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle FullSpec FreshBounds Mode ModeSpec asModeO)
open PqxdhRecordFactsOriginMarkerNative
open PqxdhRecordFactsOriginMarkerLedger (fullImpl full_run)
open PqxdhRecordFactsOriginMetadataNative
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Every actual ledger step appends its literal query/reply and gives the exact final receive metadata classification. -/
theorem ledger_record (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (before : State n E)
    (result : (FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) × State n E)
    (supported : result ∈ support ((simulateQ (nativeImpl target modes replace setup codec route env)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run before)) :
    result.1.2.transcript = ledger.transcript ++ [⟨query, result.1.1⟩] ∧
      EntryFact codec.frameRead route result.2.1.2 ⟨query, result.1.1⟩ := by
  refine ⟨PqxdhDeploymentTargetRange.ledger_step setup.source.crypto codec serverKid bounds query ledger result.1
    (support_run_fst _ _ _ result supported), ?_⟩
  rcases query with forwarded | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact native_final target modes replace setup codec route env forwarded before inner reached
  · exact secrecy_entry codec.frameRead route result.2.1.2 secrecy result.1.1

/-- Metadata facts for the actual ledger, with every source state component retained. -/
def Invariant (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (state : PqxdhDeploymentSecrecy.Ledger × State n E) : Prop :=
  ∀ entry ∈ state.1.transcript, EntryFact read route state.2.1.2 entry

/-- Complete full queries preserve prior metadata and append their literal query and reply. -/
theorem full_invariant (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × State n E) (good : Invariant codec.frameRead route before)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × State n E))
    (supported : result ∈ support ((fullImpl target modes replace setup codec route env serverKid bounds query).run before)) :
    Invariant codec.frameRead route result.2 := by
  rw [full_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have recorded := ledger_record target modes replace setup codec route env serverKid bounds query before.1 before.2 inner reached
  intro entry member
  rw [recorded.1, List.mem_append, List.mem_singleton] at member
  rcases member with prior | rfl
  · exact entry_mono codec.frameRead route before.2.1.2 inner.2.1.2
      (fun handle known => program_known target modes replace setup codec route env _ before.2 handle known inner reached)
      entry (good entry prior)
  · exact recorded.2

/-- Every adaptive full continuation retains all accepted metadata facts. -/
theorem full_program_invariant (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (client : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × State n E) (good : Invariant codec.frameRead route before)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × State n E))
    (supported : result ∈ support ((simulateQ (fullImpl target modes replace setup codec route env serverKid bounds) client).run before)) :
    Invariant codec.frameRead route result.2 :=
  support_keep_oracle (fullImpl target modes replace setup codec route env serverKid bounds) (Invariant codec.frameRead route)
    (fun query state present => full_invariant target modes replace setup codec route env serverKid bounds query state present)
    client before good result supported

/-- The literal empty transcript satisfies metadata without any source state premise. -/
theorem empty_invariant (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (state : State n E) : Invariant read route (PqxdhDeploymentSecrecy.Ledger.empty, state) := by
  simp [Invariant, PqxdhDeploymentSecrecy.Ledger.empty]

/-- Every supported initialized literal source execution supplies receive metadata facts for its actual final transcript. -/
theorem program_entryFacts (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n × Bool)
    (result : Client n E X × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript,
      EntryFact codec.frameRead route result.1.2 entry := by
  rw [PqxdhRecordFactsOriginMarkerGlobal.program_flat, mem_support_bind_iff] at supported
  obtain ⟨born, bornSupported, continued⟩ := supported
  cases bornEq : born.1.1 with
  | none =>
      simp only [bornEq] at continued
      obtain rfl := (mem_support_pure_iff _ _).mp continued
      simp
  | some start =>
      rcases start with ⟨created, start⟩
      simp only [bornEq] at continued
      rw [mem_support_bind_iff] at continued
      obtain ⟨installed, installSupported, continued⟩ := continued
      rw [support_map] at continued
      obtain ⟨final, finalSupported, rfl⟩ := continued
      have complete := full_program_invariant target modes replace setup codec route env serverKid bounds
        (asModeO mode adversary) _ (empty_invariant codec.frameRead route _) final finalSupported
      intro value member
      have equal := Option.some.inj member
      subst value
      exact complete

/-- The complete erased source has the same metadata facts after forgetting only the analysis flag. -/
theorem erased_entryFacts (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n)
    (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript, EntryFact codec.frameRead route result.1.2 entry := by
  rw [← PqxdhRecordFactsOriginMuteAdaptive.complete_erase target (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) _ (initial, false), support_map] at supported
  obtain ⟨marked, reached, rfl⟩ := supported
  exact program_entryFacts target modes replace setup codec route env serverKid bounds mode adversary (initial, false) marked reached

/-- Every successful final-hidden receive returns the metadata of its exact decoded raw frame. -/
theorem erased_received_metadata (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n)
    (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript, ∀ receiver raw opened handle slot,
      entry.received = some (receiver, raw, .Some opened) → receivingHandle route receiver raw = some handle →
      handleSlot result.1.2 handle = some slot → Metadata codec.frameRead raw opened := by
  intro value present entry recorded receiver raw opened handle slot received routed hidden
  rcases erased_entryFacts target modes replace setup codec route env serverKid bounds mode adversary initial result supported
    value present entry recorded receiver raw opened handle received routed with known | metadata
  · have absent := PqxdhRecordFactsOriginAccepted.known_no_slot result.1.2 handle known
    rw [absent] at hidden
    cases hidden
  · exact metadata

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.ledger_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.ledger_record

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.full_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.full_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.full_program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.full_program_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.empty_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.empty_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.program_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.program_entryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.erased_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.erased_entryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.erased_received_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal.erased_received_metadata
