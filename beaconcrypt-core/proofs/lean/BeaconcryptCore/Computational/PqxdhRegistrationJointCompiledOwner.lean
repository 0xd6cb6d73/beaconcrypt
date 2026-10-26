-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler

/-! The actual compiled whole native owner: one class ledger bounding its private-service and original native-tail requests, and the complete finish source and continuation distribution equalities and query-count/resource bounds transported through the exact compiler interpretation. The class ledger and uniform allowance are upper bounds. The scheduler-finish statements observe only the public reply, the encoded reinstalled owner and the complete native shared poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner
open PqxdhRefinement PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointFinishCompiler (compiler impl Kind classify cap preCap)
open PqxdhRegistrationJointFinish (State callbacks annotated)
open PqxdhRegistrationJointBundle (encode)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The whole compiled native owner emits at most one KEM decapsulation, one joint identity DH, 56 original native-tail requests and no other private-service capability. The counts hold on every phase and every typed reply, including failed preparation, root, initialization and receive attempts. -/
theorem owner_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationJointBundle.Owner) (kind : Kind) :
    (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) (Response := Response) query = kind) (cap kind) := by
  have split : cap kind = preCap kind + (if kind = none then 56 else 0) := by
    cases kind <;> simp [cap, preCap]
  rw [PqxdhRegistrationJointFinish.native_run]
  cases phase : owner.beacon.phase with
  | initSent control prekey oneTime keys =>
      simp only [PqxdhRegistrationJointFinish.run, phase]
      rw [split]
      apply isQueryBoundP_bind
      · have prepared := PqxdhRegistrationJointFinishCompiler.prepare_queries (Response := Response)
          setup codec control owner.beacon.identity prekey oneTime keys raw kind
        rw [← QueryImpl.simulateQ_compose] at prepared
        exact prepared
      · rintro (_ | prepared) _
        · trivial
        · simp only [bind_pure_comp, isQueryBoundP_map_iff]
          exact PqxdhRegistrationJointFinishCompiler.tail_queries (KemSK := KemSK) _ 56
            (PqxdhBeaconPhase2Bounds.native_tail_bound _ _) kind
  | _ => simp only [PqxdhRegistrationJointFinish.run, phase]; trivial

/-- The actual compiled owner program is interpreted by exactly the original indexed finish callbacks on the whole private-pool/native product state. -/
theorem owner_interpreted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationJointBundle.Owner) :
    simulateQ (impl setup codec) (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)) =
      simulateQ (callbacks setup codec) (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner) :=
  PqxdhRegistrationJointFinishCompiler.program_interpreted setup codec _

/-- Interpreting the compiled owner is the same annotated native execution with only the private owner representation mapped. The exact identity and active KEM slots are local representation conditions, not origin or authentication premises. -/
theorem owner_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys) :
    (simulateQ (impl setup codec) (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw (encode setup identityIndex kemIndex owner)))).run state =
      (fun result => ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) <$>
        (simulateQ (annotated setup codec identityIndex kemIndex)
          (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state := by
  rw [owner_interpreted]
  exact PqxdhRegistrationJointFinish.owner_source setup codec identityIndex kemIndex owner raw state identityOwned kemOwned

/-- Dropping only the private service pools from the compiled owner's execution recovers the literal native owner, its optional reply and complete shared state, including failure-path cache effects. -/
theorem owner_original (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys) :
    (fun result => (result.1, result.2.2)) <$>
      (simulateQ (impl setup codec) (simulateQ (compiler setup codec)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw (encode setup identityIndex kemIndex owner)))).run state =
      (fun result => ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) <$>
        (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
          (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state.2 := by
  rw [owner_interpreted]
  exact PqxdhRegistrationJointFinish.owner_original setup codec identityIndex kemIndex owner raw state identityOwned kemOwned

/-- Any complete continuation of the compiled owner receives the mapped returned owner, both private service pools and the native shared poststate of the same annotated execution. -/
theorem owner_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys)
    (next : (Option Pqxdh.Bytes × PqxdhRegistrationJointBundle.Owner) × State KemSK → ProbComp Result) :
    ((simulateQ (impl setup codec) (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw (encode setup identityIndex kemIndex owner)))).run state >>= next) =
      ((simulateQ (annotated setup codec identityIndex kemIndex)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state >>= fun result =>
          next ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) := by
  rw [owner_interpreted]
  exact PqxdhRegistrationJointFinish.owner_continuation setup codec identityIndex kemIndex owner raw state
    identityOwned kemOwned next

/-- The interpreted compiled owner inherits the complete original uniform allowance, including all KEM/base work and every root/hash cache sample before rejection. -/
theorem owner_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys) :
    ((simulateQ (impl setup codec) (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw (encode setup identityIndex kemIndex owner)))).run state).IsTotalQueryBound
      (69 * max 64 (caps.decapsUniform + caps.baseUniform * caps.decapsBase)) := by
  rw [owner_interpreted]
  exact PqxdhRegistrationJointFinish.owner_uniform setup codec caps bounded identityIndex kemIndex owner raw state
    identityOwned kemOwned

/-- A present public owner slot's actual finish and the compiled owner started from any pool holding its exact private slots agree on the public reply, the mapped reinstalled owner and the complete native shared poststate. Other owner slots and the raw reinstalled owner are not observed; `PqxdhRegistrationJointFinish.finish_source` gives the whole scheduler poststate from the same annotated execution. -/
theorem finish_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ownerAddress identityIndex kemIndex : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : state.owners[ownerAddress]? = some owner)
    (identityOwned : pool.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      pool.2.keys[kemIndex]? = some keys) :
    (fun result => (result.1, (result.2.owners[ownerAddress]?).map (encode setup identityIndex kemIndex),
      result.2.shared)) <$> (PqxdhRegistrationSchedule.finish setup codec ownerAddress raw).run state =
      (fun result => (result.1.1, some result.1.2, result.2.2)) <$>
        (simulateQ (impl setup codec) (simulateQ (compiler setup codec)
          (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw
            (encode setup identityIndex kemIndex owner)))).run (pool, state.shared) := by
  have bound : ownerAddress < state.owners.length := (List.getElem?_eq_some_iff.mp found).1
  rw [PqxdhRegistrationJointFinish.finish_source setup codec ownerAddress identityIndex kemIndex raw state pool owner found,
    owner_source setup codec identityIndex kemIndex owner raw (pool, state.shared) identityOwned kemOwned,
    Functor.map_map, Functor.map_map]
  simp only [List.getElem?_set_self bound, Option.map_some]

/-- Any continuation of the actual finish that observes its public reply, mapped reinstalled owner and complete shared poststate is the same continuation of the compiled owner's execution. -/
theorem finish_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ownerAddress identityIndex kemIndex : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : state.owners[ownerAddress]? = some owner)
    (identityOwned : pool.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      pool.2.keys[kemIndex]? = some keys)
    (next : Option Pqxdh.Bytes × Option PqxdhRegistrationJointBundle.Owner × NativeState KemSK → ProbComp Result) :
    ((PqxdhRegistrationSchedule.finish setup codec ownerAddress raw).run state >>= fun result =>
      next (result.1, (result.2.owners[ownerAddress]?).map (encode setup identityIndex kemIndex), result.2.shared)) =
      ((simulateQ (impl setup codec) (simulateQ (compiler setup codec)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw
          (encode setup identityIndex kemIndex owner)))).run (pool, state.shared) >>= fun result =>
        next (result.1.1, some result.1.2, result.2.2)) := by
  have joined := congrArg (fun work => work >>= next)
    (finish_source setup codec ownerAddress identityIndex kemIndex raw state pool owner found identityOwned kemOwned)
  simpa only [bind_map_left] using joined

end BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_interpreted

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_original

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.owner_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.finish_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.finish_continuation
