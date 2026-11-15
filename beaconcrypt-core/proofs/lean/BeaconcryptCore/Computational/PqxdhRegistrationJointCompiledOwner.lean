-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler

/-! The actual compiled whole native owner: one class ledger bounding its private-service and original native-tail requests, and the complete finish source and continuation distribution equalities and query-count/resource bounds transported through the exact compiler interpretation. The class ledger and uniform allowance are upper bounds. The scheduler-finish statements observe only the public reply, the encoded reinstalled owner and the complete native shared poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner
variable (completedBinding : beaconcrypt_core.session.CompletedRegistrationBinding)
open PqxdhRefinement PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointFinishCompiler (compiler impl Kind classify cap preCap)
open PqxdhRegistrationJointFinish (State callbacks annotated)
open PqxdhRegistrationJointBundle (encode)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The whole compiled native owner emits at most one KEM decapsulation, one joint identity DH, 56 original native-tail requests and no other private-service capability. The counts hold on every phase and every typed reply, including failed preparation, root, initialization and receive attempts. -/
theorem owner_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationJointBundle.Owner) (kind : Kind) :
    (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw owner)).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) (Response := Response) query = kind) (cap kind) := by
  have split : cap kind = preCap kind + (if kind = none then 56 else 0) := by
    cases kind <;> simp [cap, preCap]
  rw [PqxdhRegistrationJointFinish.native_run]
  cases phase : owner.beacon.phase with
  | initSent control prekey oneTime keys =>
      simp only [PqxdhRegistrationJointFinish.run, phase]
      rw [split]
      apply isQueryBoundP_bind
      · have prepared := PqxdhRegistrationJointFinishCompiler.prepare_queries (completedBinding := completedBinding) (Response := Response)
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
      (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw owner)) =
      simulateQ (callbacks setup codec) (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw owner) :=
  PqxdhRegistrationJointFinishCompiler.program_interpreted setup codec _

/-- Interpreting the compiled owner is the same annotated native execution with only the private owner representation mapped. The exact identity and active KEM slots are local representation conditions, not origin or authentication premises. -/
theorem owner_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys) :
    (simulateQ (impl setup codec) (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw (encode setup identityIndex kemIndex owner)))).run state =
      (fun result => ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) <$>
        (simulateQ (annotated setup codec identityIndex kemIndex)
          (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw owner)).run state := by
  rw [owner_interpreted]
  exact PqxdhRegistrationJointFinish.owner_source (completedBinding := completedBinding) setup codec identityIndex kemIndex owner raw state identityOwned kemOwned

/-- Dropping only the private service pools from the compiled owner's execution recovers the literal native owner, its optional reply and complete shared state, including failure-path cache effects. -/
theorem owner_original (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys) :
    (fun result => (result.1, result.2.2)) <$>
      (simulateQ (impl setup codec) (simulateQ (compiler setup codec)
        (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw (encode setup identityIndex kemIndex owner)))).run state =
      (fun result => ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) <$>
        (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
          (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw owner)).run state.2 := by
  rw [owner_interpreted]
  exact PqxdhRegistrationJointFinish.owner_original (completedBinding := completedBinding) setup codec identityIndex kemIndex owner raw state identityOwned kemOwned

/-- Any complete continuation of the compiled owner receives the mapped returned owner, both private service pools and the native shared poststate of the same annotated execution. -/
theorem owner_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys)
    (next : (Option Pqxdh.Bytes × PqxdhRegistrationJointBundle.Owner) × State KemSK → ProbComp Result) :
    ((simulateQ (impl setup codec) (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw (encode setup identityIndex kemIndex owner)))).run state >>= next) =
      ((simulateQ (annotated setup codec identityIndex kemIndex)
        (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw owner)).run state >>= fun result =>
          next ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) := by
  rw [owner_interpreted]
  exact PqxdhRegistrationJointFinish.owner_continuation (completedBinding := completedBinding) setup codec identityIndex kemIndex owner raw state
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
      (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw (encode setup identityIndex kemIndex owner)))).run state).IsTotalQueryBound
      (69 * max 64 (caps.decapsUniform + caps.baseUniform * caps.decapsBase)) := by
  rw [owner_interpreted]
  exact PqxdhRegistrationJointFinish.owner_uniform (completedBinding := completedBinding) setup codec caps bounded identityIndex kemIndex owner raw state
    identityOwned kemOwned

/-- The scheduler's owner finish with the compiled owner on the private-pool/native product state: the same transcript hash on the shared cache, then the compiled encoded owner at the completed binding of the digest; abort and inactive branches return the encoded owner. -/
noncomputable def compiledFinish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    StateT (State KemSK) ProbComp (Option Pqxdh.Bytes × PqxdhRegistrationJointBundle.Owner) :=
  match owner.beacon.phase with
  | .initSent control _ _ _ =>
    match retained, responseOf codec raw with
    | some init, some response => do
        let digest ← PqxdhRegistrationJointFinish.onNative
          (nativeHash (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) response))
        simulateQ (impl setup codec) (simulateQ (compiler setup codec)
          (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := PqxdhTranscriptAd.completedOf control digest)
            codec.frameRead raw (encode setup identityIndex kemIndex owner)))
    | _, _ => pure (none, encode setup identityIndex kemIndex (PqxdhBeaconPhase2Preparation.abort control owner))
  | _ => pure (none, encode setup identityIndex kemIndex owner)

/-- The compiled hashed owner finish is the annotated hashed owner finish with only the private owner representation mapped, under the same local slot conditions as `owner_source`. -/
theorem compiledFinish_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys) :
    (compiledFinish setup codec identityIndex kemIndex retained raw owner).run state =
      (fun result => ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) <$>
        (PqxdhRegistrationJointFinish.annotatedFinish setup codec identityIndex kemIndex retained raw owner).run state := by
  unfold PqxdhRegistrationJointFinish.annotatedFinish compiledFinish
  cases phase : owner.beacon.phase <;> simp only [StateT.run_pure, map_pure]
  case initSent control prekey oneTime kem =>
    cases retained <;> cases decoded : responseOf codec raw <;> simp only [StateT.run_pure, map_pure]
    have hashRun : ∀ (work : NativeGame KemSK CtxRomAuth.CtxDigest),
        (PqxdhRegistrationJointFinish.onNative work).run state =
          (fun result => (result.1, (state.1, result.2))) <$> work.run state.2 := fun _ => rfl
    rw [StateT.run_bind, StateT.run_bind, hashRun, bind_map_left, bind_map_left, map_bind]
    exact bind_congr fun hashed => owner_source (completedBinding := PqxdhTranscriptAd.completedOf control hashed.1)
      setup codec identityIndex kemIndex owner raw (state.1, hashed.2) identityOwned (kemOwned · · · · ·)

/-- A present public owner slot's actual finish and the compiled hashed owner finish (`compiledFinish`) started from any pool holding its exact private slots agree on the public reply, the mapped reinstalled owner and the complete native shared poststate. Other owner slots and the raw reinstalled owner are not observed; `PqxdhRegistrationJointFinish.finish_source` gives the whole scheduler poststate from the same annotated execution. -/
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
        (compiledFinish setup codec identityIndex kemIndex (state.inits ownerAddress) raw owner).run
          (pool, state.shared) := by
  have bound : ownerAddress < state.owners.length := (List.getElem?_eq_some_iff.mp found).1
  rw [PqxdhRegistrationJointFinish.finish_source setup codec ownerAddress identityIndex kemIndex raw state pool owner found,
    Functor.map_map]
  simp only [List.getElem?_set_self bound, Option.map_some]
  unfold PqxdhRegistrationJointFinish.annotatedFinish compiledFinish
  cases phase : owner.beacon.phase <;> simp only [StateT.run_pure, map_pure]
  case initSent control prekey oneTime kem =>
    cases retained : state.inits ownerAddress <;> cases decoded : responseOf codec raw <;>
      simp only [StateT.run_pure, map_pure]
    have hashRun : ∀ (work : NativeGame KemSK CtxRomAuth.CtxDigest),
        (PqxdhRegistrationJointFinish.onNative work).run (pool, state.shared) =
          (fun result => (result.1, (pool, result.2))) <$> work.run state.shared := fun _ => rfl
    rw [StateT.run_bind, StateT.run_bind, hashRun, bind_map_left, bind_map_left, map_bind, map_bind]
    refine bind_congr fun hashed => ?_
    rw [owner_source (completedBinding := PqxdhTranscriptAd.completedOf control hashed.1) setup codec
      identityIndex kemIndex owner raw (pool, hashed.2) identityOwned (kemOwned · · · · ·), Functor.map_map]

/-- Any continuation of the actual finish that observes its public reply, mapped reinstalled owner and complete shared poststate is the same continuation of the compiled hashed owner finish. -/
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
      ((compiledFinish setup codec identityIndex kemIndex (state.inits ownerAddress) raw owner).run
        (pool, state.shared) >>= fun result =>
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
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.compiledFinish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCompiledOwner.compiledFinish_source
