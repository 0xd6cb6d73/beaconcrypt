-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaStoppedGame
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaStoppedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop

/-! Actual initialized corrected free stopping execution derives ordinary validity and same-cut signing-request freshness. The source/table equation retains the entire native/platform state and private signing pool; count erasure is applied only through its independently checked exact equation. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaStoppedGood
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (handleSource Pool)
open RegistrationNativeMldsaEuf (PublicKey Forgery Valid Fresh)
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
/-- Every candidate actually returned by the complete source program is ordinary valid and fresh against its exact final same-key signing prefix. -/
theorem good (previous : Platform) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (publicKey : PublicKey) (result : Option Forgery × Pool source)
    (supported : result ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous ensureInit identityIndex serverKeyId publicKey) {}))
    (forgery : Forgery) (selected : result.1 = some forgery) :
    Valid source publicKey forgery ∧ Fresh (RegistrationNativeMldsaCandidate.requestsFor publicKey result.2.signing) forgery := by
  simp only [RegistrationNativePlatformOrdinaryMldsaStoppedGame.program, RegistrationNativeMldsaTableProgram.evaluate, simulateQ_bind, StateT.run_bind] at supported
  change result ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
    (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {} >>= fun started =>
      RegistrationNativeMldsaTableProgram.evaluate source
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.continued source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous publicKey started.1) started.2) at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨started, startup, continued_support⟩ := supported
  cases initial_eq : started.1 with
  | none =>
      simp only [initial_eq, RegistrationNativePlatformOrdinaryMldsaStoppedGame.continued, RegistrationNativeMldsaTableProgram.evaluate,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued_support
      cases continued_support
      cases selected
  | some initial =>
      simp only [initial_eq, RegistrationNativePlatformOrdinaryMldsaStoppedGame.continued, RegistrationNativeMldsaTableProgram.evaluate,
        simulateQ_map, StateT.run_map, support_map] at continued_support
      obtain ⟨inner, possible, same⟩ := continued_support
      cases same
      have mapped : RegistrationNativeMldsaStoppedSource.arrange source inner ∈ support ((simulateQ (RegistrationNativeMldsaStop.freeze
          (RegistrationNativePlatformOrdinaryMldsaTableCallback.callback source setup checks wire route representation initial.created initial.credential view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer)
          (RegistrationNativePlatformOrdinaryMldsaTableCallback.observe source publicKey) RegistrationNativeMldsaTableStop.defaultReply)
          (adversary initial.public)).run (((initial.state, previous), started.2), none)) := by
        rw [← RegistrationNativePlatformOrdinaryMldsaStoppedSource.native source setup checks wire route representation initial.created initial.credential
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer publicKey RegistrationNativeMldsaTableStop.defaultReply
          (adversary initial.public) (initial.state, previous) none started.2, support_map]
        exact ⟨inner, possible, rfl⟩
      exact RegistrationNativePlatformOrdinaryMldsaTableStop.initialized_good source setup checks wire route representation
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer publicKey ensureInit identityIndex serverKeyId
        started startup initial (by rw [initial_eq]; exact Option.mem_some_self _) previous (adversary initial.public)
        (RegistrationNativeMldsaStoppedSource.arrange source inner) mapped forgery selected

/-- The same actual validity/freshness receipt holds for the count-free primitive source used by the ordinary EUF reduction. -/
theorem zero_good (previous : Platform) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (publicKey : PublicKey) (result : Option Forgery × Pool source)
    (supported : result ∈ support (RegistrationNativeMldsaZeroSource.evaluate source
      (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous ensureInit identityIndex serverKeyId publicKey) {}))
    (forgery : Forgery) (selected : result.1 = some forgery) :
    Valid source publicKey forgery ∧ Fresh (RegistrationNativeMldsaCandidate.requestsFor publicKey result.2.signing) forgery := by
  rw [RegistrationNativePlatformOrdinaryMldsaStoppedGame.zero] at supported
  exact good source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer adversary previous ensureInit identityIndex serverKeyId publicKey result supported forgery selected
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaStoppedGood

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaStoppedGood.good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaStoppedGood.good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaStoppedGood.zero_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaStoppedGood.zero_good
