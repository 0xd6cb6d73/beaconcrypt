-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPathAgreementFacts
import BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace

/-! Every owner in the selected dynamic-writer runtime retains genuine private-row provenance, prekey/scalar consistency and pending control coherence throughout the same initialized path. Failed terminal reservations change none of these actual native facts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAgreementFacts
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationNativePlatformSourceAccept.authenticate
  RegistrationNativePlatformSourceBuild.pin

open RegistrationNativePendingFrames (PendingAt)
open RegistrationNativePlatformInitPendingJournal (SourceAt)
local notation "coins" => RegistrationNativePlatformMldsaProgram.coins

omit primitive in
private theorem after_cut (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : RegistrationNativePlatformOrdinaryExperiment.M n KemSK source Platform (Option RawCtxSourceSend.Encrypted))
    (before : Native) (previous : Platform) (result : (Option RawCtxSourceSend.Encrypted × Native) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformOrdinaryExperimentRouting.after reserve work).run before).run previous)) :
    ∃ middle ∈ support ((work.run before).run previous), result.1.2 = middle.1.2 := by
  simp only [RegistrationNativePlatformOrdinaryExperimentRouting.after, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at continued
  obtain ⟨gated, _reserved, same⟩ := continued
  exact ⟨middle, called, (congrArg (fun result => result.1.2) same).symm⟩

private theorem actual (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ((reply, after.1), after.2) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run before.1).run before.2) := by
  simp only [RegistrationNativePlatformOrdinaryKemClientJournal.actual, RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at supported
  obtain ⟨⟨⟨value, native⟩, platform⟩, called, same⟩ := supported
  cases same
  exact called

private theorem old_cut (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ∃ oldReply oldP, ((oldReply, after.1), oldP) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer query).run before.1).run before.2) := by
  have called := actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before after reply supported
  rw [RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal] at called
  cases query with
  | inl coin => exact ⟨reply, after.2, called⟩
  | inr command => cases command with
    | serverSend key plaintext =>
      obtain ⟨middle, reached, same⟩ := after_cut reserveFrame _ before.1 before.2 ((reply, after.1), after.2) called
      change after.1 = middle.1.2 at same
      exact ⟨middle.1.1, middle.2, by rw [same]; exact reached⟩
    | beaconSend owner plaintext =>
      obtain ⟨middle, reached, same⟩ := after_cut reserveFrame _ before.1 before.2 ((reply, after.1), after.2) called
      change after.1 = middle.1.2 at same
      exact ⟨middle.1.1, middle.2, by rw [same]; exact reached⟩
    | _ => exact ⟨reply, after.2, called⟩

/-- The three source key/control invariants hold simultaneously for every retained owner along the literal corrected path. -/
theorem path {first last : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl first calls last) (prior : RegistrationNativePathAgreementFacts.Valid setup first.1) :
    RegistrationNativePathAgreementFacts.Valid setup last.1 := by
  induction reached with
  | nil state => exact prior
  | cons call called rest last following ih =>
    obtain ⟨reply, next, sourceCalled⟩ := old_cut setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      call.query call.before call.after call.reply called
    have ownerFacts := RegistrationNativePlatformOwnerInvariants.handler coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer call.query call.before.1 call.after.1 call.before.2 next reply ⟨prior.1, prior.2.1⟩ sourceCalled
    exact ih ⟨ownerFacts.1, ownerFacts.2,
      RegistrationNativePlatformCoherenceRun.handler coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer call.query call.before.1 call.after.1 call.before.2 next reply prior.2.2 sourceCalled⟩

/-- Actual successful startup supplies all owner invariants at every reached corrected source prefix. -/
theorem initialized (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (last : Whole) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (reached : Path impl (initial.state, previous) calls last) : RegistrationNativePathAgreementFacts.Valid setup last.1 :=
  path setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer reached
    ⟨RegistrationNativeKemBirthRun.start_holds setup source ensureInit identityIndex serverKeyId initial started,
      RegistrationNativePrekeyCoherence.start setup ensureInit identityIndex serverKeyId initial started,
      RegistrationNativeBeaconCoherenceRun.start_holds setup source ensureInit identityIndex serverKeyId initial started⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAgreementFacts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAgreementFacts.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAgreementFacts.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAgreementFacts.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAgreementFacts.initialized
