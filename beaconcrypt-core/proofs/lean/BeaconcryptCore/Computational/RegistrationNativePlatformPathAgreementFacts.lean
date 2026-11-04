-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInvariants
import BeaconcryptCore.Computational.RegistrationNativePlatformCoherenceRun
import BeaconcryptCore.Computational.RegistrationNativePathAgreementFacts
import BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal

/-! Actual corrected chronological source paths retain genuinely generated private KEM rows, public/private prekey equations and pending control coherence. Startup discharges the initial invariants for all retained owners. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPathAgreementFacts
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeTokenSource (Present Born)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

variable [primitive : AdapterSealPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate
  RegistrationServerNativeSource.agree RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin

private theorem actual (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ((reply, after.1), after.2) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer query).run before.1).run before.2) := by
  simp only [RegistrationNativePlatformInitPendingJournal.callback, RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at supported
  obtain ⟨⟨⟨value, native⟩, platform⟩, called, same⟩ := supported
  cases same
  exact called

/-- The three source key/control invariants hold simultaneously for every retained owner along the literal corrected path. -/
theorem path {first last : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl first calls last) (prior : RegistrationNativePathAgreementFacts.Valid setup first.1) :
    RegistrationNativePathAgreementFacts.Valid setup last.1 := by
  induction reached with
  | nil state => exact prior
  | cons call called rest last following ih =>
    have sourceCalled := actual coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      call.query call.before call.after call.reply called
    have ownerFacts := RegistrationNativePlatformOwnerInvariants.handler coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer call.query call.before.1 call.after.1 call.before.2 call.after.2 call.reply ⟨prior.1, prior.2.1⟩ sourceCalled
    exact ih ⟨ownerFacts.1, ownerFacts.2,
      RegistrationNativePlatformCoherenceRun.handler coins setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer call.query call.before.1 call.after.1 call.before.2 call.after.2 call.reply prior.2.2 sourceCalled⟩

/-- Actual successful startup supplies all owner invariants at every reached corrected source prefix. -/
theorem initialized (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (last : Whole) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (reached : Path impl (initial.state, previous) calls last) : RegistrationNativePathAgreementFacts.Valid setup last.1 :=
  path coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer reached
    ⟨RegistrationNativeKemBirthRun.start_holds setup source ensureInit identityIndex serverKeyId initial started,
      RegistrationNativePrekeyCoherence.start setup ensureInit identityIndex serverKeyId initial started,
      RegistrationNativeBeaconCoherenceRun.start_holds setup source ensureInit identityIndex serverKeyId initial started⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPathAgreementFacts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPathAgreementFacts.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPathAgreementFacts.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPathAgreementFacts.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPathAgreementFacts.initialized
