-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuild
import BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath
/-! The current full Word source consumes the early KEM reservation in exact birth order under its original public create allowance. The current source-derived constructor cap rules out fallback; no final-owner activation or private row association is supplied as a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativePlatformSecretWordAliasAlignment (State)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller



open RegistrationNativeSecretWordSessionSlots (Preserves)

/-- Every actual current typed callback preserves each surviving earlier one-use session, including dynamic writer failures. -/
theorem typed_preserves (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source Platform)
    (supported : result ∈ support ((typed query).run before)) :
    Preserves before.1.1.server.sessions result.2.1.1.server.sessions := by
  have free := RegistrationNativePlatformSecretWordExecution.typed_support setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller query before result supported
  by_cases accepts : RegistrationNativeRawAdapter.kind query = 3
  · cases query with
    | inl coin => cases accepts
    | inr command => cases command with
      | accept packet =>
        rw [RegistrationNativePlatformSecretWordTargetRetained.accept_run,support_map] at supported
        obtain ⟨reached,called,equal⟩ := supported
        have shape := RegistrationNativePlatformSecretWordAtomSessionShape.accept implementation setup checks
          (decide (before.1.1.parsedAccepts = selectedAccept)) (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration)
          source.verify packet (before.1.1.server,(before.1.1.environment,(before.1.2,before.2))) reached called
        cases equal
        exact RegistrationNativeSecretWordSessionSlots.shape _ _ _ shape
      | _ => cases accepts
  · by_cases builds : RegistrationNativeRawAdapter.kind query = 4
    · cases query with
      | inl coin => cases builds
      | inr command => cases command with
        | build handle application =>
          have same := RegistrationNativePlatformSecretWordLiveBuild.sessions setup sign view failure allocation erased helper writer reservePeer
            source handle application before.1 (result.1,result.2.1) free
          rw [same]
          exact RegistrationNativeSecretWordSessionSlots.take handle before.1.1.server
        | _ => cases builds
    · have same := RegistrationNativePlatformSecretWordLiveState.quiet_server setup checks
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query ⟨accepts,builds⟩ before.1 (result.1,result.2.1) free
      rw [same]
      exact RegistrationNativeSecretWordSessionSlots.refl _

omit primitive in
private theorem program_preserves {Index : Type} {spec : OracleSpec Index}
    (localInterpreter : QueryImpl spec (StateT (State n KemSK source Platform) ProbComp))
    (step : ∀ query before result, result ∈ support ((localInterpreter query).run before) →
      Preserves before.1.1.server.sessions result.2.1.1.server.sessions)
    (work : OracleComp spec A) (before : State n KemSK source Platform) (result : A × State n KemSK source Platform)
    (supported : result ∈ support ((simulateQ localInterpreter work).run before)) :
    Preserves before.1.1.server.sessions result.2.1.1.server.sessions := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query localInterpreter
    (fun current => Preserves before.1.1.server.sessions current.1.1.server.sessions)
    (fun query current prior next reached => RegistrationNativeSecretWordSessionSlots.trans _ _ _ prior
      (step query current next reached)) work before _ result supported
  exact RegistrationNativeSecretWordSessionSlots.refl _

/-- Malformed raw requests and all decoded callbacks retain the same surviving stored session values. -/
theorem raw (query : RegistrationNativeInterface.Spec.Domain) (before : State n KemSK source Platform)
    (result : RegistrationNativeInterface.Spec.Range query × State n KemSK source Platform)
    (supported : result ∈ support ((RegistrationNativeRawAdapter.handler
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) typed query).run before)) :
    Preserves before.1.1.server.sessions result.2.1.1.server.sessions :=
  program_preserves source typed
    (typed_preserves setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationNativeRawAdapter.adapter (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) query) before result supported

/-- Every complete original full-interface callback preserves those same old slots, including all secrecy coin/send continuations. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source Platform)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds typed query).run before)) :
    Preserves before.2.1.1.server.sessions result.2.2.1.1.server.sessions := by
  rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨reached,called,returned⟩ := supported
  cases returned
  exact program_preserves source (RegistrationNativeRawAdapter.handler (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) typed)
    (raw setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    _ before.2 reached called

/-- Actual later chronological calls can only consume an old capability or append a new slot, never replace its Ready. -/
theorem path (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × State n KemSK source Platform}
    {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        serverKeyId bounds typed) before entries after) :
    Preserves before.2.1.1.server.sessions after.2.1.1.server.sessions := by
  apply RegistrationNativeSecretWordTargetPath.preserves _
    (fun current => Preserves before.2.1.1.server.sessions current.2.1.1.server.sessions)
    (fun query current result prior reached => RegistrationNativeSecretWordSessionSlots.trans _ _ _ prior
      (full setup checks wire source route sign input inside selected pairs publicKey challenge outer
        selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        serverKeyId bounds query current result reached)) actual
  exact RegistrationNativeSecretWordSessionSlots.refl _

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource.typed_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource.typed_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource.full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource.path
