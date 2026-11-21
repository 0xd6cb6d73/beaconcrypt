-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordOriginInitialized
/-! Genuine source startup carries accepted-record origin into the original complete native ledger at each receive's own earlier cache. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStartup
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Secret Reader Response Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))



open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (route : RawCtxServerRouting.SenderDecoder)
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
local notation "reference" => RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
local notation "FullResult" => RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState Platform source) Value


local notation "run" => RegistrationNativePlatformGatedRecordBindingStartup.run (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route
local notation "startup" => RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
local notation "Runtime" => RegistrationNativePlatformGatedNativeRecordOriginInitialized.Runtime n (State n KemSK ProviderState Platform source)
open RegistrationNativeStageTrace (Call Path)
open PqxdhDeploymentInterface (FullSpec Entry)

/-- Every accepted receive in the full native run has an opposite-direction seal witness at its actual earlier cache, after genuine startup and including failed public writes and all later callbacks. -/
theorem initialized_stages (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (result : FullResult) (supported : result ∈ support (run modes replace)) :
    ∃ initialized ∈ support (CborRawRecordOriginFlatten.interpret (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route startup
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl CtxPrivate.initial),
      match initialized.1.1.1 with
      | none => result.1.1 = none
      | some born =>
          let env := RegistrationNativePlatformSelectiveEntropyQuery.environment setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none)
          let reserve := fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount)
          let impl := RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes replace setup codec route
            (RegistrationNativeEntropyPort.environment env) (RegistrationNativePlatformGatedNativeEntropy.reserveLift reserve) serverKeyId bounds
          let startState := (PqxdhDeploymentSecrecy.Ledger.empty, (((([], ((born.native.frontend,previous),privateBefore)), initialized.1.1.2), initialized.1.2), initialized.2))
          ∀ finished ∈ result.1.1, ∃ final : Runtime, ∃ calls : List (Call FullSpec Runtime),
            Path impl startState calls final ∧ final.2.1.2 = result.1.2 ∧ final.2.2 = result.2 ∧
            RegistrationNativeEntropyTrace.strip (calls.map (fun call => (⟨call.query,call.reply⟩ : Entry))) = finished.2.1.2.ledger.transcript ∧
            ∀ call ∈ calls, ∀ receiver raw opened,
              (⟨call.query,call.reply⟩ : Entry).received = some (receiver,raw,core.option.Option.Some opened) →
              ∃ leading trailing, calls = leading ++ call :: trailing ∧ Path impl startState leading call.before ∧
                ∃ handle, PqxdhRecordLiftIdeal.receivingHandle route receiver raw = some handle ∧
                  PqxdhRecordFactsOriginAccepted.Accepted codec call.before.2.1.2 call.before.2.2 handle raw opened := by
  rw [RegistrationNativePlatformGatedRecordBindingStartup.run_start, mem_support_bind_iff] at supported
  obtain ⟨initialized,reached,continued⟩ := supported
  refine ⟨initialized,reached,?_⟩
  rcases initialized with ⟨⟨⟨_ | born,shell⟩,control⟩,secret⟩
  · simp only [mem_support_pure_iff] at continued
    subst result
    rfl
  · have safe := (RegistrationNativeRecordHandleSlots.interpreted
      (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route _ _ _
      PqxdhRecordLiftProtocolHistory.initial_safe _ _ reached).1
    exact RegistrationNativePlatformGatedNativeRecordOriginInitialized.initialized_stages modes ideal replace setup codec route readback
      (RegistrationNativePlatformSelectiveEntropyQuery.environment setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none))
      (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount)) serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) born.created
      ((born.native.frontend,previous),privateBefore) shell control safe secret result continued

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStartup.initialized_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStartup.initialized_stages
