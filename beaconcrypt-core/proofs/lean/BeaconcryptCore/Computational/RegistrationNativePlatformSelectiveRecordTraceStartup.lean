-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveCoinEmbedding
import BeaconcryptCore.Computational.RegistrationNativeG2Trace
/-! The literal shared-platform Server build pairs its retained descriptor with the same returned physical peer, after every source and allocator outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStartup
open PqxdhServerAuthExperiment (Setup Checks Codec)
open BeaconcryptCore.Refinement
variable {Value : Type}
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire

variable (providerState : ProviderState) (previous : Platform)
    (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

abbrev Extra (n : Nat) (KemSK ProviderState Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK ProviderState Platform source × RegistrationNativeG2Trace.State

abbrev Outcome (n : Nat) (KemSK ProviderState Platform Value : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeEntropyRun.Outcome (Extra n KemSK ProviderState Platform source) Value

def forget (result : Outcome n KemSK ProviderState Platform Value source) :
    RegistrationNativeEntropyRun.Outcome (RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK ProviderState Platform source) Value :=
  result.map (fun finished => (finished.1,finished.2.1,finished.2.2.1))

noncomputable def after (started : RegistrationNativeHiddenStartup.Started source) :
    OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (Outcome n KemSK ProviderState Platform Value source) :=
  (fun observed => some (PqxdhRegistrationJointServerBirth.encode started.created,observed.1.1.1,
    ((observed.1.1.2,observed.2),observed.1.2))) <$>
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup canonical (RegistrationNativeMldsa.owned source started.native.credential)
      seed scalar candidate provider)
      (RegistrationNativeG2Trace.program (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source started.native.credential)
          selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed,started.native.credential.publicKey,serverKeyId⟩) (started.native.frontend,previous))))).run
      (RegistrationNativeHiddenInterpreter.initial (n := n) providerState,known)

noncomputable def program : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (Outcome n KemSK ProviderState Platform Value source) := do
  let initialized ← RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
  match initialized with
  | none => pure none
  | some started => after setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known serverKeyId bounds mode adversary started

/-- Erasing only the chronological observer recovers the exact current gated source program with its complete platform and private state. -/
theorem erase :
    forget <$> program (n := n) (source := source) setup checks wire seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer providerState previous known ensureInit identityIndex serverKeyId bounds mode adversary =
      RegistrationNativePlatformSelectiveEntropyStartup.program setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous
        (RegistrationNativeHiddenInterpreter.initial (n := n) providerState,known) bounds mode adversary := by
  unfold program RegistrationNativePlatformSelectiveEntropyStartup.program
  rw [map_bind]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some started =>
    have erasedTree := congrArg (fun work => (simulateQ
      (RegistrationNativeSelectiveHiddenInterpreter.handler setup canonical (RegistrationNativeMldsa.owned source started.native.credential)
        seed scalar candidate provider) work).run (RegistrationNativeHiddenInterpreter.initial (n := n) providerState,known))
      (RegistrationNativeG2Trace.program_erase
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
          (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source (RegistrationNativeMldsa.owned source started.native.credential)
            selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
            serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed,started.native.credential.publicKey,serverKeyId⟩) (started.native.frontend,previous)))
        RegistrationNativeG2Trace.initial)
    simp only [simulateQ_map,StateT.run_map] at erasedTree
    have actual := RegistrationNativePlatformSelectiveEntropyExecution.run_source (n := n) setup checks wire source started.native.credential seed scalar candidate provider selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys seed,started.native.credential.publicKey,serverKeyId⟩)
      ((started.native.frontend,previous),(RegistrationNativeHiddenInterpreter.initial (n := n) providerState,known))
    simp only [after,RegistrationNativePlatformSelectiveEntropyStartup.stage]
    rw [← actual]
    simp only [Functor.map_map]
    rw [RegistrationNativePlatformSelectiveCoinEmbedding.program] at erasedTree
    rw [← erasedTree]
    simp only [Functor.map_map]
    rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStartup.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStartup.erase
