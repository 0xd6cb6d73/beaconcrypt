-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCallback
import BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource

/-! The actual corrected free stopping program and its true-count shared-table execution are equal jointly in candidate, native state, full platform state and private pool. Only product reassociation is performed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedSource
open BeaconcryptCore.Refinement
open RegistrationNativeMldsaOpaque (handleSource Pool)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential (handleSource source))
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Every adaptive actual corrected free stopped run equals the literal table callback stopped at the same authentication cut. -/
theorem native (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (current : RegistrationNativePlatformMldsaCountStop.State n KemSK Platform (handleSource source))
    (previous : Option RegistrationNativeMldsaEuf.Forgery) (pool : Pool source) :
    RegistrationNativeMldsaStoppedSource.arrange source <$>
      RegistrationNativeMldsaTableProgram.runState source
        (simulateQ (RegistrationNativeMldsaStop.freeze
          (RegistrationNativePlatformMldsaCountStop.handler (n := n) setup checks wire route representation created credential view failure allocation
            reserveRegistration reservePeer erased helper writer)
          (RegistrationNativePlatformMldsaCountStop.observe publicKey) defaultReply) work) (current, previous) pool =
      (simulateQ (RegistrationNativeMldsaStop.freeze
        (RegistrationNativePlatformMldsaTableCallback.callback (n := n) source setup checks wire route representation created credential view failure allocation
          reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaTableCallback.observe source publicKey) defaultReply) work).run ((current, pool), previous) := by
  have callbacks : RegistrationNativeMldsaStoppedSource.callback source
      (RegistrationNativePlatformMldsaCountStop.handler (n := n) setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer) =
      RegistrationNativePlatformMldsaTableCallback.callback (n := n) source setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer := by
    funext query before
    exact (RegistrationNativePlatformMldsaTableCallback.generic source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query before).symm
  rw [← callbacks]
  exact RegistrationNativeMldsaStoppedSource.program source _ _ defaultReply work current previous pool
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaStoppedSource.native
