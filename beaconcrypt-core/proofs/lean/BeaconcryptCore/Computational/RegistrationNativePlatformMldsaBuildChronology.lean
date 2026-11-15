-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology

/-! The full actual source SDK build retains same-position raw signing attempts and native unsigned-payload receipts. Every prefix law is instantiated with actual pure pin selection, shared AD hashing, reservation, occupancy, source first record, signature, encoder and install bodies. No complete-build preservation premise is exposed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBuildChronology
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformMldsaPublicationChronology (Keeps)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativePlatformMldsaSdkPrefixChronology (receipts)
variable {n : Nat} {E Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential (handleSource source))
variable [primitive : AdapterSealPrimitive.Operations]

/-- Actual complete source build, including every failed prefix and all private counts, derives chronological alignment from its real leaf bodies. -/
theorem build (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) :
    Keeps source (receipts (n := n))
      (RegistrationNativePlatformMldsaServer.build (handleSource source) credential setup codec view failure allocation erased reservePeer helper writer handle application) := by
  unfold RegistrationNativePlatformMldsaServer.build
  exact RegistrationNativePlatformMldsaSdkChronology.build source _
    (RegistrationNativePlatformMldsaSdkPrefixChronology.adHash source coins) _
    (RegistrationNativePlatformMldsaSdkPrefixChronology.pin source coins) _
    (RegistrationNativePlatformMldsaSdkPrefixChronology.reserve source reservePeer) _
    (RegistrationNativePlatformMldsaSdkPrefixChronology.present source coins) _
    (RegistrationNativePlatformMldsaServerChronology.finish source credential setup codec view failure allocation erased helper writer) handle application

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBuildChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBuildChronology.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBuildChronology.build
