-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
/-! The current registration seal child executes the checked extracted request controller on the same primitive and outer platform state. The exact seal and Server build equalities consume the source-controller refinement; they preserve source failure/divergence and the original analysis request receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {E Auxiliary Value I KemSK Reader Response : Type} {base : OracleSpec I}
variable {m : Type →Type} [Monad m] [LawfulMonad m]
variable (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m)

noncomputable def sealing (request : record_effects.AeadSealRequest) :
    StateT (RegistrationWorldAgreement.State n Auxiliary) m (RustM AdapterSealNative.Output) := do
  let result←simulateQ (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation ∘ₛ AdapterSealNative.native)
    (AdapterSealRequestExtraction.execute (E:=E) (m:=AdapterSealRequestMonad.Program E) request).run
  modify fun before=>{before with recordRequests:=before.recordRequests++[RegistrationWorldAgreement.recordCall (.seal request)]}
  pure result

/-- The actual extracted source controller is the current child, including its complete persistent poststate and failure result. -/
theorem sealing_source (request : record_effects.AeadSealRequest) :
    sealing (n:=n) (Auxiliary:=Auxiliary) coins setup codec view failure allocation request=
      RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request :=
  (RegistrationNativePlatformSourceSeal.source coins setup codec view failure allocation request).symm

noncomputable def build (erased : commitment.CommitmentTranscript) (reservePeer : m Bool)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (handle : Nat) (application : Option (Slice U8)) :=
  RegistrationNativePlatformSourceBuild.buildSource (n:=n) coins setup codec
    (sealing coins setup codec view failure allocation)
    (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) reservePeer sign helper writer handle application

/-- Actual Server build uses the same extracted seal child on every continued source branch. -/
theorem build_source (erased : commitment.CommitmentTranscript) (reservePeer : m Bool)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (handle : Nat) (application : Option (Slice U8)) :
    build (n:=n) coins setup codec view failure allocation erased reservePeer sign helper writer handle application=
      RegistrationNativePlatformSourceSeal.build coins setup codec view failure allocation erased reservePeer sign helper writer handle application :=
  (RegistrationNativePlatformSourceSeal.build_source coins setup codec view failure allocation erased reservePeer sign helper writer handle application).symm

/-- Any continuation sees the same returned Rust result and complete reached state. -/
theorem continued (request : record_effects.AeadSealRequest)
    (next : RustM AdapterSealNative.Output →StateT (RegistrationWorldAgreement.State n Auxiliary) m Value) :
    (do let reply←sealing coins setup codec view failure allocation request;next reply)=
      (do let reply←RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request;next reply) := by
  rw [sealing_source]

/-- Persistent platform allocation and the full primitive/world state are retained jointly at arbitrary inputs. -/
theorem joint {Platform : Type} (publicCoins : QueryImpl unifSpec (StateT Platform ProbComp))
    (publicAllocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (request : record_effects.AeadSealRequest) (before : RegistrationWorldAgreement.State n Auxiliary) (previous : Platform) :
    ((sealing publicCoins setup codec view failure publicAllocation request).run before).run previous=
      ((RegistrationNativePlatformSourceSeal.sealing publicCoins setup codec view failure publicAllocation request).run before).run previous := by
  rw [sealing_source]

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal.sealing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal.sealing_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal.build_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal.continued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal.continued

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal.joint
