-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted
/-! An actual retained seal with no earlier physical counterpart publication arose at source encoding failure or real public refusal. The same original macro ledger and full source path are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginTemporalWithheld
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode handleSlot)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (Spec FullSpec Entry Handle FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {I KemSK Reader Response E Failure : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKeyId : U64) (bounds : FreshBounds)
local notation "Runtime" => CborRawRecordFlat.NativeState n E
local notation "Whole" => PqxdhDeploymentSecrecy.Ledger × Runtime
local notation "full" => RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes replace setup codec route env reserve serverKeyId bounds

include ideal readback in
/-- A hidden seal already present at an actual receive prefix, with no earlier counterpart publication, arose at a source codec failure or actual public refusal. -/
theorem withheld (initial : Runtime) (before final : Whole)
    (leading : List (Call FullSpec Whole)) (remaining : List (Call FullSpec Whole))
    (prefixPath : Path full (PqxdhDeploymentSecrecy.Ledger.empty,initial) leading before)
    (futurePath : Path full before remaining final)
    (safe : PqxdhRecordLiftProtocolHistory.Safe initial.1.2)
    (label : Label n) (entry : CtxSuccessfulSeal) (receiver : Handle) (frame : RawCtxReceive.DecodedFrame)
    (empty : (initial.2.keys label).1.successfulSeals=[])
    (present : entry∈(before.2.2.keys label).1.successfulSeals)
    (matched : PqxdhRecordFactsOriginReplay.Matches frame entry)
    (direction : label.direction = !PqxdhRecordFactsOriginHandles.handleDirection receiver)
    (unpublished : ∀sender,PqxdhRecordLiftIdeal.Counterpart (handleSlot final.2.1.2) label.slot receiver sender →
      ¬PqxdhRecordLiftIdeal.PublishedBefore codec before.1.transcript sender frame) :
    ∃ (outerCall : Call FullSpec Whole), ∃ pre post, ∃ (inner : Call Spec Runtime), ∃ nativePre nativePost sender,
      leading=pre++outerCall::post ∧ Path full (PqxdhDeploymentSecrecy.Ledger.empty,initial) pre outerCall.before ∧
      Executed full outerCall ∧ Path full outerCall.after post before ∧
      Path (RegistrationNativePlatformGatedRecordFreshCoupling.nativeImpl modes replace setup codec route env reserve)
        outerCall.before.2 nativePre inner.before ∧
      Executed (RegistrationNativePlatformGatedRecordFreshCoupling.nativeImpl modes replace setup codec route env reserve) inner ∧
      Path (RegistrationNativePlatformGatedRecordFreshCoupling.nativeImpl modes replace setup codec route env reserve)
        inner.after nativePost outerCall.after.2 ∧
      PqxdhRecordFactsOriginHandles.OwnsLabel final.2.1.2 label sender ∧
      (codec.frameWrite frame=none ∨ (⟨.inl inner.query,inner.reply⟩ : Entry).published=none) := by
  obtain ⟨outerCall,pre,post,inner,nativePre,nativePost,sender,sourceFrame,split,prior,called,later,transcript,
    absentEarlier,absent,presentAfter,nativePrefix,nativeCalled,nativeSuffix,innerSafe,innerAbsent,innerPresent,owned,ownedBefore,sourceMatched,outcome⟩ :=
    RegistrationNativePlatformOriginFullPrefix.acquired modes ideal replace setup codec route readback env reserve serverKeyId bounds
      initial before leading prefixPath safe label entry empty present
  have beforeSafe := (RegistrationNativePlatformOriginFullPrefix.full_path modes ideal replace setup codec route env reserve
    serverKeyId bounds prefixPath safe).step.1
  have advanced := RegistrationNativePlatformOriginFullPrefix.full_path modes ideal replace setup codec route env reserve
    serverKeyId bounds futurePath beforeSafe
  have ownedFinal := PqxdhRecordFactsOriginHandles.ownsLabel_step _ _ advanced.step label sender ownedBefore
  have frames := PqxdhRecordFactsOriginAccepted.matches_unique sourceFrame frame entry sourceMatched matched
  subst sourceFrame
  refine ⟨outerCall,pre,post,inner,nativePre,nativePost,sender,split,prior,called,later,nativePrefix,nativeCalled,nativeSuffix,ownedFinal,?_⟩
  rcases outcome with failed | refused | ⟨encrypted,published,decoded⟩
  · exact Or.inl failed
  · exact Or.inr refused
  · have absentPublication := unpublished sender
      (PqxdhRecordFactsOriginHandles.counterpart_of_opposite final.2.1.2 label sender receiver ownedFinal direction)
    apply False.elim
    apply absentPublication
    refine ⟨encrypted,?_,decoded⟩
    have recorded := RegistrationNativePlatformOriginFullPrefix.transcript modes ideal replace setup codec route readback env reserve
      serverKeyId bounds prefixPath safe
    rw [PqxdhDeploymentSecrecy.Ledger.empty, List.nil_append] at recorded
    rw [recorded,List.mem_filterMap]
    refine ⟨⟨outerCall.query,outerCall.reply⟩,?_,published⟩
    rw [List.mem_map]
    exact ⟨outerCall,by rw [split];exact List.mem_append_right _ (List.mem_cons_self),rfl⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginTemporalWithheld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginTemporalWithheld.withheld' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginTemporalWithheld.withheld
