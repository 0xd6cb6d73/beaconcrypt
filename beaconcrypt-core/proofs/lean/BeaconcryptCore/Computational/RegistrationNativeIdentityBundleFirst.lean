-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce
import BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
/-! Actual logged source paths retain one-use bundle phases, so a second successful publication at the same owner index is impossible. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundleFirst
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeIdentityBundlePhase (Keeps Closed)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


private theorem path_cut {before after : Whole n KemSK Platform source}
    (leading trailing : List (Call TypedSpec (Whole n KemSK Platform source)))
    (call : Call TypedSpec (Whole n KemSK Platform source))
    (path : Path actual before (leading++call::trailing) after) :
    Path actual before leading call.before ∧ Executed actual call ∧ Path actual call.after trailing after := by
  induction leading generalizing before with
  | nil =>
      cases path with
      | cons step called rest last following => exact ⟨.nil _,called,following⟩
  | cons step leading ih =>
      cases path with
      | cons head called rest last following =>
          obtain ⟨beforePath,executed,afterPath⟩ := ih following
          exact ⟨.cons step called _ _ beforePath,executed,afterPath⟩

/-- Any successful source bundle is the unique first successful publication at its original owner index, including every earlier failed attempt. -/
theorem first {before after : Whole n KemSK Platform source}
    (calls leading trailing : List (Call TypedSpec (Whole n KemSK Platform source)))
    (call : Call TypedSpec (Whole n KemSK Platform source)) (path : Path actual before calls after)
    (split : calls=leading++call::trailing) (index : Nat) (bytes : Pqxdh.Bytes)
    (marked : RegistrationNativeRawRegistrationJournal.typedMark call.query call.reply=some (.bundle index (some bytes))) :
    (calls.filterMap (fun current=>RegistrationNativeRawRegistrationJournal.typedMark current.query current.reply)).findSome?
      (RegistrationNativeRegistrationMarkCausal.bundle index)=some bytes := by
  rw [split] at path
  obtain ⟨leadingPath,called,_following⟩ := path_cut setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer leading trailing call path
  have noLeading : (leading.filterMap (fun current=>RegistrationNativeRawRegistrationJournal.typedMark current.query current.reply)).findSome?
      (RegistrationNativeRegistrationMarkCausal.bundle index)=none := by
    apply List.findSome?_eq_none_iff.mpr
    intro entry member
    obtain ⟨earlier,present,earlierMark⟩ := List.mem_filterMap.mp member
    cases entry with
    | accept packet reply => rfl
    | bundle owner reply =>
        by_cases same : owner=index
        · subst owner
          cases reply with
          | none => simp only [RegistrationNativeRegistrationMarkCausal.bundle,ite_true]
          | some priorBytes =>
              obtain ⟨_front,middle,_split,_previous,executed,between⟩ := leadingPath.member earlier present
              exact (RegistrationNativeIdentityBundleOnce.no_second setup checks wire route representation created credential view failure allocation
                reserveRegistration reservePeer reserveFrame erased helper writer earlier call executed called middle between index priorBytes bytes earlierMark marked).elim
        · simp only [RegistrationNativeRegistrationMarkCausal.bundle,same,ite_false]
  rw [split,List.filterMap_append,List.filterMap_cons,marked]
  simp only [List.findSome?_append,noLeading,Option.or, List.findSome?_cons,RegistrationNativeRegistrationMarkCausal.bundle,ite_true]

/-- The original first-publication tuple is read from those same actual bytes; signatures remain ordinary message-EUF objects and are never canonicalized. -/
theorem published {before after : Whole n KemSK Platform source}
    (calls leading trailing : List (Call TypedSpec (Whole n KemSK Platform source)))
    (call : Call TypedSpec (Whole n KemSK Platform source)) (path : Path actual before calls after)
    (split : calls=leading++call::trailing) (index : Nat) (bytes : Pqxdh.Bytes)
    (marked : RegistrationNativeRawRegistrationJournal.typedMark call.query call.reply=some (.bundle index (some bytes))) :
    RegistrationNativeRegistrationMarkCausal.published wire
      (calls.filterMap (fun current=>RegistrationNativeRawRegistrationJournal.typedMark current.query current.reply)) index =
      (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) bytes).bind PqxdhDeploymentPublishedTuple.candidateTuple := by
  rw [RegistrationNativeRegistrationMarkCausal.published,first setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer calls leading trailing call path split index bytes marked]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundleFirst

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleFirst.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleFirst.first
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleFirst.published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleFirst.published
