-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace

/-! The selected runtime's actual source cache extends and configured pin remains fixed across every callback, including failed dynamic writer gates. The same-run path preserves the actual configured Server binding and complete public key. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState
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

open RegistrationNativeWorldCache (cache)

omit primitive in
private theorem after_cut (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : RegistrationNativePlatformOrdinaryExperiment.M n KemSK source Platform (Option RawCtxSourceSend.Encrypted))
    (before : Native) (previous : Platform) (result : (Option RawCtxSourceSend.Encrypted × Native) × Platform)
    (supported : result ∈ support
      (((RegistrationNativePlatformOrdinaryExperimentRouting.after reserve work).run before).run previous)) :
    ∃ middle ∈ support ((work.run before).run previous), result.1.2 = middle.1.2 := by
  simp only [RegistrationNativePlatformOrdinaryExperimentRouting.after, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at continued
  obtain ⟨gated, _reserved, same⟩ := continued
  exact ⟨middle, called, (congrArg (fun result => result.1.2) same).symm⟩

/-- The exact native runtime cache extends and its configured pin is retained on every outcome. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : Native) (previous : Platform)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × Native) × Platform)
    (supported : result ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run before).run previous)) :
    cache before ≤ cache result.1.2 ∧ result.1.2.server.pin = before.server.pin := by
  rw [RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal] at supported
  have prior (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
      (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × Native) × Platform)
      (called : result ∈ support (((RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created source credential view failure allocation
          reserveRegistration reservePeer erased helper writer query).run before).run previous)) :
      cache before ≤ cache result.1.2 ∧ result.1.2.server.pin = before.server.pin :=
    ⟨RegistrationNativePlatformHandlerCache.handler RegistrationNativePlatformMldsaProgram.coins setup checks
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer query before previous result called,
      RegistrationNativePlatformServerPinTrace.handler_pin RegistrationNativePlatformMldsaProgram.coins setup checks
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer query before previous result called⟩
  have gated (work : RegistrationNativePlatformOrdinaryExperiment.M n KemSK source Platform (Option RawCtxSourceSend.Encrypted))
      (keeps : ∀ middle, middle ∈ support ((work.run before).run previous) →
        cache before ≤ cache middle.1.2 ∧ middle.1.2.server.pin = before.server.pin)
      (result : (Option RawCtxSourceSend.Encrypted × Native) × Platform)
      (called : result ∈ support (((RegistrationNativePlatformOrdinaryExperimentRouting.after reserveFrame work).run before).run previous)) :
      cache before ≤ cache result.1.2 ∧ result.1.2.server.pin = before.server.pin := by
    obtain ⟨middle, reached, same⟩ := after_cut reserveFrame work before previous result called
    rw [same]
    exact keeps middle reached
  cases query with
  | inl coin => exact prior _ result supported
  | inr query => cases query with
    | serverSend key plaintext => exact gated _ (fun middle reached => prior (.inr (.serverSend key plaintext)) middle reached) result supported
    | beaconSend owner plaintext => exact gated _ (fun middle reached => prior (.inr (.beaconSend owner plaintext)) middle reached) result supported
    | _ => exact prior _ result supported

/-- The packed literal runtime callback has the same monotone cache and immutable pin. -/
theorem callback (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (called : Executed impl call) :
    cache call.before.1 ≤ cache call.after.1 ∧ call.after.1.server.pin = call.before.1.server.pin := by
  simp only [Executed, RegistrationNativePlatformOrdinaryKemClientJournal.actual, RegistrationNativePlatformPackedState.pack,
    StateT.run, support_map] at called
  obtain ⟨⟨⟨value, native⟩, platform⟩, supported, same⟩ := called
  have replyEq : value = call.reply := congrArg Prod.fst same
  have nativeEq : native = call.after.1 := congrArg (fun result => result.2.1) same
  have platformEq : platform = call.after.2 := congrArg (fun result => result.2.2) same
  rw [replyEq, nativeEq, platformEq] at supported
  exact handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer call.query call.before.1 call.before.2 ((call.reply, call.after.1), call.after.2) supported

/-- A complete actual runtime path retains one shared growing cache and one configured pin. -/
theorem path {before after : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl before calls after) : cache before.1 ≤ cache after.1 ∧ after.1.server.pin = before.1.server.pin := by
  induction reached with
  | nil => exact ⟨le_refl _, rfl⟩
  | cons call called rest last following ih =>
      obtain ⟨extension, pinEq⟩ := callback setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer call called
      exact ⟨extension.trans ih.1, ih.2.trans pinEq⟩

/-- The configured Server binding and complete public key remain true at every later path endpoint. -/
theorem pinned (referenceBinding : pqxdh.ServerBinding) (referencePublicKey : Std.Array U8 1952#usize) {before after : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl before calls after)
    (cached : RegistrationNativeServerPinCached.Configured before.1.server.pin referenceBinding referencePublicKey) :
    RegistrationNativeServerPinCached.Configured after.1.server.pin referenceBinding referencePublicKey := by
  obtain ⟨_extension, pinEq⟩ := path setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer reached
  rw [pinEq]
  exact cached

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState.pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState.pinned
