-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile
import BeaconcryptCore.Computational.RegistrationNativeMldsaPoolMap

/-! Actual free source Server build changes only its Server component. Every raw ML capability reply and draw count, all writer/allocator failures and external states retain the exact Beacon owners, private KEM pool and parsed ordinal. Live opaque owner credentials therefore require no closed dummy-source signing law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerOwners
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformMldsaProgram (M)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- A raw free Server action changes only the literal Server field, without restricting any named ML reply or private draw count. -/
theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Value)
    (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (reply : Value)
    (supported : ((reply, after), next) ∈ support (((RegistrationNativePlatformExperiment.server work).run before).run previous)) :
    after.beacons = before.beacons ∧ after.pool = before.pool ∧ after.parsedAccepts = before.parsedAccepts := by
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact ⟨(congrArg (fun result => result.1.2.beacons) same).symm,
    (congrArg (fun result => result.1.2.pool) same).symm,
    (congrArg (fun result => result.1.2.parsedAccepts) same).symm⟩

variable [primitive : AdapterSealPrimitive.Operations]

/-- The actual complete corrected free public build callback retains all owner credentials on every supported reply/count branch. -/
theorem build (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8))
    (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (reply : RustM (Option (U64 × Pqxdh.Bytes)))
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer (.inr (.build handle application))).run before).run previous)) :
    after.beacons = before.beacons ∧ after.pool = before.pool ∧ after.parsedAccepts = before.parsedAccepts := by
  simp only [RegistrationNativePlatformMldsaProfile.handler, StateT.run, bind_pure_comp, map_apply, support_map] at supported
  obtain ⟨⟨⟨raw, current⟩, platform⟩, called, same⟩ := supported
  have currentEq : current = after := congrArg (fun result => result.1.2) same
  cases currentEq
  exact server _ before after previous platform raw called

omit primitive in
/-- Exact owner preservation transports opaque Live rows without requiring private-key injectivity or an unchanged complete private signing log. -/
theorem owners_live (realSource : RegistrationNativeMldsa.Source) (pool : RegistrationNativeMldsaOpaque.Pool realSource)
    (before after : RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource realSource))
    (live : RegistrationNativeMldsaPoolMap.StateLive realSource pool before)
    (same : after.beacons = before.beacons) : RegistrationNativeMldsaPoolMap.StateLive realSource pool after := by
  change RegistrationNativeMldsaPoolMap.OwnersLive realSource pool after.beacons
  rw [same]
  exact live

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerOwners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerOwners.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerOwners.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerOwners.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerOwners.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerOwners.owners_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerOwners.owners_live
