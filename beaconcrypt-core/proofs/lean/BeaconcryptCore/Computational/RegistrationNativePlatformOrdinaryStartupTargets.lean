-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginProbability
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRunPacking
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginBound
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile

/-! The complete current dynamic-writer native profile is interpreted by one executable ordinary joint-Ed client. Startup constructs the independent Server/ML/KEM auxiliary state internally; the challenged Beacon Ed seed is supplied only by its generated indexed service. Every constructor/API failure and full shared P poststate is retained. This is source correspondence, not yet a publication-security reduction or restricted-root confidentiality client. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project liftMain)
open RegistrationNativePlatformIdentityMainOwned (Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
local notation "cfgClient" => RegistrationNativePlatformIdentityOriginObserved.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value) (previous : Platform)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
abbrev Outcome := Option (RegistrationNativeEvents.Observed Value Native × Platform)

noncomputable def outcome : ProbComp (Outcome (n := n) (KemSK := KemSK) (Platform := Platform) (Value := Value) (source := source)) :=
  RegistrationNativePlatformIdentityOriginObserved.native (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds .P adversary previous

/-- The original event keeps its full actual P poststate in the optional initialized outcome. -/
theorem profile_outcome (event : RegistrationNativeEvents.Observed Value Native → Bool) :
    (RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds .P adversary event).run previous =
    (fun result : Outcome (n := n) (KemSK := KemSK) (Platform := Platform) (Value := Value) (source := source) => match result with
      | none => (false,previous)
      | some observed => (event observed.1,observed.2)) <$>
      outcome setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds adversary previous :=
  (RegistrationNativePlatformIdentityOriginProbability.native_profile setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds .P adversary previous event).symm

/-- Boolean event probability is the same original optional outcome probability, without discarding platform effects from execution. -/
theorem profile_probability (event : RegistrationNativeEvents.Observed Value Native → Bool) :
    Pr{let result ← ((RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds .P adversary event).run previous)}[result.1 = true] =
    Pr{let result ← (outcome setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds adversary previous)}[result.any (fun observed => event observed.1) = true] := by
  rw [profile_outcome,prEvent_map]
  apply prEvent_congr
  intro result
  cases result <;> rfl

/-- A supported actual startup result exposes the same literal full raw native/platform execution. -/
theorem run_receipt (observed : RegistrationNativeEvents.Observed Value Native × Platform)
    (supported : some observed ∈ support (outcome setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds adversary previous)) :
    ∃ initial,some initial ∈ support (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) ∧
      (((observed.1.1,observed.1.2.1),observed.1.2.2),observed.2) ∈ support
        ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation initial.created source initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          bounds .P (adversary initial.public) initial.state).run previous) := by
  simp only [outcome,RegistrationNativePlatformIdentityOriginObserved.native,mem_support_bind_iff] at supported
  obtain ⟨initialized,started,continued⟩ := supported
  cases initialized with
  | none => simp only [support_pure,Set.mem_singleton_iff,reduceCtorEq] at continued
  | some initial =>
    simp only [support_map,Set.mem_image,Option.some.injEq] at continued
    obtain ⟨actual,reached,rfl⟩ := continued
    exact ⟨initial,started,reached⟩

/-- Exact packing supplies the generic full compiler support for the same original initialized native/platform outcome. -/
theorem full_receipt (observed : RegistrationNativeEvents.Observed Value Native × Platform)
    (supported : some observed ∈ support (outcome setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds adversary previous)) :
    ∃ initial,some initial ∈ support (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId) ∧
      (observed.1.1,(observed.1.2.1,(observed.1.2.2,observed.2))) ∈ support
        (RegistrationNativeFullCompiler.run setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds
          (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
          .P (adversary initial.public) (initial.state,previous)) := by
  obtain ⟨initial,started,ran⟩ := run_receipt setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds adversary previous observed supported
  exact ⟨initial,started,RegistrationNativePlatformOrdinaryRunPacking.supported setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    bounds .P (adversary initial.public) initial.state previous (((observed.1.1,observed.1.2.1),observed.1.2.2),observed.2) ran⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets.profile_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets.profile_outcome

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets.profile_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets.profile_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets.run_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets.run_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets.full_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryStartupTargets.full_receipt
