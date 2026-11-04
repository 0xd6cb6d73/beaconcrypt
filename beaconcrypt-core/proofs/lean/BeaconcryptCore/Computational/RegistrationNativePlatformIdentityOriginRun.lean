-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginObserved
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginCaps
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginFinal
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun
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
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativePlatformIdentityOriginObserved (Observed)
open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
local notation "cfgClient" => RegistrationNativePlatformIdentityOriginObserved.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

/-- A retained initialized source result exposes its own startup, adaptive run and final retrospective report states. -/
theorem client_receipt (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (count : Nat) (observed : Observed n KemSK Platform Value source) (after : MonitorState count)
    (supported : (some observed,after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous))) :
    ∃ initial starting reached,
      (some initial,starting) ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
        (simulateQ RegistrationNativeIdentityMain.coins (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId))).run
          (RegistrationNativeIdentityReportMonitor.initial count)) ∧
      (observed,reached) ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
        ((RegistrationNativePlatformIdentityMainFull.run setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          bounds mode (adversary initial.public)).run (RegistrationNativePlatformIdentityMainProfile.fromInitial initial previous))).run starting) ∧
      ((),after) ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
        (RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityFinalReports.reports
          (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) observed.1.2.transcript observed.2.1.beacons))).run reached) := by
  unfold RegistrationNativePlatformIdentityOriginObserved.client PqxdhJointPhase1Reports.run at supported
  simp only [simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨initialized,starting,continued⟩ := supported
  cases selected : initialized.1 with
  | none =>
    simp only [selected,simulateQ_pure,StateT.run_pure,mem_support_pure_iff,Prod.mk.injEq,
      Option.some_ne_none,false_and] at continued
  | some initial =>
    simp only [selected,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at continued
    obtain ⟨finished,reached,emitted⟩ := continued
    obtain ⟨reported,called,returned⟩ := emitted
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff,Prod.mk.injEq,Option.some.injEq] at returned
    obtain ⟨rfl,rfl⟩ := returned
    refine ⟨initial,initialized.2,finished.2,?_,reached,?_⟩
    · rw [←selected]
      exact starting
    · have unit : reported.1 = () := Subsingleton.elim _ _
      simpa only [←unit,Prod.mk.eta] using called

/-- The final retained current owner roster is synchronized with the same ordinary source histories after its report batch. -/
theorem client_inv (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (count : Nat) (observed : Observed n KemSK Platform Value source) (after : MonitorState count)
    (supported : (some observed,after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous))) :
    RegistrationNativePlatformIdentityMainHistory.Inv setup.joint (observed.2,privatePool after) := by
  obtain ⟨initial,starting,reached,started,ran,reported⟩ := client_receipt setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous count observed after supported
  have empty := RegistrationNativeIdentityOriginRun.coins_pool setup.joint count _ _ _ started
  have projected := Set.mem_image_of_mem (Prod.map id privatePool) ran
  rw [←support_map,RegistrationNativeIdentityReportSource.program_source] at projected
  have prior : RegistrationNativePlatformIdentityMainHistory.Inv setup.joint
      (RegistrationNativePlatformIdentityMainProfile.fromInitial initial previous,privatePool starting) := by
    apply (RegistrationNativePlatformIdentityMainHistory.projection_inv setup.joint _).mp
    change RegistrationNativePlatformIdentityMainHistory.Inv setup.joint
      (RegistrationNativePlatformIdentityMainProfile.fromInitial initial previous,RegistrationNativeIdentityCompiler.poolView (privatePool starting))
    rw [empty]
    exact RegistrationNativePlatformIdentityMainHistoryRun.initial_inv setup.joint _ previous
  have invariant := RegistrationNativePlatformIdentityMainHistoryRun.run_inv setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    bounds mode (adversary initial.public) (RegistrationNativePlatformIdentityMainProfile.fromInitial initial previous,privatePool starting)
    (observed.1,(observed.2,privatePool reached)) prior (by
      change (observed.1,(observed.2,privatePool reached)) ∈ support
        ((fun evaluated => (evaluated.1.1,(evaluated.1.2,evaluated.2))) <$>
          (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
            ((RegistrationNativePlatformIdentityMainFull.run setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
              bounds mode (adversary initial.public)).run (RegistrationNativePlatformIdentityMainProfile.fromInitial initial previous))).run (privatePool starting))
      rw [support_map]
      exact Set.mem_image_of_mem _ projected)
  rw [RegistrationNativeIdentityOriginRun.emit_pool setup.joint count _ reached ((),after) reported]
  exact invariant

/-- Every final retained generated owner fits the original finite identity budget, including future-born aliases. -/
theorem client_fits (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (count : Nat) (room : budget.create ≤ count) (observed : Observed n KemSK Platform Value source) (after : MonitorState count)
    (supported : (some observed,after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous)))
    (owner : RegistrationNativeIdentityFrontend.Owner source) (member : owner ∈ observed.2.1.beacons) :
    owner.identity.handle < count := by
  have invariant := client_inv setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous count observed after supported
  obtain ⟨seed,stored⟩ := invariant.1.1 owner member
  have valid := (List.getElem?_eq_some_iff.mp stored.1).1
  change owner.identity.handle < (privatePool after).seeds.length at valid
  have grows := RegistrationNativeIdentityReportCapacity.program_growth setup.joint count _ budget.create
    (RegistrationNativePlatformIdentityOriginCaps.client_creates (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded)
    (RegistrationNativeIdentityReportMonitor.initial count) (some observed,after) supported
  change (privatePool after).seeds.length ≤ 0 + budget.create at grows
  omega

/-- The complete retained source client reveals no generated signing seed, including its final reports. -/
theorem client_unrevealed (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (count : Nat) (observed : Observed n KemSK Platform Value source) (after : MonitorState count)
    (supported : (some observed,after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous))) :
    after.1.snapshot.history.reveals = [] :=
  RegistrationNativeIdentityReportFresh.program_reveals setup.joint count _
    (RegistrationNativePlatformIdentityOriginCaps.client_no_reveal (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous)
    (RegistrationNativeIdentityReportMonitor.initial count) (some observed,after) supported

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun.client_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun.client_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun.client_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun.client_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun.client_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun.client_fits

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun.client_unrevealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun.client_unrevealed
