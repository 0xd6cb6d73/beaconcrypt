-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationLoop
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationReceipts
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd
/-! Protected ML authentication origin is measured from the actual chronological source callback log and the same physical cache. The same supported initialized source run maps to its typed audit; the source monitor and actual startup derive event containment internally. Startup reuses the configured Ed sampler with pure-true admission, and the loss retains the original shared-hash birthday term and ordinary weak-EUF family. -/
open CoreModels Aeneas OracleComp OracleSpec ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)

variable {Value :Type}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "AuditState"=>RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source

noncomputable def event (publication :RegistrationNativeExperiment.Public)
    (_value :Value×RegistrationNativeLedger.State)
    (stored :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) :Bool :=by
  classical
  exact decide (RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.flag configuration.view publication.mldsaPublic stored.backend.2.2=true ∨
    CacheHasCollision stored.backend.1.world.primitive.2)

theorem audit_program (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (work :OracleComp RegistrationNativePlatformPublicAdapterLowSpec.Spec Value)
    (before :RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential) :
    (fun result:Value×RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential=>(result.1,result.2.1.1)) <$>
      (simulateQ (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential) work).run before=
      (simulateQ (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential) work).run before.1.1 :=by
  have native:=RegistrationNativePlatformExtractedSdkPublic.program
    (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential)
    (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential)
    (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential) work before.1
  rw [←RegistrationNativePlatformPublicAdapterLoggedJoint.program_erase configuration created credential work before] at native
  simpa only [Functor.map_map,Prod.map,id_eq,RegistrationNativePlatformExtractedSdkPublic.project] using native

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem source_cache (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (current :RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential) :
    (RegistrationNativePlatformPublicAdapterLoggedJoint.sourceState configuration created credential current).backend.1.world.primitive.2=
      current.1.1.1.1.server.world.world.1.primitive.2 :=
  RegistrationNativePlatformPublicAdapterLedgerExecution.cache configuration created credential current.1.1 current.1.2


omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem included (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (publication :RegistrationNativeExperiment.Public) (publicKey :publication.mldsaPublic=credential.publicKey)
    (current :RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential)
    (held :RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.Invariant configuration created credential current)
    (value :Value×RegistrationNativeLedger.State)
    (marked :event configuration publication value (RegistrationNativePlatformPublicAdapterLoggedJoint.sourceState configuration created credential current)=true) :
    current.1.1.2.bad=true ∨CacheHasCollision current.1.1.1.1.server.world.world.1.primitive.2 :=by
  classical
  have actual:=of_decide_eq_true marked
  rcases actual with unsigned|collision
  · change RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.flag configuration.view publication.mldsaPublic current.2=true at unsigned
    rw [publicKey] at unsigned
    exact Or.inl (held.2 unsigned)
  · exact Or.inr ((source_cache configuration created credential current) ▸collision)



theorem program_bound (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
    (publication :RegistrationNativeExperiment.Public) (publicKey :publication.mldsaPublic=credential.publicKey)
    (work :OracleComp RegistrationNativePlatformPublicAdapterLowSpec.Spec (Value×RegistrationNativeLedger.State))
    (before :RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential)
    (held :RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.Invariant configuration created credential before) :
    Pr{let result←(simulateQ (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential) work).run before}[event configuration publication result.1 (RegistrationNativePlatformPublicAdapterLoggedJoint.sourceState configuration created credential result.2)=true]≤
    Pr{let result←(simulateQ (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential) work).run before.1.1}[result.2.2.bad=true ∨CacheHasCollision result.2.1.1.server.world.world.1.primitive.2] :=by
  rw [←audit_program configuration created credential work before,prEvent_map]
  apply prEvent_mono_of_support
  intro result supported marked
  exact included configuration created credential publication publicKey result.2
    (RegistrationNativePlatformPublicAdapterSourceAuthenticationLoop.program configuration created credential work before held result supported) result.1 marked

variable [AdapterServerConstructorPrimitive.Standard]

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem cold (previous :P) (identityIndex :Nat) (identifier :U64) (rng :R)
    (packet :{value //value∈support (RegistrationNativePlatformPublicAdapterInitializationPhysical.raw (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng)})
    (ready :AdapterServerConstructorInitialized.Ready n KemSK R source) (returned :packet.val.1.ready=some ready)
    (stored :RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup configuration.view configuration.views ready.initial.created ready.initial.credential (ready.initial.state,previous)) :
    RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.Invariant configuration ready.initial.created ready.initial.credential
      (⟨((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩,[]) :=by
  constructor
  · exact RegistrationNativePlatformPublicAdapterInitializationReceipts.ready setup configuration.generator configuration.view previous identityIndex identifier rng packet.val ready packet.property returned
  · intro impossible
    change false=true at impossible
    cases impossible


variable (objects :AdapterServerConstructorObjects.Leaves configuration.views)
variable (ensureInit :StateT Unit ProbComp Bool)
variable (serverEd :AdapterServerConstructorJoint.EdContract configuration.generator configuration.view setup.joint (AdapterServerConstructorStartup.edCore ensureInit))
variable (identityIndex :Nat) (identifier :U64) (rng :R)
variable (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)

include objects serverEd in
theorem common_bound (previous :P) :
    Pr{let result←(RegistrationNativePlatformPublicAdapterLoggedExecution.commonProfile (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary (event configuration)).run previous}[result.1=true]≤
      Pr{let bad←RegistrationNativePlatformPublicAdapterAuditSecurity.game (n:=n) configuration identityIndex identifier rng bounds mode adversary previous}[bad=true] :=by
  classical
  unfold RegistrationNativePlatformPublicAdapterLoggedExecution.commonProfile RegistrationNativePlatformPublicAdapterAuditSecurity.game
  simp only [StateT.run]
  apply prEvent_bind_mono_of_forall_le
  rintro ⟨⟨⟨constructor,choice⟩,world⟩,supported⟩
  cases choice with
  | none=>simp
  | some ready=>
    dsimp only
    let packet :{value //value∈support (RegistrationNativePlatformPublicAdapterInitializationPhysical.raw (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng)}:=⟨(⟨constructor,some ready⟩,world),supported⟩
    let stored:=RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit serverEd
      configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready rfl
    let start:RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration ready.initial.created ready.initial.credential:=
      (⟨((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩,[])
    have initial:=cold configuration previous identityIndex identifier rng packet ready rfl stored
    have estimate:=program_bound configuration ready.initial.created ready.initial.credential ready.initial.public rfl
      (RegistrationNativePlatformPublicAdapterLedgerExecution.work (setup:=setup) bounds mode adversary ready.initial.public) start initial
    rw [prEvent_map,prEvent_map]
    simpa only [start,stored,packet,StateT.run,RegistrationNativePlatformPublicAdapterExecution.observe,RegistrationNativePlatformPublicAdapterSourceRuntime.embed,
      RegistrationNativePlatformPublicAdapterSourceRuntime.join,RegistrationNativePlatformPublicAdapterSourceRuntime.objects,
      event,decide_eq_true_eq] using estimate


include objects in
theorem protected_origin (previous :P) (budget :PqxdhDeploymentInterface.Budget)
    (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication)) :
    Pr{let result←(RegistrationNativePlatformPublicAdapterExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary
      (event configuration)).run previous}[result.1=true]≤
      RegistrationNativePlatformPublicAdapterAuditSecurity.loss (n:=n) configuration (pure true) identityIndex identifier bounds mode adversary previous budget :=by
  have actual:=common_bound (n:=n) configuration objects (pure true)
    (RegistrationNativePlatformPublicAdapterUnifiedStartupEd.contract configuration) identityIndex identifier rng bounds mode adversary previous
  rw [RegistrationNativePlatformPublicAdapterLoggedExecution.common_source (n:=n) configuration objects (pure true)
    (RegistrationNativePlatformPublicAdapterUnifiedStartupEd.contract configuration) identityIndex identifier rng bounds mode adversary (event configuration)] at actual
  exact actual.trans (RegistrationNativePlatformPublicAdapterAuditSecurity.bound (n:=n) configuration objects (pure true)
    (RegistrationNativePlatformPublicAdapterUnifiedStartupEd.contract configuration) identityIndex identifier rng bounds mode adversary previous budget bounded)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.audit_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.audit_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.source_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.source_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.included' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.included

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.cold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.cold

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.common_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.common_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.protected_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthenticationSecurity.protected_origin
