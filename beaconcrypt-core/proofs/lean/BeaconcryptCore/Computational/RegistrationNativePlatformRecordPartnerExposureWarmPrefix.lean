-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureAveraged
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealInitial
/-! The actual physical uniform sampler and genuine source startup form the candidate-independent reduction prefix. Completed material tables, startup refusals and every reached physical accounting/cache field remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarmPrefix
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformG3UniformRecordProgram (Sample sample)
variable {I KemSK Physical Platform E A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public →OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create+1)) (previous : Platform)
local notation "cap"=>budget.cap 4+budget.cap 5
local notation "Ctx"=>RegistrationNativePlatformRecordPartnerExposureAveraged.Context source cap KemSK Physical Platform A mode

noncomputable def context (parameters : Sample KemSK cap) (born : RegistrationNativeHiddenStartup.Started source)
    (physicalBefore : Physical) : Ctx where
  seed:=parameters.seed
  scalar:=parameters.scalar
  sign:=RegistrationNativeMldsa.owned source born.native.credential
  profile:=parameters.profile
  front:=(RegistrationNativeG3NativeStartupFields.word born.native.frontend,previous)
  word:=(RegistrationNativePlatformLorIdealInitial.symbolicPrivate
    (RegistrationNativePlatformG3UniformOpaqueNative.privateState (KemSK:=KemSK) none budget parameters.materials)).1
  materials:=RegistrationNativeG3LocalMaterialCompletedSource.cache parameters.materials
  known:=∅
  physical:=physicalBefore
  work:=adversary ⟨setup.joint.publicKeys parameters.seed,born.native.credential.publicKey,serverKeyId⟩

noncomputable def prior
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec cap) (StateT Physical ProbComp)) (physicalBefore : Physical) :
    ProbComp (Option Ctx) := do
  let sampled←(simulateQ physical (simulateQ PqxdhRecordLiftInterface.coinLift (sample setup budget selected))).run physicalBefore
  let started←(simulateQ physical
    (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys sampled.1.seed))).run sampled.2
  pure (started.1.map (fun born=>context setup source serverKeyId mode adversary budget previous sampled.1 born started.2))

/-- Every successful prefix retains its exact sampled parameters and actual supported initialized physical state. -/
theorem support_context
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec cap) (StateT Physical ProbComp)) (physicalBefore : Physical)
    (current : Ctx) (supported : some current∈support
      (prior setup source ensureInit identityIndex serverKeyId mode adversary budget selected previous physical physicalBefore)) :
    ∃sampled : Sample KemSK cap ×Physical,
      sampled∈support ((simulateQ physical (simulateQ PqxdhRecordLiftInterface.coinLift (sample setup budget selected))).run physicalBefore) ∧
      ∃born : RegistrationNativeHiddenStartup.Started source, ∃reached : Physical,
        (some born,reached)∈support ((simulateQ physical
          (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys sampled.1.seed))).run sampled.2) ∧
        current=context setup source serverKeyId mode adversary budget previous sampled.1 born reached := by
  simp only [prior,mem_support_bind_iff,mem_support_pure_iff] at supported
  obtain ⟨sampled,drawn,started,called,equal⟩:=supported
  cases initialized : started.1 with
  | none=>simp only [initialized,Option.map_none] at equal;cases equal
  | some born=>
    simp only [initialized,Option.map_some,Option.some.injEq] at equal
    refine ⟨sampled,drawn,born,started.2,?_,equal⟩
    simpa only [←initialized,Prod.mk.eta] using called

/-- The actual prefix derives its own cold sessions and original budget; no readiness or whole-source condition is supplied. -/
theorem fields
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec cap) (StateT Physical ProbComp)) (physicalBefore : Physical)
    (bounded : ∀publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (current : Ctx) (supported : some current∈support
      (prior setup source ensureInit identityIndex serverKeyId mode adversary budget selected previous physical physicalBefore)) :
    current.front.1.server.sessions=[] ∧RegistrationNativeInterface.Respects budget current.work := by
  obtain ⟨sampled,_drawn,born,reached,called,equal⟩:=
    support_context setup source ensureInit identityIndex serverKeyId mode adversary budget selected previous physical physicalBefore current supported
  subst current
  have free : some born∈support (RegistrationNativeHiddenStartup.start (n:=cap) setup source ensureInit identityIndex serverKeyId
      (setup.joint.publicKeys sampled.1.seed)) := by
    apply OracleComp.support_simulateQ_run'_subset physical _ sampled.2
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst called
  have cold:=RegistrationNativeG3NativeStartupFields.start_cold setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys sampled.1.seed) born free
  refine ⟨?_,bounded _⟩
  simp only [context,RegistrationNativeG3NativeStartupFields.word,cold.1,List.map_nil]

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarmPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarmPrefix.support_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarmPrefix.support_context
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarmPrefix.fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarmPrefix.fields
