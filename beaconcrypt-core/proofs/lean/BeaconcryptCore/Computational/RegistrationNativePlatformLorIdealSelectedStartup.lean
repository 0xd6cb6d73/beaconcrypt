-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealCborSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceStateProperties
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRun
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstallPeer
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage
/-! Original broadly designated peers have their exact protected descriptor at the same source installation ordinal under arbitrary persistent World interpretation. Original replies, every failed prefix and the full platform/private chronology are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetPath (Path)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Secret Reader Response A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity)
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "nativeInput" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "nativeInside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "publicPrekey" => setup.dh.publicKey scalar
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge
variable (candidate : MlKemSharedSecret) (previous : Platform)
    (privateBefore : NativePrivate n KemSK)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "provider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge candidate
local notation "job" => RegistrationNativePlatformSelectiveRecordTraceState.program setup checks RegistrationNativePlatformConcreteSource.wire seed scalar candidate provider
  (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  previous privateBefore ensureInit identityIndex serverKeyId bounds mode adversary
local notation "physical" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route
local notation "TraceResult" => RegistrationNativePlatformSelectiveRecordTraceHidden.Result n KemSK RegistrationNativeKemSwitchSource.Phase Platform Secret A source
local notation "StageResult" => RegistrationNativePlatformLorIdealCborSelected.Result n KemSK Platform Secret A source

private def package (born : RegistrationNativeHiddenStartup.Started source) (observed : StageResult) : TraceResult :=
  (((some (PqxdhRegistrationJointServerBirth.encode born.created,observed.1.1.1.1.1.1,
    ((observed.1.1.1.1.1.2,observed.1.1.1.2),observed.1.1.1.1.2)),observed.1.1.2),observed.1.2),observed.2)

private noncomputable def stage (born : RegistrationNativeHiddenStartup.Started source) :=
  (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire (RegistrationNativeMldsa.owned source born.native.credential)
    seed scalar candidate provider) (RegistrationNativeG2Trace.program (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source
        (RegistrationNativeMldsa.owned source born.native.credential) target.2.val target.1.val publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) (born.native.frontend,previous))))).run privateBefore

private theorem startup_stage (initialSecret : Secret) (result : TraceResult)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route job
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret))
    (finished : PqxdhRegistrationJointServerBirth.ClientCreated PqxdhTranscriptAd.AssociatedData × (A × RegistrationNativeLedger.State) ×
      RegistrationNativePlatformSelectiveRecordTraceStartup.Extra n KemSK RegistrationNativeKemSwitchSource.Phase Platform source)
    (present : finished ∈ result.1.1.1) :
    ∃ (born : RegistrationNativeHiddenStartup.Started source) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) (observed : StageResult),
      some born ∈ support (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)) ∧
      observed ∈ support (CborRawRecordOriginFlatten.interpret service codec route
        (stage setup checks source seed scalar pairs chosen challenge view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
          serverKeyId bounds mode adversary budget target candidate previous privateBefore born) shell control secret) ∧
      result=package source born observed := by
  unfold RegistrationNativePlatformSelectiveRecordTraceState.program at supported
  rw [CborRawRecordOriginFlatten.interpret_bind,mem_support_bind_iff] at supported
  obtain ⟨initialized,startupSupport,continued⟩ := supported
  rcases initialized with ⟨⟨⟨initialized,shell⟩,control⟩,secret⟩
  cases initialized with
  | none =>
    rw [CborRawRecordOriginFlatten.interpret_pure,mem_support_pure_iff] at continued
    subst result
    cases present
  | some born =>
    have actual := Set.mem_image_of_mem (fun returned => (returned.1.1.1,(returned.1.1.2,(returned.1.2,returned.2)))) startupSupport
    rw [←support_map,←RegistrationNativePlatformLorIdealPhysical.program_source service codec route _
      (CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,initialSecret))] at actual
    have free : some born ∈ support (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)) := by
      apply OracleComp.support_simulateQ_run'_subset physical _ (CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,initialSecret))
      rw [StateT.run'_eq,support_map]
      exact Set.mem_image_of_mem Prod.fst actual
    simp only [RegistrationNativePlatformSelectiveRecordTraceState.after,RegistrationNativeHiddenEnvironmentWorld.interpret_map,support_map] at continued
    obtain ⟨observed,called,equal⟩ := continued
    exact ⟨born,shell,control,secret,observed,free,called,equal.symm⟩

omit primitive in
private theorem startup_pin (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (born : RegistrationNativeHiddenStartup.Started source)
    (supported : some born ∈ support (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity)) :
    PqxdhRefinement.absBytes born.native.frontend.server.pin.binding.identity_public_key = identity.ed25519.toList := by
  simp only [RegistrationNativeHiddenStartup.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructed, continued⟩ := supported
  cases built : constructed.1 with
  | none => simp only [built, mem_support_pure_iff] at continued; cases continued
  | some created =>
      simp only [built, mem_support_bind_iff] at continued
      obtain ⟨generated, _generated, continued⟩ := continued
      cases sampled : generated with
      | none => simp only [sampled, mem_support_pure_iff] at continued; cases continued
      | some credential =>
          simp only [sampled, mem_support_bind_iff] at continued
          obtain ⟨installed, _installed, returned⟩ := continued
          simp only [mem_support_pure_iff, Option.some.injEq] at returned
          cases returned
          exact PqxdhRootTableInitialization.rootArray_bytes identity.ed25519
/-- The genuine initialized source derives selection on each original broad LR-good ideal-service result. -/
theorem ctx_selected (bounded : ∀ exposed,RegistrationNativeInterface.Respects budget (adversary exposed))
    (reserved : budget.create ≤ pairs.length) (chosenAt : pairs[target.2.val]?=some chosen)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (initialSecret : Secret) (result : TraceResult)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route job
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret))
    (finished : PqxdhRegistrationJointServerBirth.ClientCreated PqxdhTranscriptAd.AssociatedData × (A × RegistrationNativeLedger.State) ×
      RegistrationNativePlatformSelectiveRecordTraceStartup.Extra n KemSK RegistrationNativeKemSwitchSource.Phase Platform source)
    (present : finished ∈ result.1.1.1)
    (filter : RegistrationNativeLorEvents.Filter A)
    (good : RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target finished.2.1) :
    RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto wire serverKeyId finished.2.1.2 finished.2.2.2.events
      (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
  obtain ⟨born,shell,control,secret,observed,free,called,equal⟩ := startup_stage setup checks source seed scalar pairs chosen challenge
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode adversary budget target candidate previous privateBefore
    ensureInit identityIndex service codec route initialSecret result supported finished present
  subst result
  have same : finished=(PqxdhRegistrationJointServerBirth.encode born.created,observed.1.1.1.1.1.1,
      ((observed.1.1.1.1.1.2,observed.1.1.1.2),observed.1.1.1.1.2)) := by
    symm
    simpa only [package,Option.mem_some_iff] using present
  subst finished
  have cold := RegistrationNativeG3NativeStartupFields.start_cold setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) born free
  have pin := startup_pin setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) born free
  exact RegistrationNativePlatformLorIdealCborSelected.selected setup checks source (RegistrationNativeMldsa.owned source born.native.credential) seed scalar pairs chosen challenge
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) budget target candidate service codec route
    (bounded _) reserved chosenAt (born.native.frontend,previous) cold.2.2 cold.2.1 pin privateBefore pool phase shell control secret observed called filter good

/-- The same genuine initialized source derives its original claimed APP installation without requiring a test. -/
theorem ctx_claimed (bounded : ∀ exposed,RegistrationNativeInterface.Respects budget (adversary exposed))
    (reserved : budget.create ≤ pairs.length) (chosenAt : pairs[target.2.val]?=some chosen)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (initialSecret : Secret) (result : TraceResult)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route job
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl initialSecret))
    (finished : PqxdhRegistrationJointServerBirth.ClientCreated PqxdhTranscriptAd.AssociatedData × (A × RegistrationNativeLedger.State) ×
      RegistrationNativePlatformSelectiveRecordTraceStartup.Extra n KemSK RegistrationNativeKemSwitchSource.Phase Platform source)
    (present : finished ∈ result.1.1.1)
    (claim : A → Option (Nat × Pqxdh.Bytes))
    (good : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget target claim (finished.2.1.1,(finished.2.1.2,()))) :
    RegistrationNativeInstallTarget.Claimed claim finished.2.1.1 finished.2.1.2 finished.2.2.2.events
      (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate) := by
  obtain ⟨born,shell,control,secret,observed,free,called,equal⟩ := startup_stage setup checks source seed scalar pairs chosen challenge
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode adversary budget target candidate previous privateBefore
    ensureInit identityIndex service codec route initialSecret result supported finished present
  subst result
  have same : finished=(PqxdhRegistrationJointServerBirth.encode born.created,observed.1.1.1.1.1.1,
      ((observed.1.1.1.1.1.2,observed.1.1.1.2),observed.1.1.1.1.2)) := by
    symm
    simpa only [package,Option.mem_some_iff] using present
  subst finished
  have cold := RegistrationNativeG3NativeStartupFields.start_cold setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) born free
  have pin := startup_pin setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) born free
  exact RegistrationNativePlatformLorIdealCborSelected.claimed setup checks source (RegistrationNativeMldsa.owned source born.native.credential) seed scalar pairs chosen challenge
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) budget target candidate service codec route
    (bounded _) reserved chosenAt (born.native.frontend,previous) cold.2.2 cold.2.1 pin privateBefore pool phase shell control secret observed called claim good

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected.ctx_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected.ctx_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected.ctx_claimed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected.ctx_claimed
