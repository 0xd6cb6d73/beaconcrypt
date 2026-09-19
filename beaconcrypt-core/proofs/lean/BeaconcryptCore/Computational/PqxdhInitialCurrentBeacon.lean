import BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient
import BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder

/-!
The current Beacon compiler is interpreted in its full original ambient state: shared primitives, the private identity interpreter and the shared root-family cache. Its actual retained private KDF callback and classified initializer request are instantiated directly, before the first raw receive. The generic Slot owner retains every preparation/application effect, source sequence and binding check, and native state field.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhPhase2SourceAux
open PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhSecretInputKdf PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpandHybrid
open PqxdhInitialRootLabelService PqxdhInitialBeaconAmbient PqxdhInitialGenericProtocolBuilder
open RawCtxSelectedParentEntry RawCtxSelectedParentTable
variable {ι I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι}

/-- The actual source raw interpreter is the retained-parent native receive lift; every non-KDF primitive effect stays unchanged. -/
theorem raw_shared (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    PqxdhInitialSelectedBeacon.raw (A := A) fixed writer prior entry target =
      RawCtxSharedPrimitive.nativeImpl fixed.crypto (retainedKdf prior entry target) := by
  rw [PqxdhInitialSelectedBeacon.raw, retained_backend, RawCtxMixedShared.shared_receive]

/-- Every original probabilistic callback keeps its exact computation while retaining the full root cache. -/
theorem coins_labelled (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (response : PqxdhInitialRootLabelService.Response) (work : ProbComp Result) :
    simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (PqxdhInitialLabelCompiler.coins work) =
      (fun cache => (fun result => (result, cache)) <$> work) := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [PqxdhInitialLabelCompiler.coins, liftComp_bind, simulateQ_bind]
      change ((labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response (.inl query)) >>=
        fun answer => simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
          (PqxdhInitialLabelCompiler.coins (next answer))) = _
      simp only [ih]
      funext cache
      change (((fun answer => (answer, cache)) <$> (liftM (unifSpec.query query) : ProbComp _)) >>=
        fun result => (fun value => (value, result.2)) <$> next result.1) = _
      simp only [bind_map_left, map_bind]

section Current
variable
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (prior : Prior) (entry : Entry) (selected : Message) (second : Bool) (other target : RootOutput)

noncomputable def evaluated :
    QueryImpl (PqxdhInitialFusedCompiler.Spec I D K X Response)
      (Ambient A (BareState count) RootOracle.QueryCache) := fun query state =>
  simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected
    (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)))
    ((PqxdhInitialPrivateBeacon.compiler attachedVerify primitives count fixed (retainedKdf prior entry target)
      localImpl baseImpl kem secret challenge query).run state)

noncomputable def preparation :
    QueryImpl (PqxdhBeaconPhase2Shared.Spec (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (PqxdhGeneratedBeaconState.KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response
      PqxdhPhase2DecapsulationRouting.Shared) (Ambient A (BareState count) RootOracle.QueryCache) :=
  fun query state cache => (fun result => (result, cache)) <$>
    (PqxdhInitialRootFreeCallbacks.interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
      (.inl query)).run state

noncomputable def application (reply : Response) :
    Ambient A (BareState count) RootOracle.QueryCache (Option Pqxdh.Bytes) :=
  fun state cache => (fun result => (result, cache)) <$>
    (PqxdhInitialRootFreeCallbacks.interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
      (.inr (.inr reply))).run state

noncomputable def initialization
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    Ambient A (BareState count) RootOracle.QueryCache (Option RawCtxSelectedChain.Kernel) := fun state =>
  (fun value => (value.bind PqxdhInitialSelectedBeacon.labelKernel, state)) <$>
    PqxdhInitialSelectedService.service fixed selected second other secrets

/-- Actual preparation runs its original complete callback with all three ambient state components retained and no selected chain argument. -/
theorem preparation_source (query : (PqxdhBeaconPhase2Shared.Spec (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (PqxdhGeneratedBeaconState.KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response
      PqxdhPhase2DecapsulationRouting.Shared).Domain) :
    evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge prior entry selected second other target (.inl query) =
      preparation attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query := by
  funext state
  exact coins_labelled fixed selected _ _

/-- The actual application getter retains its original optional bytes and full ambient state, without accessing selected chain material. -/
theorem application_source (reply : Response) :
    evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge prior entry selected second other target
      (.inr (.inl (.inr reply))) =
      application attachedVerify primitives count fixed localImpl baseImpl kem secret challenge reply := by
  funext state
  exact coins_labelled fixed selected _ _

set_option backward.isDefEq.respectTransparency false in
/-- The actual retained private KDF and all original native raw primitive effects run inside the unchanged BareState and root cache. -/
theorem raw_source (writer : RawCtxMixedShared.Writer) (query : RawCtxSourceOpen.NativeSpec.Domain) :
    evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge prior entry selected second other target
      (.inr (.inl (.inl query))) =
      lift (N := BareState count) (C := RootOracle.QueryCache)
        (PqxdhInitialSelectedBeacon.raw fixed writer prior entry target query) := by
  funext state
  simp only [evaluated, PqxdhInitialPrivateBeacon.compiler, coins_labelled, PqxdhInitialPrivateBeacon.raw, StateT.run]
  rw [raw_shared]
  funext cache
  simp only [PqxdhInitialBeaconAmbient.lift, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- The actual compiled initializer callback uses the original request coordinate and the same shared root cache; selected responses are reused without exposing the selected half. -/
theorem initializer_source
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge prior entry selected second other target
      (.inr (.inr secrets)) =
      (fun state => (fun value => (Option.map (PqxdhInitialSelectedBeacon.response target) value, state)) <$>
        PqxdhInitialSelectedService.service fixed selected second other secrets) := by
  funext state
  simp only [evaluated, PqxdhInitialPrivateBeacon.compiler, PqxdhInitialFusedCompiler.compiler,
    StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    labelledFull, QueryImpl.add_apply_inr]
  rw [← PqxdhInitialSelectedService.value_response fixed selected second other target]
  simp only [PqxdhInitialSelectedService.service, Functor.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual current private initializer directly satisfies the optional Slot-kernel map inside the full shared/Bare/root-cache state. -/
theorem initialization_map
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    PqxdhInitialGenericBeaconNative.initial
      (fun q => evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
        prior entry selected second other target (.inr q)) secrets =
      Option.map (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) <$>
        initialization (A := A) (count := count) fixed selected second other secrets := by
  funext state
  simp only [PqxdhInitialGenericBeaconNative.initial, initializer_source]
  change (fun result => (Option.map (PqxdhBeaconPhase2Publication.normalInitial
      (PqxdhInitialRatchetComplementarity.beaconPending
        (PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)))) result.1, result.2)) <$>
      ((fun value => (Option.map (PqxdhInitialSelectedBeacon.response target) value, state)) <$>
        PqxdhInitialSelectedService.service fixed selected second other secrets) =
    (fun result => (Option.map (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) result.1, result.2)) <$>
      ((fun value => (value.bind PqxdhInitialSelectedBeacon.labelKernel, state)) <$>
        PqxdhInitialSelectedService.service fixed selected second other secrets)
  simp only [Functor.map_map]
  apply congrArg (fun f => f <$> PqxdhInitialSelectedService.service fixed selected second other secrets)
  funext value
  cases value with
  | none => rfl
  | some value => exact congrArg (fun kernel => (kernel, state)) (PqxdhInitialSelectedBeacon.response_map target value)

noncomputable def owner (writer : RawCtxMixedShared.Writer) (response : RatchetKdfResponse)
    (decode : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (state : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedChain.Kernel
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K)) :
    Ambient A (BareState count) RootOracle.QueryCache
      (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState RawCtxSelectedChain.Kernel
        (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K)) :=
  PqxdhInitialGenericBeacon.owner
    (preparation attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
    (liftCalls (RawCtxSelectedParentCalls.labelCalls fixed writer prior entry response))
    (application attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
    (initialization count fixed selected second other) decode bytes state

/-- The actual current compiler and shared root cache execute exactly the complete Slot Beacon owner under the concrete retained private KDF. All native phase fields and all three ambient states are retained. -/
theorem source_owner (writer : RawCtxMixedShared.Writer) (decode : RawCtxReceive.FrameDecoder)
    (bytes : Pqxdh.Bytes)
    (state : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedChain.Kernel
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K)) :
    simulateQ (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
      prior entry selected second other target)
      (PqxdhInitialFusedOwner.owner decode bytes
        (RawCtxGenericRoleStorage.nativeBeacon
          (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state)) =
      Prod.map id (RawCtxGenericRoleStorage.nativeBeacon
        (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        owner attachedVerify primitives count fixed localImpl baseImpl kem secret challenge prior entry selected second other
          writer (RawCtxSelectedParentCalls.childResponse prior entry target) decode bytes state := by
  have rawHandler : (fun q => evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
      prior entry selected second other target (.inr (.inl (.inl q)))) =
      (fun q => PqxdhInitialBeaconAmbient.lift (N := BareState count) (C := RootOracle.QueryCache)
        (PqxdhInitialSelectedBeacon.raw fixed writer prior entry target q)) := by
    funext query
    exact raw_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
      prior entry selected second other target writer query
  have receiveMap : ∀ kernel sequence context,
      (PqxdhInitialGenericBeaconNative.calls (fun q => evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
        prior entry selected second other target (.inr (.inl (.inl q))))).receive
        (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) kernel) sequence context =
      Prod.map (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) id <$>
        (liftCalls (RawCtxSelectedParentCalls.labelCalls fixed writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target))).receive kernel sequence context := by
    rw [rawHandler]
    exact PqxdhInitialBeaconAmbient.selected_receive fixed writer prior entry target
  have mapped := PqxdhInitialGenericBeaconNative.owner_mapped
    (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))
    (evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge prior entry selected second other target)
    (liftCalls (RawCtxSelectedParentCalls.labelCalls fixed writer prior entry
      (RawCtxSelectedParentCalls.childResponse prior entry target))) receiveMap
    (initialization (A := A) count fixed selected second other)
    (initialization_map attachedVerify primitives count fixed localImpl baseImpl kem secret challenge prior entry selected second other target)
    decode bytes state
  simpa only [preparation_source, application_source, owner] using mapped

end Current
end BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.raw_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.raw_shared
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.coins_labelled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.coins_labelled

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.preparation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.preparation_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.application_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.application_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.raw_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.initializer_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.initializer_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.initialization_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.initialization_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.source_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon.source_owner
