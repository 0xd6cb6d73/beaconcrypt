import BeaconcryptCore.Computational.PqxdhNativeSharedPrefix
import BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput
import BeaconcryptCore.Computational.PqxdhSourceAuxiliary
import BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks

/-!
The actual pending selector and source auxiliary callbacks have the local capability needed by the native shared-ROM prefix. Their full identity/root/auxiliary state and optional replies survive; they never receive the CTX cache. The actual retained initializer is already supplied by NativeSharedPrefix.initial_source. Preparation/application are separate concrete consumers.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient
variable {ι A N C : Type} {extra : OracleSpec ι}

noncomputable def selectorLocal (selector : QueryImpl extra (StateT N (StateT C ProbComp))) :
    QueryImpl extra (StateT (ExternalState A N C) ProbComp) := fun query state =>
  (fun result => (result.1.1, ((state.1.1, result.1.2), result.2))) <$>
    ((selector query).run state.1.2).run state.2

/-- The pending selector's exact source identity/root state effect is independent of the shared CTX cache by its actual typed interface. -/
theorem selector_source (selector : QueryImpl extra (StateT N (StateT C ProbComp))) (query : extra.Domain) :
    localLift (selectorLocal (A := A) selector query) = PqxdhInitialPendingAmbient.selectorLift selector query := by
  funext state cache
  simp only [localLift, selectorLocal, PqxdhInitialPendingAmbient.selectorLift, Functor.map_map]
  rfl

noncomputable def auxiliaryLocal (callbacks : PqxdhSourceAuxiliary.Callbacks A) :
    QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp) := fun query state =>
  (fun result => (result.1, ((result.2, state.1.2), state.2))) <$>
    (PqxdhSourceAuxiliary.localServer callbacks query).run state.1.1

/-- The actual validation/allocation/erase/writer dispatch used by publication is the source-local prefix callback, with complete optional outcomes and the same shared cache. -/
theorem auxiliary_source (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (query : PqxdhServerRegistrationPublication.AuxSpec.Domain) :
    localLift (auxiliaryLocal (N := N) (C := C) callbacks query) =
      PqxdhInitialBeaconAmbient.lift (PqxdhSourceAuxiliary.server callbacks query) := by
  funext state cache
  simp only [localLift, auxiliaryLocal, PqxdhInitialBeaconAmbient.lift,
    PqxdhSourceAuxiliary.server, PqxdhSourceAuxiliary.lift, Functor.map_map]

/-- Source-local callback randomness is forwarded one for one; the local adapter adds no hash query or hidden sampling. -/
theorem local_bills {Value : Type} (work : LocalCallback A N C Value)
    (state : Local A N C) (q : Nat)
    (bounded : (work.run (externalState state)).IsTotalQueryBound q) :
    ((localCall work).run state).IsQueryBoundP (AdaptiveCtxSharedHash.HashClass true) 0 ∧
    ((localCall work).run state).IsQueryBoundP (AdaptiveCtxSharedHash.HashClass false) q := by
  change ((fun result => (result.1, afterExternal state result.2)) <$>
    simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState state))).IsQueryBoundP _ 0 ∧
    ((fun result => (result.1, afterExternal state result.2)) <$>
    simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState state))).IsQueryBoundP _ q
  simpa only [isQueryBoundP_map_iff] using
    And.intro (RawCtxSelectiveSharedRom.coins_no_hash (work.run (externalState state)))
      (RawCtxSelectiveSharedRom.coins_bound (work.run (externalState state)) q bounded)

noncomputable def rootLocal {Value : Type} (work : StateT (A × N) ProbComp Value) :
    LocalCallback A N C Value := fun state =>
  (fun result => (result.1, (result.2, state.2))) <$> work.run state.1

section Actual
open PqxdhPhase2SourceAux
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhKemIndCca PqxdhJointKdfGame PqxdhPrivateKemSource PqxdhInitializerSecrecy
open PqxdhCorrelatedExpandHybrid PqxdhInitialRootFreeCallbacks
variable {I D K X Response KemSK : Type} {baseSpec : OracleSpec ι}
variable (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)

noncomputable def preparation : QueryImpl (PqxdhBeaconPhase2Shared.Spec (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (PqxdhGeneratedBeaconState.KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response
      PqxdhPhase2DecapsulationRouting.Shared) (StateT (ExternalState A (BareState count) PqxdhCorrelatedExpand.RootOracle.QueryCache) ProbComp) := fun query => rootLocal (C := PqxdhCorrelatedExpand.RootOracle.QueryCache)
  (PqxdhInitialCtxFreeCallbacks.cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inl query))

noncomputable def application (response : Response) : LocalCallback A (BareState count) PqxdhCorrelatedExpand.RootOracle.QueryCache (Option Pqxdh.Bytes) := rootLocal (C := PqxdhCorrelatedExpand.RootOracle.QueryCache)
  (PqxdhInitialCtxFreeCallbacks.cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr (.inr response)))

/-- The concrete compiler's preparation callback is the original reached source callback, retaining both caches and all private effects. -/
theorem preparation_source (query : (PqxdhBeaconPhase2Shared.Spec (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (PqxdhGeneratedBeaconState.KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response
      PqxdhPhase2DecapsulationRouting.Shared).Domain) :
    localLift (preparation attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query) =
      PqxdhInitialCurrentBeacon.preparation attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query := by
  funext state roots
  have linked := PqxdhInitialCtxFreeCallbacks.preparation_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query state roots
  simp only [localLift, preparation, rootLocal, StateT.run, Functor.map_map] at linked ⊢
  exact linked.symm

/-- The original application callback retains its optional payload and every local/private state effect under the same source-local compiler. -/
theorem application_source (response : Response) :
    localLift (application attachedVerify primitives count fixed localImpl baseImpl kem secret challenge response) =
      PqxdhInitialCurrentBeacon.application attachedVerify primitives count fixed localImpl baseImpl kem secret challenge response := by
  funext state roots
  have linked := PqxdhInitialCtxFreeCallbacks.application_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge response state roots
  simp only [localLift, application, rootLocal, StateT.run, Functor.map_map] at linked ⊢
  exact linked.symm

end Actual
end BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks


/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks.selector_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks.selector_source

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks.auxiliary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks.auxiliary_source

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks.local_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks.local_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks.preparation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks.preparation_source

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks.application_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks.application_source
