import BeaconcryptCore.Computational.PqxdhInitialPendingAmbient
import BeaconcryptCore.Computational.PqxdhInitialEvaluatedPost
import BeaconcryptCore.Computational.RawCtxSelectedParentCompiler

/-!
The actual current retained-parent interpreter instantiates the full pending post frontend. Its primitive and public callbacks are derived from the concrete source interpreters, and its preparation, initializer, application and selector callbacks retain the same complete private state and shared initializer cache. This operational equation retains native reveal interpretation; the hidden-input reduction must still use the checked stopped and freshness construction.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPendingCurrent
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhPhase2SourceAux PqxdhPhase1AcceptanceOracle
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource PqxdhCorrelatedExtractFamily
open PqxdhInitialRootLabelService PqxdhInitialGenericProtocolBuilder PqxdhCorrelatedExpand
open PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- The pending receive/send interface has precisely the concrete retained-parent calls after its instrumentation is erased. -/
theorem calls (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (response : RatchetKdfResponse) :
    RawCtxGenericOwnerInterpretation.interpretedCalls
      (RawCtxSelectedParentCompiler.pending (Auxiliary := A) fixed writer prior entry response)
      RawCtxPendingOwnerQueries.calls = RawCtxSelectedParentCalls.labelCalls fixed writer prior entry response := by
  rw [← RawCtxSelectedParentCompiler.calls_interpreted]
  unfold RawCtxGenericOwnerInterpretation.interpretedCalls
  congr 1
  · funext kernel sequence context
    simp only [RawCtxSelectedParentCompiler.pending, QueryImpl.simulateQ_compose,
      RawCtxPendingOwnerQueries.receive_call]
  · funext kernel context
    simp only [RawCtxSelectedParentCompiler.pending, QueryImpl.simulateQ_compose,
      RawCtxPendingOwnerQueries.send_call]


/-- The same pending calls retain all shared/private/cache effects inside the current Beacon interpreter. -/
theorem lifted_calls {N C : Type} (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (response : RatchetKdfResponse) :
    RawCtxGenericOwnerInterpretation.interpretedCalls
      (fun query => lift (A := A) (N := N) (C := C)
        (RawCtxSelectedParentCompiler.pending fixed writer prior entry response query)) RawCtxPendingOwnerQueries.calls =
      liftCalls (RawCtxSelectedParentCalls.labelCalls fixed writer prior entry response) := by
  rw [← calls]
  simp only [RawCtxGenericOwnerInterpretation.interpretedCalls, liftCalls, simulate_lift]

/-- Every public request still uses the real fixed HKDF and the original shared primitive backend; private retained-table substitution cannot alter it. -/
theorem public_calls (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : PqxdhSecretInputKdf.RootOutput) :
    (fun request => simulateQ (RawCtxSelectedParentCompiler.pending (Auxiliary := A) fixed writer prior entry
      (RawCtxSelectedParentCalls.childResponse prior entry target)) (RawCtxPendingOwnerQueries.publicForward request)) =
      PqxdhInitialSelectedRecords.backend fixed writer prior entry target ∘ₛ RawCtxServerServices.publicLift := by
  funext query state
  rcases query with coin | bytes | query
  all_goals simp [RawCtxSelectedParentCompiler.pending, RawCtxPendingOwnerQueries.publicForward,
    RawCtxPendingOwnerQueries.erase, RawCtxSelectedParentCompiler.original,
    RawCtxSelectedParentOwner.publicImpl, RawCtxProtocolBackend.backend,
    PqxdhInitialSelectedRecords.backend, RawCtxServerServices.publicLift,
    RawCtxServerServices.backendImpl, QueryImpl.compose, OracleSpec.query,
    RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, RawCtxSharedPrimitive.nativeImpl, StateT.run]


noncomputable def selector
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (SelectorSpec baseSpec) (StateT (BareState count) (StateT RootOracle.QueryCache ProbComp)) :=
  fun query state cache => (fun result => (result, cache)) <$>
    simulateQ (PqxdhInitialRootFreeCallbacks.publicOnly baseImpl kem secret challenge)
      (PqxdhPhase2PostScheduler.publicWork ((borrowedSelector attachedVerify primitives count query).run state))

/-- The original complete selector is independent of the selected-chain bytes and leaves the initializer cache untouched. -/
theorem selector_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (selected : Message)
    (response : PqxdhInitialRootLabelService.Response) :
    (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response).mapStateTBase
      (PqxdhInitialCurrentPost.selector attachedVerify primitives count baseImpl kem secret challenge) =
      selector attachedVerify primitives count baseImpl kem secret challenge := by
  funext query state cache
  exact PqxdhInitialEvaluatedRecords.coins fixed selected response _ cache

/-- All actual records are the same pending primitive/read frontend lifted with the complete root cache. -/
theorem records
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : PqxdhSecretInputKdf.RootOutput) :
    PqxdhInitialEvaluatedPost.records (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)
      fixed writer sender route decode prior entry target =
      PqxdhInitialPostPacking.record (PqxdhInitialPendingAmbient.cacheLive
        (RawCtxGenericFamilyLive.impl
          (RawCtxGenericOwnerInterpretation.interpretedCalls
            (RawCtxSelectedParentCompiler.pending fixed writer prior entry
              (RawCtxSelectedParentCalls.childResponse prior entry target)) RawCtxPendingOwnerQueries.calls)
          (fun request => simulateQ (RawCtxSelectedParentCompiler.pending fixed writer prior entry
            (RawCtxSelectedParentCalls.childResponse prior entry target)) (RawCtxPendingOwnerQueries.publicForward request))
          (RawCtxGenericFamilyRead.nativeReader (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))
          sender route decode)) := by
  rw [calls, public_calls]
  funext query before cache
  simp only [PqxdhInitialEvaluatedPost.records, PqxdhInitialEvaluatedRecords.lift,
    PqxdhInitialGenericRecords.records, PqxdhInitialPostPacking.record,
    StateT.run, bind_pure_comp]
  let execution := ((RawCtxGenericFamilyLive.impl
    (RawCtxSelectedParentCalls.labelCalls fixed writer prior entry (RawCtxSelectedParentCalls.childResponse prior entry target))
    (PqxdhInitialSelectedRecords.backend fixed writer prior entry target ∘ₛ RawCtxServerServices.publicLift)
    (RawCtxGenericFamilyRead.nativeReader (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))
    sender route decode query).run before.roles).run before.primitive
  change (fun result => (result, cache)) <$> ((fun a => (a.1.1,
    { before with roles := a.1.2, primitive := a.2 })) <$> execution) =
    (fun result => ((result.1.1.1, { before with roles := result.1.1.2, primitive := result.1.2 }), result.2)) <$>
      ((fun result => (result, cache)) <$> execution)
  simp only [Functor.map_map]


section Current
variable
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (selected : Message) (second : Bool) (other target : PqxdhSecretInputKdf.RootOutput)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Base A))

noncomputable def handler :
    QueryImpl (PqxdhInitialPendingPost.Spec (SelectorSpec baseSpec) RawCtxSelectedChain.Slot
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K)
      (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared S B)
      (Ambient A (BareState count) RootOracle.QueryCache) :=
  PqxdhInitialPendingPost.handler
    (fun query => lift (RawCtxSelectedParentCompiler.pending fixed writer prior entry
      (RawCtxSelectedParentCalls.childResponse prior entry target) query))
    (fun query => lift (RawCtxGenericFamilyRead.nativeReader
      (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) query))
    (PqxdhInitialCurrentBeacon.preparation attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
    (PqxdhInitialCurrentBeacon.application attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
    (PqxdhInitialCurrentBeacon.initialization count fixed selected second other)
    (PqxdhInitialPendingAmbient.selectorLift (selector attachedVerify primitives count baseImpl kem secret challenge))
    (fun query => lift (aux query))

/-- The concrete current post execution equals the full typed pending source program in its single shared/private/cache interpreter, without any continuation equation as a premise. -/
theorem program
    (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (before : PqxdhInitialPostPacking.Full RawCtxSelectedChain.Slot M P
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K) A (BareState count) S B) :
    (simulateQ (PqxdhInitialEvaluatedPost.handler attachedVerify primitives count fixed localImpl writer sender route decode
      baseImpl kem secret challenge prior entry selected second other target) client).run (PqxdhInitialPostPacking.pack before) =
      (fun result => (result.1.1, PqxdhInitialPostPacking.pack (result.1.2, result.2))) <$>
        (simulateQ (handler attachedVerify primitives count fixed localImpl writer baseImpl kem secret challenge
          prior entry selected second other target aux)
          ((simulateQ (PqxdhInitialPendingPost.compiler sender route decode) client).run before.1)).run before.2 := by
  have exactSource := PqxdhInitialPendingAmbient.schedule
    (RawCtxSelectedParentCompiler.pending (Auxiliary := A) fixed writer prior entry (RawCtxSelectedParentCalls.childResponse prior entry target))
    (RawCtxGenericFamilyRead.nativeReader (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))
    (PqxdhInitialCurrentBeacon.preparation attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
    (PqxdhInitialCurrentBeacon.application attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
    (PqxdhInitialCurrentBeacon.initialization count fixed selected second other)
    (selector attachedVerify primitives count baseImpl kem secret challenge)
    (fun query => lift (aux query)) sender route decode client before
  simp only [handler, PqxdhInitialEvaluatedPost.handler, records, selector_source]
  delta PqxdhInitialCurrentBeacon.owner
  simpa only [lifted_calls] using exactSource

end Current

end BeaconcryptCore.Computational.PqxdhInitialPendingCurrent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.calls

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.lifted_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.lifted_calls

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.public_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.public_calls

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.selector_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.selector_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.records

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingCurrent.program
