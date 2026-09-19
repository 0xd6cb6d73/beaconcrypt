import BeaconcryptCore.Computational.PqxdhInitialPendingCurrent
import BeaconcryptCore.Computational.PqxdhInitialBuilderPacking
import BeaconcryptCore.Computational.PqxdhInitialEvaluatedCurrent

/-!
The actual accepted authenticated-root execution is compiled before its first Server send and retains the entire original adaptive post client. The builder and post scheduler share one interpreter, so every private field, cache binding, callback effect and reply survives their boundary. This is a source correspondence equation, prior to the stopped-source freshness and cryptographic comparisons.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPendingAccepted
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhPhase2SourceAux
open PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhCorrelatedExtractFamily PqxdhInitialRootLabelService PqxdhSecretInputKdf
open PqxdhAuthenticatedRootExperiment PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot PqxdhInitialGenericProtocolBuilder

noncomputable def sequence {ι Chain M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (kernel : RustM (PqxdhInitialPendingPost.KernelOf Chain))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) :
    StateT (PqxdhInitialPendingPost.Front Chain M P I D K S B)
      (OracleComp (PqxdhInitialPendingPost.Spec extra Chain I D K X Response Shared S B)) Result := do
  let built ← PqxdhInitialPendingBuilder.build source kernel sender index metadata ready
  simulateQ (PqxdhInitialPendingPost.compiler sender route decode) (post built)

private theorem cache_bind_map {α β γ Cache : Type}
    (work : ProbComp α) (wrap : α → β) (next : β → StateT Cache ProbComp γ) (cache : Cache) :
    ((fun before => (fun result => (wrap result, before)) <$> work : StateT Cache ProbComp β) >>= next) cache =
      (work >>= fun result => next (wrap result) cache) := by
  change (((fun result => (wrap result, cache)) <$> work) >>= fun result => next result.1 result.2) = _
  simp only [bind_map_left]

variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
section Current
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (second : Bool) (other target : RootOutput)

noncomputable def accepted : StateT RootOracle.QueryCache ProbComp Bool :=
  let start := PqxdhInitialPostPacking.unpack
    (PqxdhInitialGenericProtocol.fromNative PqxdhInitialSelectedBuilder.knownKernel prepared.1.context.selection.2, prepared.2)
  (fun result => result.1.1) <$>
    (simulateQ (PqxdhInitialPendingCurrent.handler attachedVerify primitives 1 env.source env.localImpl env.recordWriter
      baseImpl kem secret ready.ciphertext prior entry selected second other target env.aux)
      ((sequence env.source (RawCtxInitialSentinelSampler.labelInitial second false other) env.senderId env.route env.decode
        env.index env.metadata (PqxdhInitialBuilderCut.eraseRoot ready)
        (post prepared.1.context.selection.1)).run start.1)).run start.2

/-- The original accepted source executes this single pending builder-and-post program before the first ciphertext, retaining all private and cache state without a supplied continuation law. -/
theorem source :
    PqxdhInitialEvaluatedCurrent.accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready
      prior entry second other target =
      accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready prior entry second other target := by
  let start := PqxdhInitialPostPacking.unpack
    (PqxdhInitialGenericProtocol.fromNative PqxdhInitialSelectedBuilder.knownKernel prepared.1.context.selection.2, prepared.2)
  have first := PqxdhInitialBuilderPacking.build
    (RawCtxSelectedParentCompiler.pending (Auxiliary := A) env.source env.recordWriter prior entry
      (RawCtxSelectedParentCalls.childResponse prior entry target))
    (fun query => PqxdhInitialBeaconAmbient.lift
      (RawCtxGenericFamilyRead.nativeReader (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) query))
    (PqxdhInitialCurrentBeacon.preparation attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret ready.ciphertext)
    (PqxdhInitialCurrentBeacon.application attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret ready.ciphertext)
    (PqxdhInitialCurrentBeacon.initialization 1 env.source selected second other)
    (PqxdhInitialPendingAmbient.selectorLift
      (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret ready.ciphertext))
    env.aux env.source (RawCtxInitialSentinelSampler.labelInitial second false other)
    env.senderId env.index env.metadata (PqxdhInitialBuilderCut.eraseRoot ready) start
  rw [PqxdhInitialPendingCurrent.calls] at first
  have composed := congrArg (fun work => do
    let result ← work
    Prod.fst <$> (simulateQ (PqxdhInitialEvaluatedPost.handler attachedVerify primitives 1 env.source env.localImpl
      env.recordWriter env.senderId env.route env.decode baseImpl kem secret ready.ciphertext prior entry selected second other target)
      (post prepared.1.context.selection.1 result.1)).run result.2) first
  simp_rw [bind_map_left, PqxdhInitialPendingCurrent.program attachedVerify primitives 1 env.source env.localImpl
    env.recordWriter env.senderId env.route env.decode baseImpl kem secret ready.ciphertext prior entry selected second other target env.aux] at composed
  simp only [Functor.map_map] at composed
  funext cache
  have evaluated := congrFun composed.symm cache
  simp_rw [cache_bind_map] at evaluated
  simp only [PqxdhInitialEvaluatedCurrent.accepted, accepted, sequence,
    StateT.run_bind, simulateQ_bind, map_bind]
  simpa only [start, PqxdhInitialPostPacking.pack_unpack, PqxdhInitialPostPacking.unpack,
    PqxdhInitialPostPacking.pack, PqxdhInitialPendingCurrent.handler,
    PqxdhInitialGenericProtocol.fromNative, StateT.run] using evaluated

/-- The actual authenticated accepted endpoint has the same whole pending source distribution before the first ciphertext and across all permitted post requests. -/
theorem actual :
    simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected
      (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)))
      (PqxdhInitialPrivateCurrent.accepted env (retainedKdf prior entry target) baseImpl kem attachedVerify primitives
        program post secret selected prepared ready) =
      accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready prior entry second other target := by
  rw [PqxdhInitialEvaluatedCurrent.source, source]

end Current
end BeaconcryptCore.Computational.PqxdhInitialPendingAccepted

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingAccepted.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingAccepted.source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingAccepted.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingAccepted.actual
