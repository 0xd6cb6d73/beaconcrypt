-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborResponseWriterMap
import BeaconcryptCore.Computational.CborTaggedCodec
import BeaconcryptCore.Computational.CborProductionBoundary
/-! Public response tagging preserves the supplied-root builder, optional failures and every native poststate in the normalized shared-writer model. Frame read-back is required only after a successful inner frame write; no global writer-success or legacy size law is assumed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborTaggedBuild
open PqxdhServerAuthExperiment (Setup Codec Checks tailImpl nativeTail)
open PqxdhServerRegistrationPublication
variable {ι KemSK Reader Response Reader' Response' : Type} {baseSpec : OracleSpec ι}

theorem primitive_same (setup : Setup baseSpec KemSK)
    (left : Codec Reader Response) (right : Codec Reader' Response') (checks : Checks)
    (same : left.frameWrite = right.frameWrite)
    (query : RawCtxSourceSend.PrimitiveSpec.Domain) :
    tailImpl setup left checks (.inl query) = tailImpl setup right checks (.inl query) := by
  cases query with
  | inl request => rfl
  | inr input =>
    simp only [tailImpl]
    congr 1
    simp only [nativeTail, QueryImpl.apply_compose, nativeAdapter]
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    congr 1
    funext request
    simp only [QueryImpl.compose, simulateQ_spec_query,
      PqxdhRegistrationProtocolState.registrationImpl, same]

theorem send_same {α : Type} (setup : Setup baseSpec KemSK)
    (left : Codec Reader Response) (right : Codec Reader' Response') (checks : Checks)
    (same : left.frameWrite = right.frameWrite)
    (work : OracleComp RawCtxSourceSend.PrimitiveSpec α) :
    simulateQ (tailImpl setup left checks) (simulateQ sendLift work) =
      simulateQ (tailImpl setup right checks) (simulateQ sendLift work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.compose, sendLift, simulateQ_spec_query]
  exact primitive_same setup left right checks same query

theorem after_tagged (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (checks : Checks) (sender : Std.U64)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack wire)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (pinned : candidate.server_identity_key_id = sender)
    (root : PqxdhSecretInputKdf.RootOutput) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (initialized : PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok kernel)
    (authenticated : Pqxdh.Bytes)
    (state : State Unit Unit (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (simulateQ (tailImpl setup (CborTaggedCodec.codec wire) checks)
      (afterInitialization candidate authenticated kernel () state)).run primitive =
      (fun result => (CborResponseWriterMap.outcome (CborTaggedCodec.tag sender) result.1, result.2)) <$>
        (simulateQ (tailImpl setup (CborRegistrationCodec.normalize wire sender) checks)
          (afterInitialization candidate authenticated kernel () state)).run primitive := by
  refine Eq.trans ?_ (CborResponseWriterMap.after_map (CborTaggedCodec.tag sender)
    (tailImpl setup (CborRegistrationCodec.normalize wire sender) checks)
    candidate authenticated kernel () state primitive)
  simp only [afterInitialization, simulateQ_bind, StateT.run_bind,
    CborResponseWriterMap.send_unchanged]
  rw [send_same setup (CborTaggedCodec.codec wire) (CborRegistrationCodec.normalize wire sender) checks rfl]
  apply bind_congr_of_forall_mem_support
  intro sent supported
  simp only [simulateQ_spec_query, CborResponseWriterMap.writer,
    PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
    StateT.run_pure, pure_bind]
  cases present : sent.1.2 with
  | none => rfl
  | some encrypted =>
    obtain ⟨digest, _, _, written, _⟩ := PqxdhServerAuthNegativeControl.tail_send
      setup (CborRegistrationCodec.normalize wire sender) checks root kernel initialized
      (firstContext candidate authenticated) primitive.1 primitive.2 sent supported encrypted present
    have parsed := (readBack _ encrypted.ciphertext written).2
    have same := CborTaggedCodec.write_tagged wire sender (responseFields candidate encrypted) _ parsed rfl pinned
    simp only [simulateQ_bind, simulateQ_spec_query, CborResponseWriterMap.writer,
      PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
      StateT.run_bind, StateT.run_map, StateT.run_pure, pure_bind, same]
    rw [PqxdhServerAuthNegativeControl.tailImpl_aux]
    simp only [PqxdhServerAuthExperiment.tailAux, StateT.run_pure, map_pure, pure_bind]
    cases (CborRegistrationCodec.normalize wire sender).write2 (responseFields candidate encrypted) <;> rfl
theorem candidate_tagged (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (checks : Checks) (sender : Std.U64)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack wire)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (pinned : candidate.server_identity_key_id = sender)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes)
    (state : State Unit Unit (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (simulateQ (tailImpl setup (CborTaggedCodec.codec wire) checks)
      (candidateTail setup.source candidate root data () state)).run primitive =
      (fun result => (CborResponseWriterMap.outcome (CborTaggedCodec.tag sender) <$> result.1, result.2)) <$>
        (simulateQ (tailImpl setup (CborRegistrationCodec.normalize wire sender) checks)
          (candidateTail setup.source candidate root data () state)).run primitive := by
  simp only [candidateTail, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
    StateT.run_pure, pure_bind]
  cases checks.beaconIdentity candidate.beacon_identity_public_key <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
      StateT.run_pure, pure_bind, simulateQ_pure, map_pure]
  · rfl
  cases checks.reservePeer <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
      simulateQ_pure, StateT.run_pure, map_pure]
  · rfl
  cases initialized : BeaconcryptCore.Refinement.ServerTransactionRefinement.initializeCandidate candidate
      (PqxdhRootTableInitialization.rootArray root)
      (PqxdhRootTableInitialization.initialResponse setup.source.crypto) <;>
    simp only [continueRust, simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
  case ok kernel =>
    have initial : PqxdhRootTableInitialization.initialKernelRun setup.source false root = ok kernel :=
      (candidate_initialization setup.source candidate root).symm.trans initialized
    split <;> (try simp only [simulateQ_pure, StateT.run_pure, map_pure]) <;> try rfl
    split <;> (try simp only [simulateQ_pure, StateT.run_pure, map_pure]) <;> try rfl
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
      StateT.run_pure, pure_bind]
    cases checks.reservePlaintext (8 + (data.getD registrationWitness).length) <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
        simulateQ_pure, StateT.run_pure, map_pure]
    · rfl
    cases candidate.key_id_binding <;>
      simp only [simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
    simp only [simulateQ_map, StateT.run_map,
      after_tagged setup wire checks sender readBack candidate pinned root kernel initial,
      Functor.map_map]
    rfl

theorem build_tagged (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (checks : Checks) (readBack : PqxdhServerAuthNegativeControl.FrameReadBack wire)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes)
    (state : State Unit Unit (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (simulateQ (tailImpl setup (CborTaggedCodec.codec wire) checks)
      (build setup.source pending root data () state)).run primitive =
      (fun result => (CborResponseWriterMap.outcome (CborTaggedCodec.tag state.identityKeyId) <$> result.1, result.2)) <$>
        (simulateQ (tailImpl setup (CborRegistrationCodec.normalize wire state.identityKeyId) checks)
          (build setup.source pending root data () state)).run primitive := by
  unfold build
  cases next : pqxdh.server_next_key_id state.control <;>
    simp only [continueRust, simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
  case ok result =>
    cases result <;> simp only [simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
    case Ok key =>
      cases prepared : pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩
          (if (state.server.peers key).isSome then .Occupied else .Available) <;>
        simp only [simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
      case ok result =>
        cases result <;> simp only [simulateQ_pure, StateT.run_pure, map_pure] <;> try rfl
        case Ok candidate =>
          obtain ⟨_, _, pinned, _, _, _⟩ := PqxdhServerAuthNegativeControl.prepare_commit_fields
            state.control pending ⟨state.server.identity, state.identityKeyId⟩ _ candidate prepared
          exact candidate_tagged setup wire checks state.identityKeyId readBack candidate pinned root data state primitive

theorem native_build (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (checks : Checks) (readBack : PqxdhServerAuthNegativeControl.FrameReadBack wire)
    (session : Nat) (data : Option Pqxdh.Bytes) (state : PqxdhServerAuthNative.NativeState KemSK) :
    PqxdhServerAuthNative.nativeBuild setup (CborTaggedCodec.codec wire) checks session data state =
      (fun result => ((CborResponseWriterMap.response (CborTaggedCodec.tag state.2.server.identityKeyId)) <$> result.1, result.2)) <$>
        PqxdhServerAuthNative.nativeBuild setup (CborRegistrationCodec.normalize wire state.2.server.identityKeyId)
          checks session data state := by
  simp only [PqxdhServerAuthNative.nativeBuild, PqxdhServerAuthNative.nativeGet_bind]
  cases found : state.2.pending session
  case none =>
    simp only [PqxdhServerAuthNative.native_pure_run, map_pure]
    rfl
  case some token =>
    simp only [PqxdhServerAuthNative.native_bind_run, PqxdhServerAuthNative.nativeCoins,
      PqxdhServerAuthNative.nativeSet, bind_pure_comp,
      PqxdhServerAuthNative.native_map_run, PqxdhServerAuthNative.localState,
      map_pure, Functor.map_map, build_tagged setup wire checks readBack]
    congr 1
    funext result
    cases result.1 <;> rfl

theorem deployment_build (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (checks : Checks) (readBack : PqxdhServerAuthNegativeControl.FrameReadBack wire)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (session : Nat) (data : Option Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentNative.handler setup (CborTaggedCodec.codec wire) checks route seed
      (.inr (.build session data))).run state =
      (fun result => ((CborResponseWriterMap.response
        (CborTaggedCodec.tag state.native.shared.2.server.identityKeyId)) <$> result.1, result.2)) <$>
        (PqxdhDeploymentNative.handler setup
          (CborRegistrationCodec.normalize wire state.native.shared.2.server.identityKeyId)
          checks route seed (.inr (.build session data))).run state := by
  change (fun result => (result.1, { state with native := result.2 })) <$>
    (PqxdhRegistrationSchedule.onShared
      (PqxdhServerAuthNative.nativeBuild setup (CborTaggedCodec.codec wire) checks session data)).run state.native =
    (fun result => ((CborResponseWriterMap.response
      (CborTaggedCodec.tag state.native.shared.2.server.identityKeyId)) <$> result.1, result.2)) <$>
      ((fun result => (result.1, { state with native := result.2 })) <$>
        (PqxdhRegistrationSchedule.onShared
          (PqxdhServerAuthNative.nativeBuild setup
            (CborRegistrationCodec.normalize wire state.native.shared.2.server.identityKeyId)
            checks session data)).run state.native)
  simp only [PqxdhRegistrationSchedule.onShared_run, native_build setup wire checks readBack,
    Functor.map_map]

theorem reader_codec (wire : Codec Reader Response)
    {Message Root : Type} (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (same : RawCtxFrameDecoding.decode reader.model = wire.frameRead) (sender : Std.U64) :
    PqxdhBoundaryRecordPrelude.withReader (CborRegistrationCodec.normalize wire sender) reader =
      CborRegistrationCodec.normalize (PqxdhBoundaryRecordPrelude.withReader wire reader) sender := by
  simp only [PqxdhBoundaryRecordPrelude.withReader, CborRegistrationCodec.normalize,
    CborRegistrationCodec.unwrap, same]

theorem base_at (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : PqxdhDeploymentInterface.Spec.Domain) (state : PqxdhDeploymentNative.State KemSK) :
    (CborProductionBoundary.normalizedBaseHandler setup wire parse checks seed query).run state =
      (PqxdhDeploymentNative.handler setup
        (PqxdhBoundaryRecordPrelude.withReader (CborProductionBoundary.codec wire parse
          (CborProductionBoundary.normalizationSender query state)) (CborProductionBoundary.nativeReader parse))
        checks (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed query).run state :=
  CborCommandFilter.atState_run _ state

theorem base_build (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack
      (PqxdhBoundaryRecordPrelude.withReader (CborProductionBoundary.wireCodec wire parse)
        (CborProductionBoundary.nativeReader parse)))
    (session : Nat) (data : Option Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentNative.handler setup
        (CborTaggedCodec.codec (PqxdhBoundaryRecordPrelude.withReader
          (CborProductionBoundary.wireCodec wire parse) (CborProductionBoundary.nativeReader parse)))
        checks (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed
      (.inr (.build session data))).run state =
      (fun result => ((CborResponseWriterMap.response
        (CborTaggedCodec.tag state.native.shared.2.server.identityKeyId)) <$> result.1, result.2)) <$>
        (CborProductionBoundary.normalizedBaseHandler setup wire parse checks seed (.inr (.build session data))).run state := by
  let annotate := fun result : Option PqxdhServerRegistrationPublication.Response × PqxdhDeploymentNative.State KemSK =>
    ((CborResponseWriterMap.response (CborTaggedCodec.tag state.native.shared.2.server.identityKeyId)) <$> result.1, result.2)
  have same := congrArg (fun selected : Codec Reader Response =>
      annotate <$> (PqxdhDeploymentNative.handler setup selected checks
        (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed
        (.inr (.build session data))).run state)
    (reader_codec (CborProductionBoundary.wireCodec wire parse)
      (CborProductionBoundary.nativeReader parse) (funext (CborProductionBoundary.decode_native parse))
      state.native.shared.2.server.identityKeyId).symm
  have original := congrArg (fun work => annotate <$> work)
    (base_at setup wire parse checks seed (.inr (.build session data)) state).symm
  exact (deployment_build setup
    (PqxdhBoundaryRecordPrelude.withReader (CborProductionBoundary.wireCodec wire parse)
      (CborProductionBoundary.nativeReader parse)) checks readBack
    (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed session data state).trans
      (same.trans original)

theorem filter_map {κ S : Type} {spec : OracleSpec κ}
    (allow : spec.Domain → S → Bool)
    (reject : (query : spec.Domain) → S → spec.Range query × S)
    (left right : QueryImpl spec (StateT S ProbComp)) (query : spec.Domain) (state : S)
    (encode : spec.Range query → spec.Range query)
    (exactStep : (left query).run state =
      (fun result => (encode result.1, result.2)) <$> (right query).run state)
    (rejected : encode (reject query state).1 = (reject query state).1) :
    (CborCommandFilter.handler allow reject left query).run state =
      (fun result => (encode result.1, result.2)) <$>
        (CborCommandFilter.handler allow reject right query).run state := by
  cases admitted : allow query state <;>
    simp only [CborCommandFilter.handler, StateT.run, admitted, Bool.false_eq_true,
      ite_false, ite_true, map_pure]
  · rw [rejected]
  · exact exactStep

theorem production_build (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack
      (PqxdhBoundaryRecordPrelude.withReader (CborProductionBoundary.wireCodec wire parse)
        (CborProductionBoundary.nativeReader parse)))
    (session : Nat) (data : Option Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    (CborCommandFilter.handler CborProductionBoundary.allowed CborProductionBoundary.reject
      (PqxdhDeploymentNative.handler setup
        (CborTaggedCodec.codec (PqxdhBoundaryRecordPrelude.withReader
          (CborProductionBoundary.wireCodec wire parse) (CborProductionBoundary.nativeReader parse)))
        checks (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed)
      (.inr (.build session data))).run state =
      (fun result => ((CborResponseWriterMap.response
        (CborTaggedCodec.tag state.native.shared.2.server.identityKeyId)) <$> result.1, result.2)) <$>
        (CborProductionBoundary.normalizedHandler setup wire parse checks seed (.inr (.build session data))).run state :=
  filter_map CborProductionBoundary.allowed CborProductionBoundary.reject _ _ _ state _
    (base_build setup wire parse checks seed readBack session data state) rfl

end BeaconcryptCore.Computational.CborTaggedBuild

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.primitive_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.primitive_same

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.send_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.send_same

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.after_tagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.after_tagged

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.candidate_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.candidate_tagged

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.build_tagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.build_tagged

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.native_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.native_build

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.deployment_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.deployment_build

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.reader_codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.reader_codec

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.base_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.base_at

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.base_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.base_build

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.filter_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.filter_map

/-- info: 'BeaconcryptCore.Computational.CborTaggedBuild.production_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedBuild.production_build
