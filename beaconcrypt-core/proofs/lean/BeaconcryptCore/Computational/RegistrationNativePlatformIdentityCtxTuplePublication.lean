-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeConcreteTuplePublication
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationSupport
/-! A successful literal shared-CTX bundle with the actual source serializer publishes exactly its captured owner's prekey/PQ and the same started one-time public field. The source-support extraction preserves the full reached state in its premise and admits every failure prefix. Unsigned tuple readback uses decoder injectivity only; no weak-EUF, SUF, signature uniqueness, owner-key injectivity or whole-publication contract is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicationSupport (Possible)
open RegistrationNativePlatformIdentityProgram (M external)
variable {n : Nat} {I KemSK Auxiliary Platform E A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem external_pure (value : A) :
    external (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (pure value : StateT Platform ProbComp A) = pure value := by
  funext owners env platform
  simp only [external,StateT.run_pure,simulateQ_pure,map_pure]
  rfl

private theorem external_bind (work : StateT Platform ProbComp A) (next : A → StateT Platform ProbComp B) :
    external (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (work >>= next) =
      (external work >>= fun value => external (next value)) := by
  funext owners env platform
  simp only [external,StateT.run,StateT.monad_bind_def,StateT.bind,simulateQ_bind,map_bind,bind_map_left]

private theorem external_program {J : Type} {spec : OracleSpec J}
    (writer : QueryImpl spec (StateT Platform ProbComp)) (work : OracleComp spec A) :
    simulateQ (fun query => external (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (writer query)) work =
      external (simulateQ writer work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure,external_pure]
  | query_bind query next ih => simp only [simulateQ_bind,simulateQ_spec_query,ih,external_bind]

private theorem encoder (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (view : registration.SignedInitView) (bytes : alloc.vec.Vec U8)
    (possible : Possible (external (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)
      (simulateQ (RegistrationNativePlatformConcreteSource.writer reserve)
        (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
          (RegistrationNativePlatformWriter.initPacket view)).run)) (.ok (.Some bytes))) :
    core.option.Option.Some (RegistrationNativeSourceWriterReadback.initVector view) = .Some bytes := by
  obtain ⟨owners,env,previous,result,reached,returned⟩ := possible
  simp only [StateT.run,external,support_map] at reached
  obtain ⟨actual,called,same⟩ := reached
  have raw := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  have replied : actual.1 = .ok (.Some bytes) := by
    exact (congrArg (fun result => result.1.1.1) same).trans returned
  have exactBytes := RegistrationNativePlatformPublicationConcrete.source_writer reserve view previous actual raw bytes replied
  rw [exactBytes]

/-- Any literal concrete source publication that succeeds decodes to its captured unsigned tuple. This uses only successful serializer readback and free controller payload provenance. -/
theorem publication (setup : Setup base KemSK) (index : Nat)
    (owner : RegistrationNativeIdentityFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (published : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (possible : Possible (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary)
      setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
      (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin owner.mldsa.publicKey)) (.ok (.Ok published))) :
    (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
      (TranscriptAuthParts.absSlice published.encoded)).bind PqxdhDeploymentPublishedTuple.candidateTuple =
        some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic, setup.dh.publicKey scalar, owner.kemPublic⟩ := by
  rw [RegistrationNativePlatformWriter.begin_interpret] at possible
  change Possible (RegistrationNativePlatformBeaconPublication.begin _
    (fun view => simulateQ (fun query => external ((RegistrationNativePlatformConcreteSource.writer reserve) query))
      (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run) _ _ _ _ _) _ at possible
  simp_rw [external_program] at possible
  have original := RegistrationNativePlatformPublicationSupport.begin _ _
    (fun view => core.option.Option.Some (RegistrationNativeSourceWriterReadback.initVector view))
    (encoder (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) reserve)
    ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin owner.mldsa.publicKey published possible
  have fields := RegistrationNativeConcreteTuplePublication.begin_tuple _ _ _ _ _ published original
  simpa only [RegistrationNativeIdentityFrontend.inputs,PqxdhPhase2InputBytes.word_rootArray,
    RegistrationNativeBeaconPublication.pq_key] using fields

/-- The actual physical shared-hash source interpretation can only return values supported by its literal owner/Env/P source tree. -/
theorem beacon_possible (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : A × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (supported : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work)).run before)) :
    Possible work result.1 := by
  have mapped := Set.mem_image_of_mem (Prod.map id RegistrationNativePlatformIdentityCtxMain.project) supported
  rw [← support_map,RegistrationNativePlatformIdentityCtxMain.beacon_execution,support_map] at mapped
  obtain ⟨full,reached,same⟩ := mapped
  have free := OracleComp.support_simulateQ_run'_subset
    (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created)
    (((work.run before.1.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world)).run before.1.2)
    ⟨RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1.1.context,RegistrationNativeIdentityCompiler.poolView before.2.1⟩
  have freeReached : full.1 ∈ support (((work.run before.1.1.beacons).run
      (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world)).run before.1.2) := by
    apply free
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  exact ⟨before.1.1.beacons,RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world,
    before.1.2,full.1,freeReached,congrArg Prod.fst same⟩

private theorem bind_possible (work : M n KemSK Auxiliary Platform source A)
    (next : A → M n KemSK Auxiliary Platform source B) (value : B)
    (possible : Possible (work >>= next) value) :
    ∃ middle, Possible work middle ∧ Possible (next middle) value := by
  obtain ⟨first,second,previous,result,reached,same⟩ := possible
  simp only [StateT.run_bind,mem_support_bind_iff] at reached
  obtain ⟨middle,called,continued⟩ := reached
  exact ⟨middle.1.1.1,⟨first,second,previous,middle,called,rfl⟩,
    ⟨middle.1.1.2,middle.1.2,middle.2,result,continued,same⟩⟩

private theorem next_bytes (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (reply : RegistrationNativePlatformIdentityBundle.Reply)
    (bytes : alloc.vec.Vec U8)
    (possible : Possible (RegistrationNativePlatformIdentityBundle.next (n := n) (KemSK := KemSK)
      (Auxiliary := Auxiliary) (Platform := Platform) index owner scalar reply) (.ok (some bytes))) :
    ∃ published, reply = .ok (.Ok published) ∧ published.encoded = bytes := by
  obtain ⟨owners,env,previous,result,reached,same⟩ := possible
  cases reply with
  | fail error | div =>
    simp only [RegistrationNativePlatformIdentityBundle.next,StateT.run_pure,mem_support_pure_iff] at reached
    cases reached
    cases same
  | ok answer => cases answer with
    | Err error =>
      simp only [RegistrationNativePlatformIdentityBundle.next,StateT.run_pure,mem_support_pure_iff] at reached
      cases reached
      cases same
    | Ok published =>
      simp only [RegistrationNativePlatformIdentityBundle.next,StateT.run_bind,mem_support_bind_iff] at reached
      obtain ⟨phase,_changed,advanced,_advanced,returned⟩ := reached
      obtain rfl := eq_of_mem_support_pure _ returned
      exact ⟨published,rfl,Option.some.inj (RustM.ok.inj same)⟩

/-- A successful captured actual CTX body publishes the unsigned tuple of that same owner and scalar. The arbitrary final source, physical cache/journal, counters and P are retained by the actual support premise. -/
theorem bundled (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (before after : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source) (bytes : alloc.vec.Vec U8)
    (supported : (.ok (some bytes),after) ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar (RegistrationNativePlatformConcreteSource.writer reserve)))).run before)) :
    (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
      (TranscriptAuthParts.absSlice bytes)).bind PqxdhDeploymentPublishedTuple.candidateTuple =
        some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,setup.dh.publicKey scalar,owner.kemPublic⟩ := by
  have possible := beacon_possible setup checks representation created _ before ((RustM.ok (some bytes) : RustM (Option (alloc.vec.Vec U8))),after) supported
  unfold RegistrationNativePlatformIdentityBundle.bundled at possible
  obtain ⟨reply,published,continued⟩ := bind_possible _ _ _ possible
  obtain ⟨actual,rfl,encoded⟩ := next_bytes index owner scalar reply bytes continued
  rw [← encoded]
  exact publication setup index owner scalar reserve actual published

/-- The same captured body also identifies the original tagged one-time message used by its actual source start. -/
theorem bundled_started (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ = .ok started)
    (before after : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source) (bytes : alloc.vec.Vec U8)
    (supported : (.ok (some bytes),after) ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar (RegistrationNativePlatformConcreteSource.writer reserve)))).run before)) :
    (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
      (TranscriptAuthParts.absSlice bytes)).bind PqxdhDeploymentPublishedTuple.candidateTuple =
        some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,setup.dh.publicKey scalar,owner.kemPublic⟩ ∧
      PqxdhRefinement.absBytes started.message.one_time_key = PqxdhEd25519EufCma.oneTimeMessage (setup.dh.publicKey scalar) := by
  refine ⟨bundled setup checks representation created index owner scalar reserve before after bytes supported,?_⟩
  simpa only [PqxdhPhase2InputBytes.word_rootArray] using
    RegistrationNativeOneTimePublication.started_key _ _ _ started built

/-- Every successful actual outer source bundle reaches one captured owner/scalar and publishes precisely their unsigned key tuple. -/
theorem bundle_vec (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (before after : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source) (bytes : alloc.vec.Vec U8)
    (supported : (.ok (some bytes),after) ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityBundleRun.bundle setup index (RegistrationNativePlatformConcreteSource.writer reserve)))).run before)) :
    ∃ owner scalar middle, before.1.1.beacons[index]? = some owner ∧
      RegistrationNativePlatformIdentityCtxBundleDispatch.Picked setup checks representation created owner scalar before middle ∧
      (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
        (TranscriptAuthParts.absSlice bytes)).bind PqxdhDeploymentPublishedTuple.candidateTuple =
          some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,setup.dh.publicKey scalar,owner.kemPublic⟩ := by
  rcases RegistrationNativePlatformIdentityCtxBundleDispatch.cut setup checks representation created index
    (RegistrationNativePlatformConcreteSource.writer reserve) before (.ok (some bytes),after) supported with rejected | captured
  · cases rejected
  · obtain ⟨owner,scalar,middle,found,picked,called⟩ := captured
    exact ⟨owner,scalar,middle,found,picked,bundled setup checks representation created index owner scalar reserve middle after bytes called⟩

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem interpret_map (joint : PqxdhJointIdentity.Primitives) (change : A → B)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source A) :
    RegistrationNativePlatformIdentityCtxMain.interpret joint (change <$> work) =
      change <$> RegistrationNativePlatformIdentityCtxMain.interpret joint work := by
  funext before
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret,StateT.run,map_apply,simulateQ_map,Functor.map_map]
  rfl

/-- The public lifecycle's successful byte reply has this same captured source tuple, with all sampled/stored-coin and failed-prefix paths retained. -/
theorem bundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (before after : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some bytes),after) ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created
        (RegistrationNativePlatformConcreteSource.writer reserve) index)).run before)) :
    ∃ owner scalar middle, before.1.1.beacons[index]? = some owner ∧
      RegistrationNativePlatformIdentityCtxBundleDispatch.Picked setup checks representation created owner scalar before middle ∧
      (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
        bytes).bind PqxdhDeploymentPublishedTuple.candidateTuple =
          some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,setup.dh.publicKey scalar,owner.kemPublic⟩ := by
  rw [RegistrationNativePlatformIdentityCtxLifecycle.bundle,interpret_map,StateT.run_map,support_map] at supported
  obtain ⟨⟨raw,finished⟩,called,same⟩ := supported
  have afterEq : finished=after := congrArg Prod.snd same
  subst finished
  have replied := congrArg Prod.fst same
  cases raw with
  | fail error | div => cases replied
  | ok optional => cases optional with
    | none => cases replied
    | some encoded =>
      have bytesEq : TranscriptAuthParts.absSlice encoded=bytes := Option.some.inj (RustM.ok.inj replied)
      rw [← bytesEq]
      exact bundle_vec setup checks representation created index reserve before after encoded called

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.beacon_possible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.beacon_possible

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.bundled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.bundled_started' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.bundled_started

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.bundle_vec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.bundle_vec

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication.bundle
