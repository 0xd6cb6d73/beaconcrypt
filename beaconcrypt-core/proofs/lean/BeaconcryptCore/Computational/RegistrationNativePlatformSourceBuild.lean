-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk
import BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute

/-! This additive native Server build uses both actual source writer request bodies, an external stateful reservation, and pure exact Server pin selection. Platform callbacks receive their public source requests and cannot inspect or change private native coordinates. Native crypto, history, record-call markers and installation remain in the original Local/Server state; all effects are interpreted through the same outer monad. Public container and decoder correspondence remain separate source obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerFrontendCompiler (State)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformSourceCompletion (writeWith encodeWith)
variable {n : Nat} {E Value ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m]

def write (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (request : record_effects.RecordWriteRequest) :
    StateT (Local n) m (RustM (core.option.Option (Slice U8))) := fun before =>
  (fun result => (result, { before with recordRequests := before.recordRequests ++
    [RegistrationWorldAgreement.recordCall (.write request)] })) <$> writeWith helper request

def encode (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (view : registration.SignedResponseView) :
    StateT (Local n) m (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  StateT.lift (encodeWith writer view)

noncomputable def finish (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) :
    RegistrationNativePlatformCompletionSdk.Completion n m (alloc.vec.Vec U8) := fun control pending =>
  RegistrationNativePlatformSourceCompletion.fromInitialWith
    (RegistrationNativePlatformServerCompletion.records coins setup codec) (write helper)
    (RegistrationNativePlatformServerCompletion.outgoing coins sign)
    (RegistrationNativePlatformServerCompletion.capability coins) (encode writer) control pending

noncomputable def finishSource (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) m RegistrationNativePlatformCommitment.HashReply)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) :
    RegistrationNativePlatformCompletionSdk.Completion n m (alloc.vec.Vec U8) := fun control pending =>
  RegistrationNativePlatformSourceCompletion.fromInitialSource
    (RegistrationNativePlatformServerCompletion.records coins setup codec) sealing hash (write helper)
    (RegistrationNativePlatformServerCompletion.outgoing coins sign)
    (RegistrationNativePlatformServerCompletion.capability coins) (encode writer) control pending

noncomputable def pin (coins : QueryImpl unifSpec m) :
    StateT (State n) m (RustM (core.option.Option session.ServerAuthenticationPin)) := fun before =>
  (fun result => (result.1, { before with world :=
    { before.world with world := (result.2, before.world.world.2) } })) <$>
    simulateQ coins ((RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key).run
      before.world.world.1)

noncomputable def build (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : m Bool) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (handle : Nat) (application : Option (Slice U8)) :
    StateT (State n) m (RustM (Option (U64 × alloc.vec.Vec U8))) :=
  RegistrationNativePlatformCompletionSdk.build (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) (pin coins) (StateT.lift reserve)
    (RegistrationNativePlatformCompletionSdk.nativePresent coins)
    (finish coins setup codec sign helper writer) handle application

noncomputable def buildSource (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) m RegistrationNativePlatformCommitment.HashReply)
    (reserve : m Bool) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (handle : Nat) (application : Option (Slice U8)) :
    StateT (State n) m (RustM (Option (U64 × alloc.vec.Vec U8))) :=
  RegistrationNativePlatformCompletionSdk.build (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) (pin coins) (StateT.lift reserve)
    (RegistrationNativePlatformCompletionSdk.nativePresent coins)
    (finishSource coins setup codec sealing hash sign helper writer) handle application

theorem write_run (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (request : record_effects.RecordWriteRequest) (before : Local n) :
    (write helper request).run before =
      (fun result => (result, { before with recordRequests := before.recordRequests ++
        [RegistrationWorldAgreement.recordCall (.write request)] })) <$> writeWith helper request := rfl

variable [LawfulMonad m]

theorem finishSource_native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    finishSource (n := n) coins setup codec
      (fun request => RustM.ok <$> RegistrationNativePlatformServerCompletion.records coins setup codec (.seal request))
      (fun transcript => (fun reply => RustM.ok (reply, erased)) <$>
        RegistrationNativePlatformServerCompletion.records coins setup codec (.hash transcript))
      sign helper writer control pending = finish coins setup codec sign helper writer control pending := by
  unfold finishSource finish
  exact RegistrationNativePlatformSourceCompletion.fromInitialSource_native _ erased _ _ _ _ control pending

theorem buildSource_native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : commitment.CommitmentTranscript) (reserve : m Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (handle : Nat) (application : Option (Slice U8)) :
    buildSource (n := n) coins setup codec
      (fun request => RustM.ok <$> RegistrationNativePlatformServerCompletion.records coins setup codec (.seal request))
      (fun transcript => (fun reply => RustM.ok (reply, erased)) <$>
        RegistrationNativePlatformServerCompletion.records coins setup codec (.hash transcript))
      reserve sign helper writer handle application = build coins setup codec reserve sign helper writer handle application := by
  unfold buildSource build
  apply congrArg (fun finish => RegistrationNativePlatformCompletionSdk.build (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) (pin coins) (StateT.lift reserve)
    (RegistrationNativePlatformCompletionSdk.nativePresent coins) finish handle application)
  funext control pending
  exact finishSource_native coins setup codec erased sign helper writer control pending

/-- Repeated pin selection has no primitive effect and preserves the complete compiler state. -/
theorem pin_exact (coins : QueryImpl unifSpec m) (before : State n) :
    (pin coins).run before = pure (.ok (.Some before.pin), before) := by
  unfold pin StateT.run
  rw [RegistrationNativeServerPinRecompute.native_exact, simulateQ_pure, map_pure]

theorem encode_run (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (view : registration.SignedResponseView) (before : Local n) :
    (encode writer view).run before = (fun result => (result, before)) <$> encodeWith writer view := by
  simp only [encode, StateT.run_lift, bind_pure_comp]

theorem write_joint {Platform : Type}
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : record_effects.RecordWriteRequest) (current : Local n) (before : Platform) :
    ((write helper request).run current).run before =
      (fun result => ((result.1, { current with recordRequests := current.recordRequests ++
        [RegistrationWorldAgreement.recordCall (.write request)] }), result.2)) <$>
        (writeWith helper request).run before := by
  simp only [write_run, StateT.run_map]

theorem write_native {Platform : Type}
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : record_effects.RecordWriteRequest) (current : Local n) (before : Platform)
    (result : (RustM (core.option.Option (Slice U8)) × Local n) × Platform)
    (supported : result ∈ support (((write helper request).run current).run before)) :
    result.1.2.world = current.world ∧ result.1.2.auxiliary = current.auxiliary ∧
      result.1.2.requests = current.requests ∧ result.1.2.recordRequests = current.recordRequests ++
        [RegistrationWorldAgreement.recordCall (.write request)] := by
  rw [write_joint] at supported
  obtain ⟨inner, _possible, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  exact ⟨rfl, rfl, rfl, rfl⟩

section Interpret
open RegistrationNativePlatformInterpret (state state_pure state_bind)
variable {κ : Type} {spec : OracleSpec.{0, 0} κ}

private theorem helper_interpret (implementation : QueryImpl spec m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (request : record_effects.RecordWriteRequest) :
    simulateQ implementation (writeWith helper request) =
      writeWith (fun query => simulateQ implementation (helper query)) request := by
  unfold writeWith
  rw [simulateQ_map, ← QueryImpl.simulateQ_compose]
  rfl

private theorem writer_interpret (implementation : QueryImpl spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (view : registration.SignedResponseView) :
    simulateQ implementation (encodeWith writer view) =
      encodeWith (fun query => simulateQ implementation (writer query)) view := by
  unfold encodeWith
  rw [← QueryImpl.simulateQ_compose]
  rfl

theorem write_interpret (implementation : QueryImpl spec m)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (request : record_effects.RecordWriteRequest) :
    state implementation (write (n := n) helper request) =
      write (fun query => simulateQ implementation (helper query)) request := by
  funext before
  change simulateQ implementation ((write helper request).run before) =
    (write (fun query => simulateQ implementation (helper query)) request).run before
  simp only [write_run, simulateQ_map, helper_interpret]

theorem encode_interpret (implementation : QueryImpl spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (view : registration.SignedResponseView) :
    state implementation (encode (n := n) writer view) =
      encode (fun query => simulateQ implementation (writer query)) view := by
  funext before
  change simulateQ implementation ((encode writer view).run before) =
    (encode (fun query => simulateQ implementation (writer query)) view).run before
  rw [encode_run, simulateQ_map, writer_interpret, encode_run]

theorem finish_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    state implementation (finish (n := n) coins setup codec sign helper writer control pending) =
      finish (fun query => simulateQ implementation (coins query)) setup codec sign
        (fun query => simulateQ implementation (helper query))
        (fun query => simulateQ implementation (writer query)) control pending := by
  unfold finish
  rw [RegistrationNativePlatformSourceCompletion.fromInitialWith_map
    (RegistrationNativePlatformBuildInterpret.state_hom implementation)]
  simp only [RegistrationNativePlatformServerCompletion.records,
    RegistrationNativePlatformServerCompletion.outgoing, RegistrationNativePlatformServerCompletion.capability,
    RegistrationNativePlatformBuildInterpret.local_native, write_interpret, encode_interpret]
  rfl

theorem finishSource_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) (OracleComp spec)
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) (OracleComp spec) RegistrationNativePlatformCommitment.HashReply)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    state implementation (finishSource coins setup codec sealing hash sign helper writer control pending) =
      finishSource (fun query => simulateQ implementation (coins query)) setup codec
        (fun request => state implementation (sealing request)) (fun transcript => state implementation (hash transcript)) sign
        (fun query => simulateQ implementation (helper query))
        (fun query => simulateQ implementation (writer query)) control pending := by
  unfold finishSource
  rw [RegistrationNativePlatformSourceCompletion.fromInitialSource_map
    (RegistrationNativePlatformBuildInterpret.state_hom implementation)]
  simp only [RegistrationNativePlatformServerCompletion.records,
    RegistrationNativePlatformServerCompletion.outgoing, RegistrationNativePlatformServerCompletion.capability,
    RegistrationNativePlatformBuildInterpret.local_native, write_interpret, encode_interpret]
  rfl

theorem pin_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec)) :
    state implementation (pin (n := n) coins) = pin (fun query => simulateQ implementation (coins query)) := by
  funext before
  change simulateQ implementation ((pin coins).run before) =
    (pin (fun query => simulateQ implementation (coins query))).run before
  unfold pin
  simp only [StateT.run]
  rw [simulateQ_map, ← QueryImpl.simulateQ_compose]
  rfl

private theorem lift_interpret {S : Type} (implementation : QueryImpl spec m) (work : OracleComp spec Value) :
    state implementation (StateT.lift work : StateT S (OracleComp spec) Value) =
      StateT.lift (simulateQ implementation work) := by
  funext before
  change simulateQ implementation ((StateT.lift work : StateT S (OracleComp spec) Value).run before) =
    (StateT.lift (simulateQ implementation work) : StateT S m Value).run before
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure]

private theorem world_interpret (implementation : QueryImpl spec m)
    (work : StateT (Local n) (OracleComp spec) Value) :
    state implementation (RegistrationNativePlatformServerSdk.world work) =
      RegistrationNativePlatformServerSdk.world (state implementation work) := by
  funext before
  simp only [state, RegistrationNativePlatformServerSdk.world, StateT.run, simulateQ_map]

private theorem present_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (keyId : U64) :
    state implementation (RegistrationNativePlatformCompletionSdk.nativePresent (n := n) coins keyId) =
      RegistrationNativePlatformCompletionSdk.nativePresent (fun query => simulateQ implementation (coins query)) keyId := by
  unfold RegistrationNativePlatformCompletionSdk.nativePresent
  rw [world_interpret]
  simp only [RegistrationNativePlatformServerCompletion.capability, RegistrationNativePlatformBuildInterpret.local_native]

private theorem adHash_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (pending : registration.ServerAdHash) :
    state implementation (RegistrationNativePlatformCompletionSdk.nativeAdHash (n := n) coins pending) =
      RegistrationNativePlatformCompletionSdk.nativeAdHash (fun query => simulateQ implementation (coins query)) pending := by
  exact RegistrationNativePlatformBuildInterpret.sdk_adHash implementation coins pending

theorem build_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (reserve : OracleComp spec Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (handle : Nat) (application : Option (Slice U8)) :
    state implementation (build (n := n) coins setup codec reserve sign helper writer handle application) =
      build (fun query => simulateQ implementation (coins query)) setup codec (simulateQ implementation reserve) sign
        (fun query => simulateQ implementation (helper query))
        (fun query => simulateQ implementation (writer query)) handle application := by
  unfold build
  rw [RegistrationNativePlatformCompletionSdk.build_interpret]
  simp only [adHash_interpret, pin_interpret, lift_interpret, present_interpret, finish_interpret]

theorem buildSource_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) (OracleComp spec)
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) (OracleComp spec) RegistrationNativePlatformCommitment.HashReply)
    (reserve : OracleComp spec Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (handle : Nat) (application : Option (Slice U8)) :
    state implementation (buildSource coins setup codec sealing hash reserve sign helper writer handle application) =
      buildSource (fun query => simulateQ implementation (coins query)) setup codec
        (fun request => state implementation (sealing request)) (fun transcript => state implementation (hash transcript))
        (simulateQ implementation reserve) sign (fun query => simulateQ implementation (helper query))
        (fun query => simulateQ implementation (writer query)) handle application := by
  unfold buildSource
  rw [RegistrationNativePlatformCompletionSdk.build_interpret]
  simp only [adHash_interpret, pin_interpret, lift_interpret, present_interpret, finishSource_interpret]

theorem buildSource_continuation (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) (OracleComp spec)
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) (OracleComp spec) RegistrationNativePlatformCommitment.HashReply)
    (reserve : OracleComp spec Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (handle : Nat) (application : Option (Slice U8))
    (next : RustM (Option (U64 × alloc.vec.Vec U8)) → StateT (State n) (OracleComp spec) Value) :
    state implementation (buildSource coins setup codec sealing hash reserve sign helper writer handle application >>= next) = (do
      let result ← buildSource (fun query => simulateQ implementation (coins query)) setup codec
        (fun request => state implementation (sealing request)) (fun transcript => state implementation (hash transcript))
        (simulateQ implementation reserve) sign (fun query => simulateQ implementation (helper query))
        (fun query => simulateQ implementation (writer query)) handle application
      state implementation (next result)) := by
  rw [RegistrationNativePlatformInterpret.state_bind, buildSource_interpret]

theorem build_continuation (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (reserve : OracleComp spec Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (handle : Nat) (application : Option (Slice U8))
    (next : RustM (Option (U64 × alloc.vec.Vec U8)) → StateT (State n) (OracleComp spec) Value) :
    state implementation (build coins setup codec reserve sign helper writer handle application >>= next) = (do
      let result ← build (fun query => simulateQ implementation (coins query)) setup codec
        (simulateQ implementation reserve) sign (fun query => simulateQ implementation (helper query))
        (fun query => simulateQ implementation (writer query)) handle application
      state implementation (next result)) := by
  rw [RegistrationNativePlatformInterpret.state_bind, build_interpret]

end Interpret

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.write_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.write_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.pin_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.pin_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.encode_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.encode_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.write_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.write_joint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.write_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.write_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.write_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.write_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.encode_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.encode_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.finish_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.finish_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.pin_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.pin_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.build_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.build_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.build_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.build_continuation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.finishSource_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.finishSource_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.buildSource_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.buildSource_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.finishSource_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.finishSource_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.buildSource_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.buildSource_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.buildSource_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.buildSource_continuation
