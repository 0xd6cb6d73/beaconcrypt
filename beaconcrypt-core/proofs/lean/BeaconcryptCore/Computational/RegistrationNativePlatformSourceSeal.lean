-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterSealNative
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild

/-! The actual seal request program is interpreted with public allocation outcomes and the original native World's AEAD leaf. Allocation preserves the supplied Vec contents by construction, while retaining arbitrary failure/divergence and external poststates. Opaque key/nonce byte views are primitive representation data; their narrow successful-conversion contract is explicit. The source wrapper records one reached seal call, and only the actual AEAD leaf updates primitive AEAD counts. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {E Auxiliary Value ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m]

structure KeyView where
  key : primitives.Key → Std.Array U8 32#usize
  nonce : primitives.Nonce → Std.Array U8 12#usize

def KeyView.Correct (view : KeyView) : Prop :=
  (∀ input output, primitives.fromKey input = .ok output → view.key output = input) ∧
  (∀ input output, primitives.fromNonce input = .ok output → view.nonce output = input)

abbrev Allocation (E : Type) (m : Type → Type) :=
  alloc.vec.Vec U8 → Usize → m (RustM (core.result.Result Unit E))

def reserve (allocation : Allocation E m) (before : alloc.vec.Vec U8) (capacity : Usize) :
    m (RustM (core.result.Result Unit E × alloc.vec.Vec U8)) :=
  (fun result => do let reply ← result; .ok (reply, before)) <$> allocation before capacity

def input (view : KeyView) (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
    (nonce : primitives.Nonce) (key : primitives.Key) : RawCtxSourceSeal.AeadInput :=
  ⟨PqxdhRefinement.absBytes (view.key key), PqxdhRefinement.absBytes (view.nonce nonce),
    match associated with
    | .none => []
    | .some bytes => TranscriptAuthParts.absSlice bytes,
    TranscriptAuthParts.absSlice plaintext⟩

def detached (failure : primitives.Error) (reply : Option (Pqxdh.Bytes × Pqxdh.Bytes)) :
    core.result.Result (alloc.vec.Vec U8 × Std.Array U8 16#usize) primitives.Error :=
  match RegistrationRecordPrimitives.sealedBytes reply with
  | .none => .Err failure
  | .some value => .Ok value

noncomputable def aead (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : KeyView) (failure : primitives.Error)
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
    (nonce : primitives.Nonce) (key : primitives.Key) :
    StateT (State n Auxiliary) m AdapterSealNative.NativeReply := fun before =>
  (fun result => (.ok (detached failure result.1), result.2)) <$>
    simulateQ coins ((RegistrationWorldRecords.record setup codec
      (.inr (.inl (input view plaintext associated nonce key)))).run before)

noncomputable def handler (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : KeyView) (failure : primitives.Error) (allocation : Allocation E m) :
    QueryImpl (AdapterSealNative.Spec E) (StateT (State n Auxiliary) m)
  | .reserve before capacity => StateT.lift (reserve allocation before capacity)
  | .aead plaintext associated nonce key => aead coins setup codec view failure plaintext associated nonce key

noncomputable def sealing (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : KeyView) (failure : primitives.Error) (allocation : Allocation E m)
    (request : record_effects.AeadSealRequest) :
    StateT (State n Auxiliary) m (RustM AdapterSealNative.Output) := do
  let result ← simulateQ (handler coins setup codec view failure allocation) (AdapterSealNative.execute E request)
  modify fun before => { before with recordRequests := before.recordRequests ++
    [RegistrationWorldAgreement.recordCall (.seal request)] }
  pure result

noncomputable def hash (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : commitment.CommitmentTranscript) (transcript : commitment.CommitmentTranscript) :
    StateT (State n Auxiliary) m RegistrationNativePlatformCommitment.HashReply := do
  let reply ← RegistrationNativePlatformServerCompletion.records coins setup codec (.hash transcript)
  pure (.ok (reply, erased))

noncomputable def build (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : KeyView) (failure : primitives.Error) (allocation : Allocation E m)
    (erased : commitment.CommitmentTranscript) (reservePeer : m Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (handle : Nat) (application : Option (Slice U8)) :
    StateT (RegistrationServerFrontendCompiler.State n) m (RustM (Option (U64 × alloc.vec.Vec U8))) :=
  RegistrationNativePlatformSourceBuild.buildSource coins setup codec
    (sealing coins setup codec view failure allocation) (hash coins setup codec erased) reservePeer sign helper writer handle application

variable [LawfulMonad m]

theorem source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : KeyView) (failure : primitives.Error) (allocation : Allocation E m)
    (request : record_effects.AeadSealRequest) :
    sealing (n := n) (Auxiliary := Auxiliary) coins setup codec view failure allocation request = (do
      let result ← simulateQ (handler coins setup codec view failure allocation ∘ₛ AdapterSealNative.native)
        (AdapterSealRequestExtraction.execute (E := E) (m := AdapterSealRequestMonad.Program E) request).run
      modify fun before => { before with recordRequests := before.recordRequests ++
        [RegistrationWorldAgreement.recordCall (.seal request)] }
      pure result) := by
  unfold sealing
  rw [QueryImpl.simulateQ_compose]
  rw [show simulateQ AdapterSealNative.native
    (AdapterSealRequestExtraction.execute (E := E) (m := AdapterSealRequestMonad.Program E) request).run =
      AdapterSealNative.execute E request from AdapterSealNative.source_native E request]

theorem build_source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : KeyView) (failure : primitives.Error) (allocation : Allocation E m)
    (erased : commitment.CommitmentTranscript) (reservePeer : m Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (handle : Nat) (application : Option (Slice U8)) :
    build (n := n) coins setup codec view failure allocation erased reservePeer sign helper writer handle application =
      RegistrationNativePlatformSourceBuild.buildSource coins setup codec
        (fun request => do
          let result ← simulateQ (handler coins setup codec view failure allocation ∘ₛ AdapterSealNative.native)
            (AdapterSealRequestExtraction.execute (E := E) (m := AdapterSealRequestMonad.Program E) request).run
          modify fun before => { before with recordRequests := before.recordRequests ++
            [RegistrationWorldAgreement.recordCall (.seal request)] }
          pure result)
        (hash coins setup codec erased) reservePeer sign helper writer handle application := by
  unfold build
  congr 1
  funext request
  exact source coins setup codec view failure allocation request

omit [LawfulMonad m] in
theorem aead_run (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : KeyView) (failure : primitives.Error)
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
    (nonce : primitives.Nonce) (key : primitives.Key) (before : State n Auxiliary) :
    (aead coins setup codec view failure plaintext associated nonce key).run before =
      (fun result => (.ok (detached failure result.1), result.2)) <$>
        simulateQ coins ((RegistrationWorldRecords.record setup codec
          (.inr (.inl (input view plaintext associated nonce key)))).run before) := rfl

omit primitives in
theorem reserve_joint {Platform : Type} (allocation : Allocation E (StateT Platform ProbComp))
    (before : alloc.vec.Vec U8) (capacity : Usize) (platform : Platform) :
    (reserve allocation before capacity).run platform =
      (fun result => ((do let reply ← result.1; .ok (reply, before)), result.2)) <$>
        (allocation before capacity).run platform := by
  simp only [reserve, StateT.run_map]

theorem reserve_native {Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (view : KeyView) (failure : primitives.Error)
    (allocation : Allocation E (StateT Platform ProbComp)) (before : alloc.vec.Vec U8) (capacity : Usize)
    (current : State n Auxiliary) (platform : Platform) :
    ((handler coins setup codec view failure allocation (.reserve before capacity)).run current).run platform =
      (fun result => ((result.1, current), result.2)) <$>
        (reserve allocation before capacity).run platform := by
  simp only [handler, StateT.run_lift, bind_pure_comp, StateT.run_map]

section Interpret
open RegistrationNativePlatformInterpret (state state_bind state_pure state_simulate)
variable {κ : Type} {spec : OracleSpec.{0, 0} κ}

omit primitives in
private theorem reserve_interpret (implementation : QueryImpl spec m)
    (allocation : Allocation E (OracleComp spec)) (before : alloc.vec.Vec U8) (capacity : Usize) :
    simulateQ implementation (reserve allocation before capacity) =
      reserve (fun before capacity => simulateQ implementation (allocation before capacity)) before capacity := by
  unfold reserve
  rw [simulateQ_map]

private theorem aead_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (view : KeyView) (failure : primitives.Error)
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
    (nonce : primitives.Nonce) (key : primitives.Key) :
    state implementation (aead (n := n) (Auxiliary := Auxiliary) coins setup codec view failure plaintext associated nonce key) =
      aead (fun query => simulateQ implementation (coins query)) setup codec view failure plaintext associated nonce key := by
  funext before
  unfold aead state StateT.run
  rw [simulateQ_map, ← QueryImpl.simulateQ_compose]
  rfl

omit primitives in
private theorem lift_interpret (implementation : QueryImpl spec m) {S A : Type} (work : OracleComp spec A) :
    state implementation (StateT.lift work : StateT S (OracleComp spec) A) = StateT.lift (simulateQ implementation work) := by
  funext before
  change simulateQ implementation ((StateT.lift work : StateT S (OracleComp spec) A).run before) =
    (StateT.lift (simulateQ implementation work) : StateT S m A).run before
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure]

private theorem handler_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (view : KeyView) (failure : primitives.Error)
    (allocation : Allocation E (OracleComp spec)) (query : (AdapterSealNative.Spec E).Domain) :
    state implementation (handler (n := n) (Auxiliary := Auxiliary) coins setup codec view failure allocation query) =
      handler (fun query => simulateQ implementation (coins query)) setup codec view failure
        (fun before capacity => simulateQ implementation (allocation before capacity)) query := by
  cases query with
  | reserve before capacity =>
      unfold handler
      rw [lift_interpret, reserve_interpret]
  | aead plaintext associated nonce key => exact aead_interpret implementation coins setup codec view failure plaintext associated nonce key

theorem sealing_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (view : KeyView) (failure : primitives.Error)
    (allocation : Allocation E (OracleComp spec)) (request : record_effects.AeadSealRequest) :
    state implementation (sealing (n := n) (Auxiliary := Auxiliary) coins setup codec view failure allocation request) =
      sealing (fun query => simulateQ implementation (coins query)) setup codec view failure
        (fun before capacity => simulateQ implementation (allocation before capacity)) request := by
  unfold sealing
  rw [state_bind, state_simulate]
  simp only [handler_interpret]
  apply bind_congr
  intro result
  rw [state_bind]
  have update : state implementation
      (modify fun before : State n Auxiliary => { before with recordRequests := before.recordRequests ++
        [RegistrationWorldAgreement.recordCall (.seal request)] }) =
      (modify fun before : State n Auxiliary => { before with recordRequests := before.recordRequests ++
        [RegistrationWorldAgreement.recordCall (.seal request)] } : StateT (State n Auxiliary) m Unit) := rfl
  rw [update]
  apply bind_congr
  intro unused
  exact state_pure implementation result

omit primitives in
private theorem hash_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (erased transcript : commitment.CommitmentTranscript) :
    state implementation (hash (n := n) (Auxiliary := Auxiliary) coins setup codec erased transcript) =
      hash (fun query => simulateQ implementation (coins query)) setup codec erased transcript := by
  unfold hash
  rw [state_bind]
  simp only [RegistrationNativePlatformServerCompletion.records, RegistrationNativePlatformBuildInterpret.local_native]
  apply bind_congr
  intro reply
  exact state_pure implementation _

theorem build_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (view : KeyView) (failure : primitives.Error)
    (allocation : Allocation E (OracleComp spec)) (erased : commitment.CommitmentTranscript) (reservePeer : OracleComp spec Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (OracleComp spec))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (OracleComp spec))
    (handle : Nat) (application : Option (Slice U8)) :
    state implementation (build (n := n) coins setup codec view failure allocation erased reservePeer sign helper writer handle application) =
      build (fun query => simulateQ implementation (coins query)) setup codec view failure
        (fun before capacity => simulateQ implementation (allocation before capacity)) erased (simulateQ implementation reservePeer) sign
        (fun query => simulateQ implementation (helper query)) (fun query => simulateQ implementation (writer query)) handle application := by
  unfold build
  rw [RegistrationNativePlatformSourceBuild.buildSource_interpret]
  simp only [hash_interpret]
  congr 1
  funext request
  exact sealing_interpret implementation coins setup codec view failure allocation request

end Interpret

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.build_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.aead_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.aead_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.reserve_joint' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.reserve_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.reserve_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.reserve_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.sealing_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.sealing_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.build_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.build_interpret
