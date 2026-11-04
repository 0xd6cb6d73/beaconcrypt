-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionLifetime
import BeaconcryptCore.Refinement.AdapterPublicServerCutPin
import BeaconcryptCore.Refinement.AdapterPublicServerPresenceNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Private same-run publication receipts extend through the literal enclosing source build prefix. Pin computation, response preflight, readonly map membership and fallible map reservation retain their original call order and complete mutable poststates. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerBuildTrace
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open AdapterPublicServerBuildBody (Server Reply)
section Generic
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)] [containers : ContainerOperations (RustT m)]
abbrev Publication := RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))
abbrev Word := Option Publication × RustM Reply

omit localOps crypto children containers in
def invoke {A : Type} (work : RustT m A) (next : A → m Word) : m Word := do
  let result ← work.run
  match result with
  | .fail error => pure (none, .fail error)
  | .div => pure (none, .div)
  | .ok value => next value

omit localOps crypto children containers in
def checked {A Error : Type} (self : Server) (work : RustM (core.result.Result A Error))
    (next : A → m Word) : m Word :=
  match work with
  | .fail error => pure (none, .fail error)
  | .div => pure (none, .div)
  | .ok (.Err _) => pure (none, .ok (.None, self))
  | .ok (.Ok value) => next value

variable (completion : Server → registration.ServerInitialKdf → m (Publication × RustM Reply))

noncomputable def reserved (self : Server) (initial : registration.ServerInitialKdf) : m Word :=
  invoke (containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize) fun result =>
    let current := {self with known_ids := result.2}
    match result.1 with
    | .Err _ => pure (none, .ok (.None, current))
    | .Ok _ => (fun result => (some result.1, result.2)) <$> completion current initial

noncomputable def lookup (self : Server) (pending : peer.CompletionLookup) (plaintext : Slice U8) : m Word :=
  invoke (liftRust pending.request) fun identifier =>
  invoke (liftRust (CoreModels.core.slice.Slice.len plaintext)) fun size =>
  invoke (beaconcrypt_public_request.server.registration_response_len size identifier) fun admitted =>
    match admitted with
    | .None => pure (none, .ok (.None, self))
    | .Some _ =>
      invoke (containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) self.known_ids identifier) fun occupied =>
        checked self (pending.resume occupied) (reserved completion self)

noncomputable def build (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) : m Word :=
  invoke (liftRust (transport.normalize_registration_application data)) fun application =>
  invoke (liftRust (beaconcrypt_public_wrapper.server.registration_application_bytes application)) fun plaintext =>
  invoke (beaconcrypt_public_request.server.Server.authentication_pin self) fun pin =>
    match pin with
    | .None => pure (none, .ok (.None, self))
    | .Some pin => checked self (peer.begin_completion_lookup self.control pin token.registration plaintext)
        (fun pending => lookup completion self pending plaintext)

omit localOps crypto children containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem invoke_erasure {A : Type} (work : RustT m A) (next : A → m Word) :
    Prod.snd <$> invoke work next = (do
      let result ← work.run
      match result with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok value => Prod.snd <$> next value) := by
  unfold invoke
  rw [map_bind]
  apply bind_congr
  intro result
  cases result <;> simp only [map_pure]

omit localOps crypto children containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem checked_erasure {A Error : Type} (self : Server) (work : RustM (core.result.Result A Error))
    (next : A → m Word) :
    Prod.snd <$> checked self work next = AdapterPublicServerRecord.resumeResult self work
      (fun value => Prod.snd <$> next value) := by
  cases work with
  | fail error | div => simp only [checked, map_pure, AdapterPublicServerRecord.resumeResult]
  | ok result => cases result <;> simp only [checked, map_pure, AdapterPublicServerRecord.resumeResult]

omit crypto in
private theorem reserved_erasure
    (matched : ∀ current initial, Prod.snd <$> completion current initial = (AdapterPublicServerBuildBody.record (m := m) current initial).run)
    (self : Server) (initial : registration.ServerInitialKdf) :
    Prod.snd <$> reserved completion self initial = (AdapterPublicServerBuildBody.reserved (m := m) self initial).run := by
  unfold reserved AdapterPublicServerBuildBody.reserved
  rw [invoke_erasure, RustT.run_bind]
  apply bind_congr
  intro result
  cases result with
  | fail error | div => rfl
  | ok pair =>
    rcases pair with ⟨allocation, known⟩
    cases allocation with
    | Err error => simp only [map_pure, RustT.run_pure]
    | Ok unitValue =>
      simp only [Functor.map_map]
      exact matched {self with known_ids := known} initial

omit crypto in
private theorem lookup_erasure
    (matched : ∀ current initial, Prod.snd <$> completion current initial = (AdapterPublicServerBuildBody.record (m := m) current initial).run)
    (self : Server) (pending : peer.CompletionLookup) (plaintext : Slice U8) :
    Prod.snd <$> lookup completion self pending plaintext = (AdapterPublicServerBuildBody.lookup (m := m) self pending plaintext).run := by
  unfold lookup AdapterPublicServerBuildBody.lookup
  rw [invoke_erasure, RustT.run_bind]
  apply bind_congr
  intro requested
  cases requested with
  | fail error | div => rfl
  | ok identifier =>
    simp only []
    rw [invoke_erasure, RustT.run_bind]
    apply bind_congr
    intro sized
    cases sized with
    | fail error | div => rfl
    | ok size =>
      simp only []
      rw [invoke_erasure, RustT.run_bind]
      apply bind_congr
      intro admitted
      cases admitted with
      | fail error | div => rfl
      | ok optional =>
        simp only []
        cases optional with
        | none => simp only [map_pure, RustT.run_pure]
        | some capacity =>
          simp only []
          rw [invoke_erasure, RustT.run_bind]
          apply bind_congr
          intro occupied
          cases occupied with
          | fail error | div => rfl
          | ok occupied =>
            simp only []
            rw [checked_erasure, AdapterPublicServerRecord.checked]
            exact congrArg (AdapterPublicServerRecord.resumeResult self (pending.resume occupied))
                (funext (fun initial => reserved_erasure completion matched self initial))

private theorem build_erasure
    (matched : ∀ current initial, Prod.snd <$> completion current initial = (AdapterPublicServerBuildBody.record (m := m) current initial).run)
    (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) :
    Prod.snd <$> build completion self token data = (AdapterPublicServerBuildBody.build (m := m) self token data).run := by
  unfold build AdapterPublicServerBuildBody.build
  rw [invoke_erasure, RustT.run_bind]
  apply bind_congr
  intro normalized
  cases normalized with
  | fail error | div => rfl
  | ok application =>
    simp only []
    rw [invoke_erasure, RustT.run_bind]
    apply bind_congr
    intro bytes
    cases bytes with
    | fail error | div => rfl
    | ok plaintext =>
      simp only []
      rw [invoke_erasure, RustT.run_bind]
      apply bind_congr
      intro pinned
      cases pinned with
      | fail error | div => rfl
      | ok optional =>
        simp only []
        cases optional with
        | none => simp only [map_pure, RustT.run_pure]
        | some pin =>
          simp only []
          rw [checked_erasure, AdapterPublicServerRecord.checked]
          exact congrArg (AdapterPublicServerRecord.resumeResult self
            (peer.begin_completion_lookup self.control pin token.registration plaintext))
              (funext (fun pending => lookup_erasure completion matched self pending plaintext))


/-- The actual source Builder prefix accepts an internally derived record interpreter in any lawful source effect monad. The equality retains that monad's complete state, including source observations. -/
theorem generic_source
    (matched :∀current initial,Prod.snd <$>completion current initial=(AdapterPublicServerBuildBody.record (m:=m) current initial).run)
    (self :Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :
    Prod.snd <$>build completion self token data=
      (beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m:=RustT m) self token data).run :=by
  rw [AdapterPublicServerBuildBody.source]
  exact build_erasure completion matched self token data

end Generic

section Actual
variable {n : Nat} {KemSK Platform E I Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Base" => StateT Platform ProbComp
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource Base
local notation "SourceM" => StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) Base
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [primitive : AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]

noncomputable def complete
    (coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)
    (self : Server) (initial : registration.ServerInitialKdf) : SourceM (Publication × RustM Reply) :=
  AdapterPublicServerCompletionSource.receipt
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback coins setup codec keyView failure allocation helper erased
    (AdapterPublicServerCompletionNative.writer writer) self initial

theorem source
    (previousLocal : LocalOperations (RustT SourceM)) (previousChildren : ChildOperations (RustT SourceM))
    (coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)
    [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
      (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
    (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) :
    letI : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    Prod.snd <$> build (complete coins setup codec keyView failure allocation helper erased sign writer fallback) self token data =
      (beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m := RustT SourceM) self token data).run := by
  let : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  let : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  rw [AdapterPublicServerBuildBody.source]
  apply build_erasure
  intro current initial
  exact (AdapterPublicServerCompletionLifetime.source_marginal previousLocal previousChildren coins setup codec keyView failure allocation helper erased sign writer fallback current initial).symm
end Actual

end BeaconcryptCore.Refinement.AdapterPublicServerBuildTrace

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildTrace.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildTrace.source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildTrace.generic_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildTrace.generic_source
