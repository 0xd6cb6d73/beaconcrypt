-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerBuildTrace
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
namespace BeaconcryptCore.Refinement.AdapterPublicServerBuildWithRecord
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open AdapterPublicServerBuildBody (Server Reply)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type  →  Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)] [containers : ContainerOperations (RustT m)]

open AdapterPublicServerBuildTrace (Publication Word)
variable (completion :Server → registration.ServerInitialKdf → m (Publication×RustM Reply))
variable (record :Server → registration.ServerInitialKdf → m (RustM Reply))
noncomputable def reserved (record :Server → registration.ServerInitialKdf → m (RustM Reply)) (self : Server) (pending : registration.ServerInitialKdf) : RustT m Reply := do
  let (allocation, known) ← containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize
  let current := { self with known_ids := known }
  match allocation with
  | .Err _ => pure (.None, current)
  | .Ok _ => ⟨record current pending⟩

noncomputable def adHash (record : Server → registration.ServerInitialKdf → m (RustM Reply))
    (self : Server) (pending : registration.ServerAdHash) : RustT m Reply := do
  let request ← liftRust pending.request
  let digest ← children.executeHash request
  AdapterPublicServerBuildBody.checked self (pending.resume digest) (reserved record self)

noncomputable def lookup (record :Server → registration.ServerInitialKdf → m (RustM Reply)) (self : Server) (pending : peer.CompletionLookup) (plaintext : Slice U8) : RustT m Reply := do
  let identifier ← liftRust pending.request
  let size ← liftRust (CoreModels.core.slice.Slice.len plaintext)
  let admitted ← beaconcrypt_public_request.server.registration_response_len size identifier
  match admitted with
  | .None => pure (.None, self)
  | .Some _ =>
    let occupied ← containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
      core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
        (core.borrow.Borrow.Blanket U64)) self.known_ids identifier
    AdapterPublicServerBuildBody.checked self (pending.resume occupied) (adHash record self)

noncomputable def build (record :Server → registration.ServerInitialKdf → m (RustM Reply)) (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) : RustT m Reply := do
  let application ← liftRust (transport.normalize_registration_application data)
  let plaintext ← liftRust (beaconcrypt_public_wrapper.server.registration_application_bytes application)
  let pin ← beaconcrypt_public_request.server.Server.authentication_pin self
  match pin with
  | .None => pure (.None, self)
  | .Some pin =>
    AdapterPublicServerBuildBody.checked self (peer.begin_completion_lookup self.control pin token.registration plaintext)
      (fun pending => lookup record self pending plaintext)
omit localOps crypto children containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem invoke_erasure {A : Type} (work : RustT m A) (next : A  →  m Word) :
    Prod.snd <$> AdapterPublicServerBuildTrace.invoke work next = (do
      let result ← work.run
      match result with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok value => Prod.snd <$> next value) := by
  unfold AdapterPublicServerBuildTrace.invoke
  rw [map_bind]
  apply bind_congr
  intro result
  cases result <;> simp only [map_pure]

omit localOps crypto children containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem checked_erasure {A Error : Type} (self : Server) (work : RustM (core.result.Result A Error))
    (next : A  →  m Word) :
    Prod.snd <$> AdapterPublicServerBuildTrace.checked self work next = AdapterPublicServerRecord.resumeResult self work
      (fun value => Prod.snd <$> next value) := by
  cases work with
  | fail error | div => simp only [AdapterPublicServerBuildTrace.checked, map_pure, AdapterPublicServerRecord.resumeResult]
  | ok result => cases result <;> simp only [AdapterPublicServerBuildTrace.checked, map_pure, AdapterPublicServerRecord.resumeResult]

omit localOps crypto children in
private theorem reserved_erasure
    (matched : ∀ current initial, Prod.snd <$> completion current initial = record current initial)
    (self : Server) (initial : registration.ServerInitialKdf) :
    Prod.snd <$> AdapterPublicServerBuildTrace.reserved completion self initial = (reserved record self initial).run := by
  unfold AdapterPublicServerBuildTrace.reserved reserved
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

omit localOps crypto in
private theorem adHash_erasure
    (matched : ∀ current initial, Prod.snd <$> completion current initial = record current initial)
    (self : Server) (pending : registration.ServerAdHash) :
    Prod.snd <$> AdapterPublicServerBuildTrace.adHash completion self pending = (adHash record self pending).run := by
  unfold AdapterPublicServerBuildTrace.adHash adHash
  rw [invoke_erasure, RustT.run_bind]
  apply bind_congr
  intro requested
  cases requested with
  | fail error | div => rfl
  | ok request =>
    simp only []
    rw [invoke_erasure, RustT.run_bind]
    apply bind_congr
    intro digest
    cases digest with
    | fail error | div => rfl
    | ok digest =>
      simp only []
      rw [checked_erasure, AdapterPublicServerRecord.checked]
      exact congrArg (AdapterPublicServerRecord.resumeResult self (pending.resume digest))
        (funext (fun initial => reserved_erasure completion record matched self initial))

omit localOps crypto in
private theorem lookup_erasure
    (matched : ∀ current initial, Prod.snd <$> completion current initial = record current initial)
    (self : Server) (pending : peer.CompletionLookup) (plaintext : Slice U8) :
    Prod.snd <$> AdapterPublicServerBuildTrace.lookup completion self pending plaintext = (lookup record self pending plaintext).run := by
  unfold AdapterPublicServerBuildTrace.lookup lookup
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
                (funext (fun selected => adHash_erasure completion record matched self selected))

theorem factor
    (matched : ∀ current initial, Prod.snd <$> completion current initial = record current initial)
    (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) :
    Prod.snd <$> AdapterPublicServerBuildTrace.build completion self token data = (build record self token data).run := by
  unfold AdapterPublicServerBuildTrace.build build
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
              (funext (fun pending => lookup_erasure completion record matched self pending plaintext))


theorem source (self :Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :
    (beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
      (m:=RustT m) self token data).run=
      (build (fun current initial=>(AdapterPublicServerBuildBody.record (m:=m) current initial).run) self token data).run :=by
  rw [AdapterPublicServerBuildBody.source]
  rfl
end BeaconcryptCore.Refinement.AdapterPublicServerBuildWithRecord

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildWithRecord.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildWithRecord.factor

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildWithRecord.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildWithRecord.source
