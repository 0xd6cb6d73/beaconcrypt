-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall
import BeaconcryptCore.Refinement.AdapterPublicServerPublication
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The literal source publication installer and native installation/commit share the same live counter and standard map-entry footprint. Every occupied rejection retains the original control while charging the actual native capability; a vacant insertion installs the exact binding, kernel and bytes. Authentication-derived parsing receipts remain explicit. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerPublicationInstall
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
variable {n : Nat} {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "ServerM" => StateT (RegistrationServerFrontendCompiler.State n) m

noncomputable def native (coins : QueryImpl unifSpec m) (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) :
    ServerM (RustM (Option (U64 × alloc.vec.Vec U8))) := do
  let installed ← RegistrationNativePlatformServerSdk.world
    (RegistrationNativePlatformServerCompletion.continueResult published
      (RegistrationNativePlatformServerCompletion.installWith
        (RegistrationNativePlatformServerCompletion.capability coins) control))
  RegistrationNativePlatformServerSdk.commit installed

private theorem world_bind {A B : Type} (work : StateT (RegistrationServerRootCompiler.Local n) m A)
    (next : A → StateT (RegistrationServerRootCompiler.Local n) m B) :
    RegistrationNativePlatformServerSdk.world (work >>= next) =
      (RegistrationNativePlatformServerSdk.world work >>= fun value => RegistrationNativePlatformServerSdk.world (next value)) := by
  apply StateT.ext
  intro before
  change (fun result => (result.1, {before with world := result.2})) <$> ((work >>= next).run before.world) = _
  simp only [StateT.run_bind, map_bind]
  change _ = ((fun result => (result.1, {before with world := result.2})) <$> work.run before.world >>= fun result =>
    (fun output => (output.1, {result.2 with world := output.2})) <$> (next result.1).run result.2.world)
  rw [bind_map_left]

private theorem world_pure {A : Type} (value : A) :
    RegistrationNativePlatformServerSdk.world (pure value : StateT (RegistrationServerRootCompiler.Local n) m A) =
      (pure value : ServerM A) := by
  apply StateT.ext
  intro before
  change (fun result => (result.1, {before with world := result.2})) <$> pure (value, before.world) = pure (value, before)
  rw [map_pure]

private theorem world_capability (coins : QueryImpl unifSpec m) (pending : peer.PeerInsert (alloc.vec.Vec U8)) :
    RegistrationNativePlatformServerSdk.world
      (RegistrationNativePlatformServerCompletion.capability (n := n) coins
        (.installServer pending.peer.binding.assigned_key_id (PqxdhRecordLiftInterface.PeerBinding.ofSession pending.peer.binding)
          (.known pending.peer.ratchet))) =
      RegistrationNativePlatformServerSdk.liftNative coins (AdapterPublicServerInstallNative.capability pending) := by
  apply StateT.ext
  intro before
  change (fun result => (result.1, {before with world := result.2})) <$>
      simulateQ coins ((RegistrationWorldServerCompletion.capability
        (.installServer pending.peer.binding.assigned_key_id (PqxdhRecordLiftInterface.PeerBinding.ofSession pending.peer.binding)
          (.known pending.peer.ratchet))).run before.world) =
    simulateQ coins ((fun result => (result.1, {before with world := result.2})) <$>
      ((RegistrationWorldServerCompletion.capability
        (.installServer pending.peer.binding.assigned_key_id (PqxdhRecordLiftInterface.PeerBinding.ofSession pending.peer.binding)
          (.known pending.peer.ratchet))).run before.world))
  rw [simulateQ_map]

theorem native_insert (coins : QueryImpl unifSpec m) (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse (alloc.vec.Vec U8))
    (pending : peer.PeerInsert (alloc.vec.Vec U8))
    (began : peer.begin_peer_insert control published = .ok (.Ok pending)) :
    native (n := n) coins control (.ok (.Ok published)) = (do
      let inserted ← RegistrationNativePlatformServerSdk.liftNative coins
        (AdapterPublicServerInstallNative.capability pending)
      RegistrationNativePlatformServerSdk.commit
        ((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
          peer.PublicationFinish (alloc.vec.Vec U8)).finish inserted)) := by
  unfold native
  simp only [RegistrationNativePlatformServerCompletion.continueResult,
    RegistrationNativePlatformServerCompletion.installWith, began,
    PeerOwnership.peer_insert_request, PeerOwnership.peer_insert_parts,
    RegistrationNativePlatformServerCompletion.continueWith]
  rw [world_bind]
  simp only [world_pure, bind_assoc, pure_bind]
  rw [world_capability]

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT m)]
variable {mlSource : RegistrationNativeMldsa.Source} {KemSK : Type}

def output (reply : core.option.Option beaconcrypt_public_wrapper.server.RegResponse) : Option (U64 × alloc.vec.Vec U8) :=
  match reply with | .None => none | .Some response => some (response.kid, response.serialized)

theorem install (coins : QueryImpl unifSpec m)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self before)
    (published : registration.PublishedServerResponse (alloc.vec.Vec U8))
    (pending : peer.PeerInsert (alloc.vec.Vec U8))
    (began : peer.begin_peer_insert self.control published = .ok (.Ok pending))
    (publicKey : ed.PublicKey)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
      pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey))
    (standard : AdapterPublicServerInstallFunctional.Standard (m := m) views self pending publicKey) :
    ∃ reply current after,
      AdapterPublicServerBuildBody.install (m := m) self pending = pure (reply, current) ∧
      (native coins self.control (.ok (.Ok published))).run before = pure (.ok (output reply), after) ∧
      Server view views created credential current after := by
  obtain ⟨reply, current, after, actual, installed, retained, bytes⟩ :=
    AdapterPublicServerInstallFunctional.functional view views created credential self before related published pending began publicKey parsed standard
  refine ⟨reply, current, {after with control := if _root_.Option.isSome reply then pending.next else pending.previous}, actual, ?_, retained⟩
  rw [native_insert coins self.control published pending began]
  rw [StateT.run_bind]
  change (do let result ← simulateQ coins ((AdapterPublicServerInstallNative.capability pending).run before)
             (RegistrationNativePlatformServerSdk.commit
               ((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
                 peer.PublicationFinish (alloc.vec.Vec U8)).finish result.1)).run result.2) = _
  rw [installed, simulateQ_pure, pure_bind]
  cases reply with
  | none => rfl
  | some response =>
    obtain ⟨encoded, identifier⟩ := bytes response rfl
    simp only [output, encoded, identifier, PeerOwnership.publication_finish]
    rfl
def project (result : RustM AdapterPublicServerBuildBody.Reply) : RustM (Option (U64 × alloc.vec.Vec U8)) :=
  match result with | .fail error => .fail error | .div => .div | .ok (reply, _) => .ok (output reply)

def Returned (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (result : RustM AdapterPublicServerBuildBody.Reply) (after : RegistrationServerFrontendCompiler.State n) : Prop :=
  match result with | .fail _ | .div => True | .ok (_, current) => Server view views created credential current after

theorem publication (coins : QueryImpl unifSpec m)
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self before)
    (initial : registration.ServerInitialKdf)
    (previous : initial.candidate.previous_state = self.control)
    (parsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (retained : RegistrationServerSourceCompletionReceipt.Post initial published)
    (standard : ∀ publication pending publicKey,
      published = .ok (.Ok publication) → peer.begin_peer_insert self.control publication = .ok (.Ok pending) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := m) views self pending publicKey) :
    ∃ result after,
      AdapterPublicServerPublication.afterPublication (m := m) self published = pure result ∧
      (native coins self.control published).run before = pure (project result, after) ∧
      Returned view views created credential result after := by
  cases published with
  | fail error =>
    refine ⟨.fail error, before, rfl, ?_, trivial⟩
    simp only [native, RegistrationNativePlatformServerCompletion.continueResult, world_pure, pure_bind]
    rfl
  | div =>
    refine ⟨.div, before, rfl, ?_, trivial⟩
    simp only [native, RegistrationNativePlatformServerCompletion.continueResult, world_pure, pure_bind]
    rfl
  | ok result => cases result with
    | Err rejected =>
      have control : rejected = before.control := retained.trans (previous.trans related.control)
      refine ⟨.ok (.None, self), before, rfl, ?_, related⟩
      simp only [native, RegistrationNativePlatformServerCompletion.continueResult, world_pure, pure_bind]
      change pure (RustM.ok (none : Option (U64 × alloc.vec.Vec U8)), {before with control := rejected}) = pure (RustM.ok none, before)
      rw [control]
    | Ok published =>
      obtain ⟨result, began, fields⟩ := PeerOwnership.peer_insert_begin_retains self.control published
      cases result with
      | Err rejected =>
        have control : rejected = before.control := fields.trans related.control
        refine ⟨.ok (.None, self), before, ?_, ?_, related⟩
        · simp only [AdapterPublicServerPublication.afterPublication, AdapterPublicServerRecord.checked, began,
            AdapterPublicServerRecord.resumeResult]
        · simp only [native, RegistrationNativePlatformServerCompletion.continueResult,
            RegistrationNativePlatformServerCompletion.installWith, began, world_pure, pure_bind]
          change pure (RustM.ok (none : Option (U64 × alloc.vec.Vec U8)), {before with control := rejected}) = pure (RustM.ok none, before)
          rw [control]
      | Ok pending =>
        obtain ⟨publicKey, reparsed⟩ := AdapterPublicServerCompletionInstall.insertion_parsed self.control initial published pending retained began parsed
        obtain ⟨reply, current, after, actual, installed, material⟩ := install coins view views created credential self before related
          published pending began publicKey reparsed (standard published pending publicKey rfl began reparsed)
        refine ⟨.ok (reply, current), after, ?_, installed, material⟩
        simp only [AdapterPublicServerPublication.afterPublication, AdapterPublicServerRecord.checked, began,
          AdapterPublicServerRecord.resumeResult]
        rw [actual, RustT.run_pure]

end BeaconcryptCore.Refinement.AdapterPublicServerPublicationInstall
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPublicationInstall.native_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPublicationInstall.native_insert
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPublicationInstall.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPublicationInstall.install

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPublicationInstall.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPublicationInstall.publication
