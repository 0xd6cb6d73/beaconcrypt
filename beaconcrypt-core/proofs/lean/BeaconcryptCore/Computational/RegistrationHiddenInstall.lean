-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBoundPublication
import BeaconcryptCore.Refinement.PeerOwnership

/-! The actual source peer-insertion controller checks the live allocation counter after dynamic response publication, retains its full authenticated binding, and asks the record World to install a hidden reference. The public compiler never reads or returns the generated seed or concrete kernel. A failed encoding/signature never reaches this controller, and a refused World insertion returns the native entry control. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationHiddenInstall
open PqxdhRecordLiftInterface
variable {n : Nat} {Encoded : Type}

abbrev Result (Encoded : Type) := core.result.Result (peer.PublishedPeer Encoded) pqxdh.ServerState

private def request (capability : Capability n) : OracleComp (EnvEffects n) ((CapabilitySpec n).Range capability) :=
  (EnvEffects n).query (.inr capability)

private def continueWith {Input : Type} (action : RustM Input)
    (next : Input → OracleComp (EnvEffects n) (RustM (Result Encoded))) :
    OracleComp (EnvEffects n) (RustM (Result Encoded)) :=
  match action with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

private def continueResult {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp (EnvEffects n) (RustM (Result Encoded))) :
    OracleComp (EnvEffects n) (RustM (Result Encoded)) :=
  match action with
  | .ok (.Ok value) => next value
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- Native insertion transfers the original signed publication's binding and checks the live allocation counter before issuing one hidden-reference installation. -/
def install (control : pqxdh.ServerState) (slot : Slot n)
    (published : registration.PublishedServerResponse Encoded) : OracleComp (EnvEffects n) (RustM (Result Encoded)) :=
  continueResult (peer.begin_peer_insert control published) fun pending =>
    continueWith pending.request fun keyId =>
      continueWith pending.into_parts fun parts => do
        let inserted ← request
          (.installServer keyId (PeerBinding.ofSession parts.1.binding) (.hidden slot))
        pure (parts.2.finish inserted)

/-- Only the actual successful response publication reaches peer insertion. -/
def after (control : pqxdh.ServerState) (slot : Slot n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    OracleComp (EnvEffects n) (RustM (Result Encoded)) :=
  continueResult published (install control slot)

/-- Actual peer setup, selected binding/handle and native finish are independent of the concrete kernel when the installation uses its protected hidden reference. -/
theorem install_map (kernel : ConcreteRatchetKernel) (control : pqxdh.ServerState) (slot : Slot n)
    (published : registration.PublishedServerResponse Encoded) :
    install control slot (RegistrationPublicationKernelErasure.published kernel published) =
      install control slot published := by
  obtain ⟨next, nextRun⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok control
  cases next
  all_goals simp only [install, peer.begin_peer_insert, nextRun,
    RegistrationPublicationKernelErasure.published, registration.PublishedServerResponse.into_parts,
    pqxdh.ServerState.impl.last_key_id, peer.Peer.from_trusted_parts, bind_tc_ok]
  all_goals dsimp! only
  all_goals try split
  all_goals rfl

/-- Every publication failure stays a failure; successful native peer insertion retains exactly its public output while the World resolves the private kernel. -/
theorem after_map (kernel : ConcreteRatchetKernel) (control : pqxdh.ServerState) (slot : Slot n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    after control slot (RegistrationPublicationKernelErasure.result kernel published) = after control slot published := by
  cases published with
  | fail error => rfl
  | div => rfl
  | ok value =>
    cases value with
    | Err previous => rfl
    | Ok completed => exact install_map kernel control slot completed

abbrev Spec (n : Nat) := RegistrationBoundPublication.Spec + EnvEffects n

def publicationLift : QueryImpl RegistrationBoundPublication.Spec (OracleComp (Spec n)) :=
  fun query => (Spec n).query (.inl query)

def effectLift : QueryImpl (EnvEffects n) (OracleComp (Spec n)) :=
  fun query => (Spec n).query (.inr query)

/-- Actual first-record/sign/encode publication followed by native peer ownership and hidden installation. -/
def stage (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) : OracleComp (Spec n) (RustM (Result Encoded)) := do
  let published ← simulateQ publicationLift (RegistrationBoundPublication.program encode initial output)
  simulateQ effectLift (after control slot published)

/-- The actual native pipeline can be compiled with the public material alone, retaining the private slot reference at installation. All primitive effects, optional failures and actual public results are identical. -/
theorem stage_split (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed) :
    stage encode control slot initial (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      (do let published ← simulateQ publicationLift (RegistrationBoundPublication.thin encode initial material)
          simulateQ effectLift (after control slot published)) := by
  simp only [stage, RegistrationBoundPublication.split, simulateQ_map, bind_map_left, after_map]

/-- The single reached installation request is exactly the binding and source-selected assigned ID owned by the actual native insertion capability. -/
theorem install_native (control : pqxdh.ServerState) (slot : Slot n)
    (published : registration.PublishedServerResponse Encoded) (pending : peer.PeerInsert Encoded)
    (prepared : peer.begin_peer_insert control published = .ok (.Ok pending)) :
    install control slot published = (do
      let inserted ← request
        (.installServer pending.peer.binding.assigned_key_id (PeerBinding.ofSession pending.peer.binding) (.hidden slot))
      pure ((⟨pending.previous, pending.next, pending.peer.binding.assigned_key_id, pending.encoded⟩ :
        peer.PublicationFinish Encoded).finish inserted)) := by
  simp only [install, prepared, continueResult,
    BeaconcryptCore.Refinement.PeerOwnership.peer_insert_request,
    BeaconcryptCore.Refinement.PeerOwnership.peer_insert_parts, continueWith]

/-- A successful actual hidden World installation stores the complete generated kernel and the exact populated native binding AD, and caches the same seed privately. -/
theorem installed_fields (keyId : U64) (binding : PeerBinding) (slot : Slot n)
    (before after : PqxdhRecordLiftWorld.State n)
    (supported : (true, after) ∈ support
      ((PqxdhRecordLiftWorld.installServer keyId binding (.hidden slot)).run before)) :
    ∃ (seed : PqxdhRecordLiftSeed.Seed) (server : PqxdhRecordLiftWorld.Server)
        (peer : RawCtxServerRouting.Peer (Std.Array U8 151#usize)),
      after.server = some server ∧ server.records.server.peers keyId = some peer ∧
      peer.identity = binding.identity ∧ peer.kernel = PqxdhRecordLiftWorld.kernel .server seed ∧
      peer.metadata = binding.associatedArray server.records.server.identity ∧
      after.seeds.1 slot = some seed := by
  obtain ⟨⟨server, present, vacant⟩, unused⟩ :=
    PqxdhRecordLiftWorld.installServer_admitted keyId binding (.hidden slot) before after supported
  simp only [PqxdhRecordLiftWorld.installServer, StateT.run, present, ite_eq_left (And.intro vacant unused),
    bind_pure_comp, support_map] at supported
  obtain ⟨resolved, reached, equal⟩ := supported
  obtain ⟨seed, kernel, cached, _persistent, _used, _server, _owners, _raw, _produced, _cache, _native, _effects⟩ :=
    PqxdhRecordLiftWorld.resolve_hidden_facts .server slot before resolved reached
  have afterEq := (congrArg Prod.snd equal).symm
  dsimp only at afterEq
  subst after
  refine ⟨seed, _, ⟨binding.identity, resolved.1, binding.associatedArray server.records.server.identity⟩,
    rfl, ?_, rfl, kernel, rfl, ?_⟩
  · simp only [Function.update_self]
  · simpa only [PqxdhRecordLiftWorld.markUsed] using cached

/-- When another native role already resolved the same private slot, actual installation uses precisely that persistent seed without a new kernel choice. -/
theorem installed_cached_kernel (keyId : U64) (binding : PeerBinding) (slot : Slot n)
    (seed : PqxdhRecordLiftSeed.Seed) (before after : PqxdhRecordLiftWorld.State n)
    (cached : before.seeds.1 slot = some seed)
    (supported : (true, after) ∈ support
      ((PqxdhRecordLiftWorld.installServer keyId binding (.hidden slot)).run before)) :
    ∃ (server : PqxdhRecordLiftWorld.Server) (peer : RawCtxServerRouting.Peer (Std.Array U8 151#usize)),
      after.server = some server ∧ server.records.server.peers keyId = some peer ∧
      peer.kernel = PqxdhRecordLiftWorld.kernel .server seed ∧
      peer.metadata = binding.associatedArray server.records.server.identity := by
  obtain ⟨found, server, peer, present, stored, _identity, kernel, data, seedCached⟩ :=
    installed_fields keyId binding slot before after supported
  have persistent := PqxdhRecordLiftWorld.installServer_persists keyId binding (.hidden slot) before
    (true, after) supported
  have same := (persistent.1 cached).symm.trans seedCached
  have foundEq : seed = found := Option.some.inj same
  exact ⟨server, peer, present, stored, kernel.trans (congrArg (PqxdhRecordLiftWorld.kernel .server) foundEq.symm), data⟩

end BeaconcryptCore.Computational.RegistrationHiddenInstall

/-- info: 'BeaconcryptCore.Computational.RegistrationHiddenInstall.install_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationHiddenInstall.install_map

/-- info: 'BeaconcryptCore.Computational.RegistrationHiddenInstall.after_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationHiddenInstall.after_map

/-- info: 'BeaconcryptCore.Computational.RegistrationHiddenInstall.stage_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationHiddenInstall.stage_split

/-- info: 'BeaconcryptCore.Computational.RegistrationHiddenInstall.install_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationHiddenInstall.install_native

/-- info: 'BeaconcryptCore.Computational.RegistrationHiddenInstall.installed_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationHiddenInstall.installed_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationHiddenInstall.installed_cached_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationHiddenInstall.installed_cached_kernel
