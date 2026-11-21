-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterSelectedSendPrivacy
import BeaconcryptCore.Computational.RawCtxSelectedFamilyLiveCompiler

/-! The literal selected Server and Beacon sends retain their complete optional frontend state in the two-plaintext relation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhFirstRecordConfidentiality
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxGenericRoleStorage
open RawCtxSelectedOwnerCompiler (Kernel)
variable {M P I D K : Type} {S B : Nat}
variable (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder)

include equal

/-- The complete owner send keeps the original empty-input gate, optional nonce refusal, writer result and advanced owner. -/
theorem owner_twin (sender : Std.U64) (before : RawCtxChainOwner.State Kernel M)
    (selected : RawCtxSelectedPendingCut.requestAddress before.kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    Twin left right (fun a b => a = b) (fun _ => False) (fun _ => False)
      (RawCtxSelectedOwnerCompiler.owner source writer prior (some parent) target nonce next read sender (.inl left) before)
      (RawCtxSelectedOwnerCompiler.owner source writer prior (some parent) target nonce next read sender (.inl right) before) := by
  rw [RawCtxSelectedOwnerCompiler.send_cases, RawCtxSelectedOwnerCompiler.send_cases]
  have sameEmpty : right.isEmpty = left.isEmpty := by
    cases left <;> cases right <;> simp_all
  rw [sameEmpty]
  split_ifs with empty
  case neg =>
    exact twin_map left right
      (PqxdhLaterSelectedSendPrivacy.send_twin left right source writer prior parent target nonce next before.kernel
        ⟨left, before.expectedSender, sender, before.associatedData⟩ selected separate) _ _
      (fun _ _ same => congrArg _ same) (fun _ impossible => impossible.elim) (fun _ impossible => impossible.elim)
  case pos => exact Twin.pure rfl

/-- The literal Server dispatch keeps its actual peer and associated-data lookups before the same complete selected send. Missing peers and unavailable AD remain ordinary source rejection. -/
theorem server_twin (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (kid : Std.U64) (before : ServerState Kernel M P)
    (selected : ∀ peer, before.server.peers kid = some peer →
      RawCtxSelectedPendingCut.requestAddress peer.kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    Twin left right (fun a b => a = b) (fun _ => False) (fun _ => False)
      (RawCtxSelectedRoleCompiler.server source writer prior (some parent) target nonce next sender route read (.inl (left, kid)) before)
      (RawCtxSelectedRoleCompiler.server source writer prior (some parent) target nonce next sender route read (.inl (right, kid)) before) := by
  rw [RawCtxSelectedRoleCompiler.server_send_cases, RawCtxSelectedRoleCompiler.server_send_cases]
  cases associated : RawCtxGenericServer.peerAssociatedData before.server kid
  case some ad =>
    cases found : before.server.peers kid
    case some peer =>
      exact twin_map left right
        (owner_twin left right equal source writer prior parent target nonce next read (sender before.server.metadata)
          (RawCtxGenericServer.selectedOwner kid ad peer before.rawAttempts) (selected peer found) separate) _ _
        (fun _ _ same => congrArg _ same) (fun _ impossible => impossible.elim) (fun _ impossible => impossible.elim)
    case none => exact Twin.pure rfl
  case none => exact Twin.pure rfl

/-- The literal Beacon phase dispatch retains inactive rejection and reinstalls the complete established owner after the selected send. -/
theorem beacon_twin (before : BeaconState Kernel I D K)
    (selected : ∀ control ad kernel, before.beacon.phase = .established control ad kernel →
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    Twin left right (fun a b => a = b) (fun _ => False) (fun _ => False)
      (RawCtxSelectedRoleCompiler.beacon source writer prior (some parent) target nonce next read (.inl left) before)
      (RawCtxSelectedRoleCompiler.beacon source writer prior (some parent) target nonce next read (.inl right) before) := by
  rw [RawCtxSelectedRoleCompiler.beacon_cases, RawCtxSelectedRoleCompiler.beacon_cases]
  cases phase : before.beacon.phase
  case established control ad kernel =>
    exact twin_map left right
      (owner_twin left right equal source writer prior parent target nonce next read before.beacon.identityKeyId
        (RawCtxGenericBeacon.selected before control ad kernel) (selected control ad kernel phase) separate) _ _
      (fun _ _ same => congrArg _ same) (fun _ impossible => impossible.elim) (fun _ impossible => impossible.elim)
  all_goals exact Twin.pure rfl

omit equal in
/-- One literal existing LIVE send, with its full roles and disclosure history. The enclosing source query is unchanged. -/
noncomputable def liveSend (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes)
    (before : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec
      (Option (Option RawCtxSourceSend.Encrypted) × RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B) :=
  match owner with
  | .server index peer =>
      ((RawCtxSelectedFamilyLiveCompiler.impl source writer prior (some parent) target nonce next sender route read
        (.inl (.inl ⟨index, .inl (plaintext, peer)⟩))).run).run before
  | .beacon index =>
      ((RawCtxSelectedFamilyLiveCompiler.impl source writer prior (some parent) target nonce next sender route read
        (.inl (.inr (.inl ⟨index, .inl plaintext⟩)))).run).run before

/-- The complete actual indexed LIVE send is twin for either owner and any send counter. Its target-input condition concerns the request state; outer refusal, ordinary rejection, writer failure and full history tick remain distinct. -/
theorem live_twin (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (owner : RawCtxProtocolReveals.Owner S B)
    (before : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (selected : ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1 = some kernel →
      RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    Twin left right (fun a b => a = b) (fun _ => False) (fun _ => False)
      (liveSend source writer prior parent target nonce next read sender route owner left before)
      (liveSend source writer prior parent target nonce next read sender route owner right before) := by
  cases owner
  all_goals simp only [liveSend, RawCtxSelectedFamilyLiveCompiler.impl, OptionT.run_mk, StateT.run,
    RawCtxSelectedFamilyCompiler.family_cases, Functor.map_map]
  case server index kid =>
    refine twin_map left right
      (server_twin left right equal source writer prior parent target nonce next read sender route kid (before.1.1 index)
        ?_ separate) _ _ (fun _ _ same => by cases same; rfl)
      (fun _ impossible => impossible.elim) (fun _ impossible => impossible.elim)
    exact fun peer found => selected peer.kernel (by simp only [RawCtxGenericRoleFamily.selectedKernel, found, Option.map_some])
  case beacon index =>
    refine twin_map left right
      (beacon_twin left right equal source writer prior parent target nonce next read (before.1.2 index) ?_ separate) _ _
      (fun _ _ same => by cases same; rfl) (fun _ impossible => impossible.elim) (fun _ impossible => impossible.elim)
    exact fun control ad kernel phase => selected kernel (by simp only [RawCtxGenericRoleFamily.selectedKernel, phase])

end BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy.owner_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy.owner_twin
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy.server_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy.server_twin
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy.beacon_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy.beacon_twin
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy.live_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterFamilySendPrivacy.live_twin
