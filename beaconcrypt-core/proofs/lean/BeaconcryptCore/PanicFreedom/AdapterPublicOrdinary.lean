-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicOrdinaryExtraction.Funs
import BeaconcryptCore.PanicFreedom.AdapterNormal
import BeaconcryptCore.PanicFreedom.RecordEffects
import BeaconcryptCore.PanicFreedom.Transport
import BeaconcryptCore.Refinement.FrameCodecDecodeTotality
import BeaconcryptCore.PanicFreedom.AdapterRecordSend
import BeaconcryptCore.PanicFreedom.AdapterRecordReceive
import BeaconcryptCore.PanicFreedom.AdapterPublicTrivial

/-! A public ratchet is usable exactly when its synchronous kernel slot is populated. Taking the kernel temporarily empties that slot; every normal success or rejection restores a populated slot. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary
open Refinement AdapterNormal beaconcrypt_public_wrapper

def Populated (slot : ratchet.RatchetKernelSlot) : Prop := ∃ kernel, slot.kernel = some kernel
def Empty (slot : ratchet.RatchetKernelSlot) : Prop := slot.kernel = none
def ValidManager (manager : ratchet.RatchetManager) : Prop := Populated manager.refined
def ValidOptionalManager (manager : core.option.Option ratchet.RatchetManager) : Prop :=
  ∀ value, manager = some value → ValidManager value

def ValidBeacon [PublicWrapperPlatform.Material] [AdapterInitEdPrimitive.Operations]
    (self : beacon.Beacon) : Prop :=
  match self.state with
  | .Established _ _ manager => ValidManager manager
  | _ => True

theorem frame_len_total (length : Usize) (sequence sender : U64) :
    ∃ result, beaconcrypt_public_ordinary.wire.frame_len length sequence sender = ok result :=
  Transport.protected_frame_len_total length sequence sender

theorem status_send_sequence_total (status : beaconcrypt_public_ordinary.ratchet.RatchetStatus) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.RatchetStatus.impl.send_sequence status = ok result := ⟨_, rfl⟩

theorem slot_take_total (slot : ratchet.RatchetKernelSlot) (valid : Populated slot) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.take slot = ok result := by
  rcases slot with ⟨contents⟩
  obtain ⟨kernel, same⟩ := valid
  change contents = some kernel at same
  subst contents
  exact ⟨_, rfl⟩

theorem slot_deref_total (slot : ratchet.RatchetKernelSlot) (valid : Populated slot) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.Insts.CoreOpsDerefDerefConcreteRatchetKernel.deref slot = ok result := by
  rcases slot with ⟨contents⟩
  obtain ⟨kernel, same⟩ := valid
  change contents = some kernel at same
  subst contents
  exact ⟨kernel, rfl⟩

theorem slot_put_total (slot : ratchet.RatchetKernelSlot) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (valid : Empty slot) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.put slot kernel = ok result := by
  rcases slot with ⟨contents⟩
  change contents = none at valid
  subst contents
  exact ⟨⟨some kernel⟩, rfl⟩

theorem slot_roundtrip (kernel changed : ratchet.concrete.ConcreteRatchetKernel) :
    (do
      let (_, empty) ← beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.take ⟨some kernel⟩
      beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.put empty changed) = ok ⟨some changed⟩ := rfl

theorem status_total (manager : ratchet.RatchetManager) (valid : ValidManager manager) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.RatchetManager.status manager = ok result := by
  rcases manager with ⟨slot⟩
  rcases slot with ⟨contents⟩
  obtain ⟨kernel, same⟩ := valid
  change contents = some kernel at same
  subst contents
  exact ⟨_, rfl⟩

theorem send_sequence_total (manager : ratchet.RatchetManager) (valid : ValidManager manager) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.RatchetManager.send_sequence manager = ok result := by
  obtain ⟨kernel, returned⟩ := slot_deref_total manager.refined valid
  exact ⟨kernel.refined.control.send_sequence, by
    simp only [beaconcrypt_public_ordinary.ratchet.RatchetManager.send_sequence, returned, bind_tc_ok]
    rfl⟩

private theorem status_some (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary.ratchet.RatchetManager.status ⟨⟨some kernel⟩⟩ =
      ok (⟨kernel.refined.control.send_sequence, kernel.refined.control.receive_sequence,
        kernel.refined.control.receive_cache.len⟩ : beaconcrypt_public_ordinary.ratchet.RatchetStatus) := rfl
private theorem take_some (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.take ⟨some kernel⟩ = ok (kernel, ⟨none⟩) := rfl
private theorem put_empty (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_ordinary.ratchet.RatchetKernelSlot.put ⟨none⟩ kernel = ok ⟨some kernel⟩ := rfl

private theorem increment_total (sequence : U64) : Normal (core.num.U64.checked_add sequence 1#u64) := by
  simp only [core.num.U64.checked_add, core.num.U64.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_u64, bind_tc_ok]
  cases UScalar.overflowing_add sequence 1#u64 with
  | mk next overflow => cases overflow <;> exact normal_ok _

section Send
variable [beaconcrypt_record_send.ratchet.Operations]

theorem encrypt_with_ratchet_preserves (contracts : AdapterRecordSend.Contracts)
    (bytes : Slice U8) (target sender : U64) (associatedData : Array U8 151#usize)
    (manager : ratchet.RatchetManager) (frameEncoding : Bool) (valid : ValidManager manager) :
    Ensures (beaconcrypt_public_ordinary.ratchet.encrypt_with_ratchet bytes target sender associatedData manager frameEncoding)
      (fun result => ValidManager result.2) := by
  rcases manager with ⟨⟨contents⟩⟩
  obtain ⟨kernel, same⟩ := valid
  change contents = some kernel at same
  subst contents
  unfold beaconcrypt_public_ordinary.ratchet.encrypt_with_ratchet
  simp only [status_some, take_some, beaconcrypt_public_ordinary.ratchet.RatchetStatus.impl.send_sequence,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, bind_tc_ok]
  repeat'
    try simp only [put_empty, bind_tc_ok]
    first
      | (solve | simp_all)
      | exact normal_ok _
      | exact increment_total _
      | exact Transport.protected_frame_len_total _ _ _
      | exact AdapterRecordSend.execute_record_send_total contracts _ _
      | (apply ensures_ok; exact ⟨_, rfl⟩)
      | (intro value)
      | (split)
      | apply ensures_bind_at

theorem encrypt_with_ratchet_total (contracts : AdapterRecordSend.Contracts)
    (bytes : Slice U8) (target sender : U64) (associatedData : Array U8 151#usize)
    (manager : ratchet.RatchetManager) (frameEncoding : Bool) (valid : ValidManager manager) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.encrypt_with_ratchet bytes target sender associatedData manager frameEncoding = ok result :=
  ensures_normal (encrypt_with_ratchet_preserves contracts bytes target sender associatedData manager frameEncoding valid)

theorem encrypt_message_with_ratchet_preserves (contracts : AdapterRecordSend.Contracts)
    (bytes : Slice U8) (target sender : U64) (associatedData : Array U8 151#usize)
    (manager : ratchet.RatchetManager) (valid : ValidManager manager) :
    Ensures (beaconcrypt_public_ordinary.ratchet.encrypt_message_with_ratchet bytes target sender associatedData manager)
      (fun result => ValidManager result.2) :=
  encrypt_with_ratchet_preserves contracts bytes target sender associatedData manager true valid

theorem encrypt_message_with_ratchet_total (contracts : AdapterRecordSend.Contracts)
    (bytes : Slice U8) (target sender : U64) (associatedData : Array U8 151#usize)
    (manager : ratchet.RatchetManager) (valid : ValidManager manager) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.encrypt_message_with_ratchet bytes target sender associatedData manager = ok result :=
  ensures_normal (encrypt_message_with_ratchet_preserves contracts bytes target sender associatedData manager valid)

variable [PublicWrapperPlatform.Material] [AdapterInitEdPrimitive.Operations]

theorem beacon_encrypt_message_preserves (contracts : AdapterRecordSend.Contracts)
    (self : beacon.Beacon) (bytes : Slice U8) (valid : ValidBeacon self) :
    Ensures (beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message self bytes)
      (fun result => ValidBeacon result.2) := by
  cases state : self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey onetime kem
  | InitSent control prekey onetime kem | Aborted control =>
    exact ⟨(none, self), by simp only [beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message, state], valid⟩
  | Established control binding manager =>
    have managerValid : ValidManager manager := by simpa only [ValidBeacon, state] using valid
    obtain ⟨⟨sealed, changed⟩, sent, changedValid⟩ := encrypt_message_with_ratchet_preserves contracts bytes
      control.server_binding.identity_key_id self.identity_key_kid binding.associated_data manager managerValid
    refine ⟨(sealed, { self with state := .Established control binding changed }), ?_, changedValid⟩
    simp only [beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message, state,
      pqxdh.BeaconEstablished.server_key_id, AdapterPublicOrdinaryPlatform.associatedData, bind_tc_ok, sent]
    rfl

theorem beacon_encrypt_message_total (contracts : AdapterRecordSend.Contracts)
    (self : beacon.Beacon) (bytes : Slice U8) (valid : ValidBeacon self) :
    ∃ result, beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message self bytes = ok result :=
  ensures_normal (beacon_encrypt_message_preserves contracts self bytes valid)

end Send

section Receive
variable [beaconcrypt.ratchet.Operations]

omit [beaconcrypt.ratchet.Operations] in
theorem decode_crypto_frame_total (bytes : Slice U8) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.decode_crypto_frame bytes = ok result :=
  FrameCodecDecodeTotality.decode_total bytes

omit [beaconcrypt.ratchet.Operations] in
theorem encrypted_frame_sender_total (bytes : Slice U8) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.encrypted_frame_sender bytes = ok result := by
  obtain ⟨frame, decoded⟩ := decode_crypto_frame_total bytes
  unfold beaconcrypt_public_ordinary.ratchet.encrypted_frame_sender
  rw [decoded, bind_tc_ok]
  cases frame <;> exact ⟨_, rfl⟩

theorem decrypt_payload_with_ratchet_preserves (contracts : AdapterRecordReceive.Contracts)
    (bytes : Slice U8) (sequence sender : U64) (associatedData : Array U8 151#usize)
    (manager : ratchet.RatchetManager) (valid : ValidManager manager) :
    Ensures (beaconcrypt_public_ordinary.ratchet.decrypt_payload_with_ratchet bytes sequence sender associatedData manager)
      (fun result => ValidManager result.2) := by
  rcases manager with ⟨⟨contents⟩⟩
  obtain ⟨kernel, same⟩ := valid
  change contents = some kernel at same
  subst contents
  obtain ⟨effect, started⟩ := RecordEffects.begin_record_receive_total kernel sequence bytes associatedData sender
  obtain ⟨⟨changed, opened⟩, received⟩ := AdapterRecordReceive.execute_record_receive_total contracts effect
  refine ⟨(opened, ⟨⟨some changed⟩⟩), ?_, ⟨changed, rfl⟩⟩
  simp only [beaconcrypt_public_ordinary.ratchet.decrypt_payload_with_ratchet, take_some, bind_tc_ok]
  dsimp! only
  simp only [started, received, bind_tc_ok]
  rfl

theorem decrypt_payload_with_ratchet_total (contracts : AdapterRecordReceive.Contracts)
    (bytes : Slice U8) (sequence sender : U64) (associatedData : Array U8 151#usize)
    (manager : ratchet.RatchetManager) (valid : ValidManager manager) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.decrypt_payload_with_ratchet bytes sequence sender associatedData manager = ok result :=
  ensures_normal (decrypt_payload_with_ratchet_preserves contracts bytes sequence sender associatedData manager valid)

theorem decrypt_message_with_ratchet_preserves (contracts : AdapterRecordReceive.Contracts)
    (bytes : Slice U8) (sender : U64) (associatedData : Array U8 151#usize)
    (manager : ratchet.RatchetManager) (valid : ValidManager manager) :
    Ensures (beaconcrypt_public_ordinary.ratchet.decrypt_message_with_ratchet bytes sender associatedData manager)
      (fun result => ValidManager result.2) := by
  unfold beaconcrypt_public_ordinary.ratchet.decrypt_message_with_ratchet
  simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
  repeat'
    try simp only [bind_tc_ok]
    first
      | (solve | simp_all)
      | exact decode_crypto_frame_total _
      | exact Transport.admit_frame_total _ _ _ _
      | exact decrypt_payload_with_ratchet_preserves contracts _ _ _ _ _ valid
      | exact normal_ok _
      | (intro value)
      | (split)
      | apply ensures_bind_at

theorem decrypt_message_with_ratchet_total (contracts : AdapterRecordReceive.Contracts)
    (bytes : Slice U8) (sender : U64) (associatedData : Array U8 151#usize)
    (manager : ratchet.RatchetManager) (valid : ValidManager manager) :
    ∃ result, beaconcrypt_public_ordinary.ratchet.decrypt_message_with_ratchet bytes sender associatedData manager = ok result :=
  ensures_normal (decrypt_message_with_ratchet_preserves contracts bytes sender associatedData manager valid)

variable [PublicWrapperPlatform.Material] [AdapterInitEdPrimitive.Operations]

theorem beacon_decrypt_message_preserves (contracts : AdapterRecordReceive.Contracts)
    (self : beacon.Beacon) (bytes : Slice U8) (valid : ValidBeacon self) :
    Ensures (beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message self bytes)
      (fun result => ValidBeacon result.2) := by
  cases state : self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey onetime kem
  | InitSent control prekey onetime kem | Aborted control =>
    exact ⟨(none, self), by simp only [beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message, state], valid⟩
  | Established control binding manager =>
    have managerValid : ValidManager manager := by simpa only [ValidBeacon, state] using valid
    obtain ⟨⟨opened, changed⟩, received, changedValid⟩ := decrypt_message_with_ratchet_preserves contracts bytes
      control.server_binding.identity_key_id binding.associated_data manager managerValid
    refine ⟨(opened, { self with state := .Established control binding changed }), ?_, changedValid⟩
    simp only [beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message, state,
      pqxdh.BeaconEstablished.server_key_id, AdapterPublicOrdinaryPlatform.associatedData, bind_tc_ok, received]
    rfl

theorem beacon_decrypt_message_total (contracts : AdapterRecordReceive.Contracts)
    (self : beacon.Beacon) (bytes : Slice U8) (valid : ValidBeacon self) :
    ∃ result, beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message self bytes = ok result :=
  ensures_normal (beacon_decrypt_message_preserves contracts self bytes valid)

end Receive

section Maps
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [lookup : AdapterPublicOrdinaryPlatform.LookupOperations]

abbrev Remote := shared.EstablishedRemote beaconcrypt_crypto.crypto_sign.PublicKey
abbrev PeerMap := hashbrown.map.HashMap U64 Remote collections.KeyedHasher hashbrown.alloc.inner.Global

def mapGet (map : PeerMap) (key : U64) : RustM (core.option.Option Remote) :=
  hashbrown.map.HashMap.get core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_ordinary.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator core.U64.Insts.CoreHashHash
    (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq (core.borrow.Borrow.Blanket U64)) map key

def mapGetMut (map : PeerMap) (key : U64) :
    RustM (core.option.Option Remote × (core.option.Option Remote → PeerMap)) :=
  hashbrown.map.HashMap.get_mut core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_ordinary.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator core.U64.Insts.CoreHashHash
    (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq (core.borrow.Borrow.Blanket U64)) map key

def ValidRemote (remote : Remote) : Prop := ValidManager remote.peer.ratchet
def ValidOptionalRemote (remote : core.option.Option Remote) : Prop :=
  ∀ value, remote = some value → ValidRemote value

/-- A mutable lookup is restored through the same optional borrow shape that it returned. -/
def SameOptionShape {T : Type} (selected replacement : core.option.Option T) : Prop :=
  match selected, replacement with
  | none, none | some _, some _ => True
  | _, _ => False

/-- Every remote visible through the selected map interpretation has a populated synchronous slot. -/
def ValidMap (map : PeerMap) : Prop :=
  ∀ key remote, mapGet map key = ok (some remote) → ValidRemote remote

def ValidServer (self : server.Server) : Prop := ValidMap self.known_ids

/-- Mutable lookup returns a valid selection and retains map validity for valid replacements of the actual borrow shape. -/
structure LookupContracts : Prop where
  get : ∀ map key, Normal (mapGet map key)
  getMut : ∀ map key, ValidMap map →
    ∃ result, mapGetMut map key = ok result ∧ ValidOptionalRemote result.1 ∧
      ∀ replacement, SameOptionShape result.1 replacement →
        ValidOptionalRemote replacement → ValidMap (result.2 replacement)

theorem associated_data_total (contracts : LookupContracts) (self : server.Server) (key : U64) :
    ∃ result, beaconcrypt_public_ordinary.server.Server.associated_data self key = ok result := by
  obtain ⟨selected, returned⟩ := contracts.get self.known_ids key
  unfold beaconcrypt_public_ordinary.server.Server.associated_data
  change ∃ result, (do
    let selected ← mapGet self.known_ids key
    let branch ← core.option.Option.Insts.CoreOpsTry_traitTry.branch selected
    match branch with
    | .Continue remote => do
      let binding ← beaconcrypt_public_ordinary.shared.EstablishedRemote.binding
        beaconcrypt_public_ordinary.beaconcrypt_crypto.crypto_sign.PublicKey.Insts.BeaconcryptSharedSignaturePk remote
      let bytes ← AdapterPublicOrdinaryPlatform.associatedData binding
      ok (some bytes)
    | .Break residual => core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual _ residual) = ok result
  rw [returned, bind_tc_ok]
  cases selected <;> exact ⟨_, rfl⟩

theorem ratchet_manager_mut_preserves (contracts : LookupContracts)
    (self : server.Server) (key : U64) (valid : ValidServer self) :
    Ensures (beaconcrypt_public_ordinary.server.Server.ratchet_manager_mut self key)
      (fun result => ValidOptionalManager result.1 ∧
        ∀ replacement, ValidOptionalManager replacement → ValidServer (result.2 replacement)) := by
  obtain ⟨⟨selected, back⟩, returned, selectedValid, restores⟩ := contracts.getMut self.known_ids key valid
  unfold beaconcrypt_public_ordinary.server.Server.ratchet_manager_mut
  change Ensures (mapGetMut self.known_ids key >>= _) _
  rw [returned, bind_tc_ok]
  cases selected with
  | none =>
    refine ⟨_, rfl, ?_, ?_⟩
    · intro manager impossible
      cases impossible
    · intro replacement _
      exact restores none trivial (by intro remote impossible; cases impossible)
  | some remote =>
    refine ⟨_, rfl, ?_, ?_⟩
    · intro manager same
      cases same
      exact selectedValid remote rfl
    · intro replacement replacementValid
      apply restores
      · trivial
      intro updated same
      cases same
      cases replacement with
      | none => exact selectedValid remote rfl
      | some manager => exact replacementValid manager rfl

theorem ratchet_manager_mut_total (contracts : LookupContracts)
    (self : server.Server) (key : U64) (valid : ValidServer self) :
    ∃ result, beaconcrypt_public_ordinary.server.Server.ratchet_manager_mut self key = ok result :=
  ensures_normal (ratchet_manager_mut_preserves contracts self key valid)

variable [beaconcrypt_record_send.ratchet.Operations]

theorem server_encrypt_message_preserves (contracts : AdapterRecordSend.Contracts)
    (lookups : LookupContracts) (self : server.Server) (bytes : Slice U8) (key : U64)
    (valid : ValidServer self) :
    Ensures (beaconcrypt_public_ordinary.server.Server.encrypt_message self bytes key)
      (fun result => ValidServer result.2) := by
  obtain ⟨associated, associatedRun⟩ := associated_data_total lookups self key
  unfold beaconcrypt_public_ordinary.server.Server.encrypt_message
  rw [associatedRun, bind_tc_ok]
  cases associated with
  | none => exact ⟨(none, self), rfl, valid⟩
  | some associated =>
    obtain ⟨sender, senderRun⟩ := AdapterPublicTrivial.ordinary_server_identity_key_kid_total self
    obtain ⟨⟨selected, back⟩, borrowed, selectedValid, restores⟩ := ratchet_manager_mut_preserves lookups self key valid
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok, senderRun, borrowed]
    cases selected with
    | none =>
      exact ⟨(none, back none), rfl, restores none (by intro manager impossible; cases impossible)⟩
    | some manager =>
      obtain ⟨⟨sealed, changed⟩, sent, changedValid⟩ := encrypt_message_with_ratchet_preserves contracts
        bytes key sender associated manager (selectedValid manager rfl)
      refine ⟨(sealed, back (some changed)), ?_, restores (some changed) ?_⟩
      · dsimp! only
        rw [sent]
        rfl
      · intro manager same
        cases same
        exact changedValid

theorem server_encrypt_message_total (contracts : AdapterRecordSend.Contracts)
    (lookups : LookupContracts) (self : server.Server) (bytes : Slice U8) (key : U64)
    (valid : ValidServer self) :
    ∃ result, beaconcrypt_public_ordinary.server.Server.encrypt_message self bytes key = ok result :=
  ensures_normal (server_encrypt_message_preserves contracts lookups self bytes key valid)

variable [beaconcrypt.ratchet.Operations]

omit [beaconcrypt_record_send.ratchet.Operations] in
theorem server_decrypt_message_transition_preserves (contracts : AdapterRecordReceive.Contracts)
    (lookups : LookupContracts) (self : server.Server) (bytes : Slice U8) (valid : ValidServer self) :
    Ensures (beaconcrypt_public_ordinary.server.Server.decrypt_message_transition self bytes)
      (fun result => ValidServer result.2) := by
  obtain ⟨sender, senderRun⟩ := encrypted_frame_sender_total bytes
  unfold beaconcrypt_public_ordinary.server.Server.decrypt_message_transition
  rw [senderRun, bind_tc_ok]
  cases sender with
  | none => exact ⟨(.Rejected, self), rfl, valid⟩
  | some sender =>
    dsimp! only
    obtain ⟨associated, associatedRun⟩ := associated_data_total lookups self sender
    rw [associatedRun, bind_tc_ok]
    cases associated with
    | none => exact ⟨(.Rejected, self), rfl, valid⟩
    | some associated =>
      dsimp! only
      obtain ⟨⟨selected, back⟩, borrowed, selectedValid, restores⟩ := ratchet_manager_mut_preserves lookups self sender valid
      rw [borrowed, bind_tc_ok]
      cases selected with
      | none => exact ⟨(.Rejected, back none), rfl, restores none (by intro manager impossible; cases impossible)⟩
      | some manager =>
        obtain ⟨⟨opened, changed⟩, received, changedValid⟩ := decrypt_message_with_ratchet_preserves contracts bytes sender
          associated manager (selectedValid manager rfl)
        refine ⟨((opened.elim .Rejected .Accepted), back (some changed)), ?_,
          restores (some changed) ?_⟩
        · dsimp! only
          rw [received, bind_tc_ok]
          cases opened <;> rfl
        · intro manager same
          cases same
          exact changedValid

omit [beaconcrypt_record_send.ratchet.Operations] in
theorem server_decrypt_message_transition_total (contracts : AdapterRecordReceive.Contracts)
    (lookups : LookupContracts) (self : server.Server) (bytes : Slice U8) (valid : ValidServer self) :
    ∃ result, beaconcrypt_public_ordinary.server.Server.decrypt_message_transition self bytes = ok result :=
  ensures_normal (server_decrypt_message_transition_preserves contracts lookups self bytes valid)

omit [beaconcrypt_record_send.ratchet.Operations] in
theorem server_decrypt_message_preserves (contracts : AdapterRecordReceive.Contracts)
    (lookups : LookupContracts) (self : server.Server) (bytes : Slice U8) (valid : ValidServer self) :
    Ensures (beaconcrypt_public_ordinary.server.Server.decrypt_message self bytes)
      (fun result => ValidServer result.2) := by
  obtain ⟨⟨transition, changed⟩, received, changedValid⟩ := server_decrypt_message_transition_preserves contracts lookups self bytes valid
  unfold beaconcrypt_public_ordinary.server.Server.decrypt_message
  rw [received, bind_tc_ok]
  cases transition <;> exact ⟨_, rfl, changedValid⟩

omit [beaconcrypt_record_send.ratchet.Operations] in
theorem server_decrypt_message_total (contracts : AdapterRecordReceive.Contracts)
    (lookups : LookupContracts) (self : server.Server) (bytes : Slice U8) (valid : ValidServer self) :
    ∃ result, beaconcrypt_public_ordinary.server.Server.decrypt_message self bytes = ok result :=
  ensures_normal (server_decrypt_message_preserves contracts lookups self bytes valid)

end Maps

end BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary
