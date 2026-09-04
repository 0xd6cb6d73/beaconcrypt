import BeaconcryptCore.PanicFreedom.Control
import BeaconcryptCore.Refinement.PqxdhCore

/-! Static sizes, assertions, and role selections return normally on every supported word width. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

namespace BeaconcryptCore.PanicFreedom.Static

@[simp] private theorem add_32_12 :
    (32#usize : Std.Usize) + 12#usize = ok 44#usize :=
  usize_add_eq _ _ _ (by simp)

@[simp] private theorem add_44_153 :
    (44#usize : Std.Usize) + 153#usize = ok 197#usize :=
  usize_add_eq _ _ _ (by simp)

@[simp] private theorem add_197_16 :
    (197#usize : Std.Usize) + 16#usize = ok 213#usize :=
  usize_add_eq _ _ _ (by simp)

@[simp] private theorem mul_2_8 :
    (2#usize : Std.Usize) * 8#usize = ok 16#usize :=
  usize_mul_eq _ _ _ (by simp)

@[simp] private theorem add_213_16 :
    (213#usize : Std.Usize) + 16#usize = ok 229#usize :=
  usize_add_eq _ _ _ (by simp)

@[simp] private theorem mul_32_2 :
    (32#usize : Std.Usize) * 2#usize = ok 64#usize :=
  usize_mul_eq _ _ _ (by simp)

@[simp] private theorem add_32_32 :
    (32#usize : Std.Usize) + 32#usize = ok 64#usize :=
  usize_add_eq _ _ _ (by simp)

@[simp] private theorem add_32_1 :
    (32#usize : Std.Usize) + 1#usize = ok 33#usize :=
  usize_add_eq _ _ _ (by simp)

@[simp] private theorem add_32_2 :
    (32#usize : Std.Usize) + 2#usize = ok 34#usize :=
  usize_add_eq _ _ _ (by simp)

@[simp] private theorem add_1184_1 :
    (1184#usize : Std.Usize) + 1#usize = ok 1185#usize :=
  usize_add_eq _ _ _ (by simp)

@[simp] private theorem mul_4_32 :
    (4#usize : Std.Usize) * 32#usize = ok 128#usize :=
  usize_mul_eq _ _ _ (by simp)

@[simp] private theorem add_32_128 :
    (32#usize : Std.Usize) + 128#usize = ok 160#usize :=
  usize_add_eq _ _ _ (by simp)

@[simp] private theorem add_160_32 :
    (160#usize : Std.Usize) + 32#usize = ok 192#usize :=
  usize_add_eq _ _ _ (by simp)

@[simp] private theorem add_64_12 :
    (64#usize : Std.Usize) + 12#usize = ok 76#usize :=
  usize_add_eq _ _ _ (by simp)

theorem commitment_COMMITMENT_TRANSCRIPT_SIZE_total :
    ∃ result, commitment.COMMITMENT_TRANSCRIPT_SIZE = ok result := by
  simp [commitment.COMMITMENT_TRANSCRIPT_SIZE,
    commitment.AEAD_KEY_SIZE,
    commitment.AEAD_NONCE_SIZE,
    commitment.ASSOCIATED_DATA_SIZE,
    constants.ASSOCIATED_DATA_SIZE,
    commitment.AEAD_TAG_SIZE,
    commitment.ENCODED_U64_SIZE]

theorem commitment_assert_total :
    ∃ result, commitment._ = ok result := by
  simp [commitment._,
    commitment.AEAD_KEY_SIZE]

theorem commitment_assert_1_total :
    ∃ result, commitment.__1 = ok result := by
  simp [commitment.__1,
    commitment.AEAD_NONCE_SIZE]

theorem commitment_assert_2_total :
    ∃ result, commitment.__2 = ok result := by
  simp [commitment.__2,
    commitment.ASSOCIATED_DATA_SIZE,
    constants.ASSOCIATED_DATA_SIZE]

theorem commitment_assert_3_total :
    ∃ result, commitment.__3 = ok result := by
  simp [commitment.__3,
    commitment.AEAD_TAG_SIZE]

theorem commitment_assert_4_total :
    ∃ result, commitment.__4 = ok result := by
  simp [commitment.__4,
    commitment.ENCODED_U64_SIZE]

theorem commitment_assert_5_total :
    ∃ result, commitment.__5 = ok result := by
  simp [commitment.__5,
    commitment.COMMITMENT_TRANSCRIPT_SIZE,
    commitment.AEAD_KEY_SIZE,
    commitment.AEAD_NONCE_SIZE,
    commitment.ASSOCIATED_DATA_SIZE,
    constants.ASSOCIATED_DATA_SIZE,
    commitment.AEAD_TAG_SIZE,
    commitment.ENCODED_U64_SIZE]

theorem pqxdh_BEACON_RATCHETS_total :
    ∃ result, pqxdh.BEACON_RATCHETS = ok result := by
  simp [pqxdh.BEACON_RATCHETS,
    pqxdh.RATCHET_CHAIN_SIZE,
    ratchet.RATCHET_CHAIN_SIZE, lift]

theorem pqxdh_SERVER_RATCHETS_total :
    ∃ result, pqxdh.SERVER_RATCHETS = ok result := by
  simp [pqxdh.SERVER_RATCHETS,
    pqxdh.RATCHET_CHAIN_SIZE,
    ratchet.RATCHET_CHAIN_SIZE, lift]

theorem pqxdh_INITIAL_RATCHET_KDF_OUTPUT_SIZE_total :
    ∃ result, pqxdh.INITIAL_RATCHET_KDF_OUTPUT_SIZE = ok result := by
  simp [pqxdh.INITIAL_RATCHET_KDF_OUTPUT_SIZE,
    pqxdh.RATCHET_CHAIN_SIZE,
    ratchet.RATCHET_CHAIN_SIZE]

theorem pqxdh_assert_total :
    ∃ result, pqxdh._ = ok result := by
  simp [pqxdh._,
    pqxdh.INITIAL_RATCHET_KDF_OUTPUT_SIZE,
    pqxdh.RATCHET_CHAIN_SIZE,
    ratchet.RATCHET_CHAIN_SIZE]

theorem pqxdh_REGISTRATION_ID_SIZE_total :
    ∃ result, pqxdh.REGISTRATION_ID_SIZE = ok result := by
  simp [pqxdh.REGISTRATION_ID_SIZE,
    pqxdh.SIGN_PUBLIC_KEY_SIZE,
    pqxdh.X25519_PUBLIC_KEY_SIZE]

theorem pqxdh_ENCODED_SIGN_PUBLIC_KEY_SIZE_total :
    ∃ result, pqxdh.ENCODED_SIGN_PUBLIC_KEY_SIZE = ok result := by
  simp [pqxdh.ENCODED_SIGN_PUBLIC_KEY_SIZE,
    pqxdh.SIGN_PUBLIC_KEY_SIZE]

theorem pqxdh_ENCODED_X25519_PUBLIC_KEY_SIZE_total :
    ∃ result, pqxdh.ENCODED_X25519_PUBLIC_KEY_SIZE = ok result := by
  simp [pqxdh.ENCODED_X25519_PUBLIC_KEY_SIZE,
    pqxdh.X25519_PUBLIC_KEY_SIZE]

theorem pqxdh_ENCODED_MLKEM768_PUBLIC_KEY_SIZE_total :
    ∃ result, pqxdh.ENCODED_MLKEM768_PUBLIC_KEY_SIZE = ok result := by
  simp [pqxdh.ENCODED_MLKEM768_PUBLIC_KEY_SIZE,
    pqxdh.MLKEM768_PUBLIC_KEY_SIZE]

theorem pqxdh_ROOT_KEY_INPUT_SIZE_total :
    ∃ result, pqxdh.ROOT_KEY_INPUT_SIZE = ok result := by
  simp [pqxdh.ROOT_KEY_INPUT_SIZE,
    pqxdh.DH_SECRET_SIZE,
    pqxdh.PQXDH_PADDING_SIZE,
    pqxdh.SHARED_SECRET_SIZE]

theorem pqxdh_assert_1_total :
    ∃ result, pqxdh.__1 = ok result := by
  simp [pqxdh.__1,
    pqxdh.SIGN_PUBLIC_KEY_SIZE]

theorem pqxdh_assert_2_total :
    ∃ result, pqxdh.__2 = ok result := by
  simp [pqxdh.__2,
    pqxdh.X25519_PUBLIC_KEY_SIZE]

theorem pqxdh_assert_3_total :
    ∃ result, pqxdh.__3 = ok result := by
  simp [pqxdh.__3,
    pqxdh.MLKEM768_PUBLIC_KEY_SIZE]

theorem pqxdh_assert_4_total :
    ∃ result, pqxdh.__4 = ok result := by
  simp [pqxdh.__4,
    pqxdh.DH_SECRET_SIZE]

theorem pqxdh_assert_5_total :
    ∃ result, pqxdh.__5 = ok result := by
  simp [pqxdh.__5,
    pqxdh.SHARED_SECRET_SIZE]

theorem pqxdh_assert_6_total :
    ∃ result, pqxdh.__6 = ok result := by
  simp [pqxdh.__6,
    pqxdh.RATCHET_CHAIN_SIZE,
    ratchet.RATCHET_CHAIN_SIZE]

theorem pqxdh_assert_7_total :
    ∃ result, pqxdh.__7 = ok result := by
  simp [pqxdh.__7,
    pqxdh.ROOT_KEY_INPUT_SIZE,
    pqxdh.DH_SECRET_SIZE,
    pqxdh.PQXDH_PADDING_SIZE,
    pqxdh.SHARED_SECRET_SIZE]

theorem pqxdh_assert_8_total :
    ∃ result, pqxdh.__8 = ok result := by
  simp [pqxdh.__8,
    pqxdh.ASSOCIATED_DATA_SIZE,
    constants.ASSOCIATED_DATA_SIZE]

theorem pqxdh_assert_9_total :
    ∃ result, pqxdh.__9 = ok result := by
  simp [pqxdh.__9,
    pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE]

theorem pqxdh_assert_10_total :
    ∃ result, pqxdh.__10 = ok result := by
  simp [pqxdh.__10,
    pqxdh.REGISTRATION_ID_SIZE,
    pqxdh.SIGN_PUBLIC_KEY_SIZE,
    pqxdh.X25519_PUBLIC_KEY_SIZE]

theorem pqxdh_assert_11_total :
    ∃ result, pqxdh.__11 = ok result := by
  simp [pqxdh.__11,
    pqxdh.SIGN_TYPE_ED25519]

theorem pqxdh_assert_12_total :
    ∃ result, pqxdh.__12 = ok result := by
  simp [pqxdh.__12,
    pqxdh.KEM_TYPE_MLKEM768]

theorem pqxdh_assert_13_total :
    ∃ result, pqxdh.__13 = ok result := by
  simp [pqxdh.__13,
    pqxdh.KEM_TYPE_X25519]

theorem pqxdh_assert_14_total :
    ∃ result, pqxdh.__14 = ok result := by
  simp [pqxdh.__14,
    pqxdh.KEY_ROLE_PREKEY]

theorem pqxdh_assert_15_total :
    ∃ result, pqxdh.__15 = ok result := by
  simp [pqxdh.__15,
    pqxdh.KEY_ROLE_ONE_TIME]

theorem pqxdh_assert_16_total :
    ∃ result, pqxdh.__16 = ok result := by
  simp [pqxdh.__16,
    pqxdh.KEY_ROLE_PREKEY,
    pqxdh.KEY_ROLE_ONE_TIME]

theorem pqxdh_beacon_ratchet_initialization_total :
    ∃ result, pqxdh.beacon_ratchet_initialization = ok result := by
  simp [pqxdh.beacon_ratchet_initialization,
    pqxdh.BEACON_RATCHETS,
    pqxdh.RATCHET_CHAIN_SIZE,
    ratchet.RATCHET_CHAIN_SIZE, lift]

theorem pqxdh_server_ratchet_initialization_total :
    ∃ result, pqxdh.server_ratchet_initialization = ok result := by
  simp [pqxdh.server_ratchet_initialization,
    pqxdh.SERVER_RATCHETS,
    pqxdh.RATCHET_CHAIN_SIZE,
    ratchet.RATCHET_CHAIN_SIZE, lift]

theorem ratchet_control_RECEIVE_CACHE_CAPACITY_total :
    ∃ result, ratchet.control.RECEIVE_CACHE_CAPACITY = ok result := by
  simp [ratchet.control.RECEIVE_CACHE_CAPACITY,
    ratchet.control.RATCHET_MAX_GAP]

theorem ratchet_RATCHET_KDF_OUTPUT_SIZE_total :
    ∃ result, ratchet.RATCHET_KDF_OUTPUT_SIZE = ok result := by
  simp [ratchet.RATCHET_KDF_OUTPUT_SIZE,
    commitment.AEAD_KEY_SIZE,
    ratchet.RATCHET_CHAIN_SIZE,
    commitment.AEAD_NONCE_SIZE]

theorem ratchet_concrete_assert_total :
    ∃ result, ratchet.concrete._ = ok result := by
  simp [ratchet.concrete._,
    ratchet.RATCHET_KDF_OUTPUT_SIZE,
    commitment.AEAD_KEY_SIZE,
    ratchet.RATCHET_CHAIN_SIZE,
    commitment.AEAD_NONCE_SIZE]

theorem ratchet_control_RatchetState_Insts_CoreDefaultDefault_default_total :
    ∃ result, ratchet.control.RatchetState.Insts.CoreDefaultDefault.default = ok result := ⟨_, rfl⟩

theorem ratchet_assert_total :
    ∃ result, ratchet._ = ok result := by
  simp [ratchet._,
    ratchet.RATCHET_KDF_OUTPUT_SIZE,
    commitment.AEAD_KEY_SIZE,
    ratchet.RATCHET_CHAIN_SIZE,
    commitment.AEAD_NONCE_SIZE]

end BeaconcryptCore.PanicFreedom.Static
