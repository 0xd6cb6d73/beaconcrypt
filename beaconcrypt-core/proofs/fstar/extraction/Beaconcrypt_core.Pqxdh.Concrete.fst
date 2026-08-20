module Beaconcrypt_core.Pqxdh.Concrete
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

friend Beaconcrypt_core.Ratchet
friend Beaconcrypt_core.Ratchet.Concrete

/// Apply the sole opaque initial-chain primitive to the exact session root
/// and order its output.
/// The primitive's complete production-facing type is
/// `32-byte root -> 64-byte output`.
/// Label selection and HKDF details are private to that domain-specific
/// primitive. Input selection, output size, role ordering, partitioning, and
/// fixed-width construction remain owned by the core.
let derive_initial_ratchet_chains
      (root: t_Array u8 (mk_usize 32))
      (initialization: Beaconcrypt_core.Pqxdh.t_RatchetInitialization)
      (kdf: (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 64)))
    : Beaconcrypt_core.Pqxdh.t_InitialRatchetChains =
  let request:Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest =
    Beaconcrypt_core.Ratchet.impl_SymmetricRatchetKdfRequest__new root
  in
  let output:t_Array u8 (mk_usize 64) = kdf request in
  Beaconcrypt_core.Pqxdh.split_initial_ratchet_kdf_output output initialization

/// Construct a concrete kernel directly from one root, one role plan, and the
/// executors for initial and subsequent core-owned KDF requests.
let derive_initial_ratchet_kernel
      (root: t_Array u8 (mk_usize 32))
      (initialization: Beaconcrypt_core.Pqxdh.t_RatchetInitialization)
      (initial_kdf:
          (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 64)))
      (ratchet_kdf:
          (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : Beaconcrypt_core.Ratchet.Concrete.t_ConcreteRatchetKernel =
  let chains:Beaconcrypt_core.Pqxdh.t_InitialRatchetChains =
    derive_initial_ratchet_chains root initialization initial_kdf
  in
  let
  (send_chain: Beaconcrypt_core.Ratchet.t_RatchetChain),
  (receive_chain: Beaconcrypt_core.Ratchet.t_RatchetChain) =
    Beaconcrypt_core.Pqxdh.impl_InitialRatchetChains__into_parts chains
  in
  Beaconcrypt_core.Ratchet.Concrete.impl_ConcreteRatchetKernel__new send_chain
    receive_chain
    ratchet_kdf

/// Construct the beacon role's complementary concrete kernel.
let derive_beacon_ratchet_kernel
      (root: t_Array u8 (mk_usize 32))
      (initial_kdf:
          (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 64)))
      (ratchet_kdf:
          (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : Beaconcrypt_core.Ratchet.Concrete.t_ConcreteRatchetKernel =
  derive_initial_ratchet_kernel root
    Beaconcrypt_core.Pqxdh.v_BEACON_RATCHETS
    initial_kdf
    ratchet_kdf

/// Construct the server role's complementary concrete kernel.
let derive_server_ratchet_kernel
      (root: t_Array u8 (mk_usize 32))
      (initial_kdf:
          (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 64)))
      (ratchet_kdf:
          (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : Beaconcrypt_core.Ratchet.Concrete.t_ConcreteRatchetKernel =
  derive_initial_ratchet_kernel root
    Beaconcrypt_core.Pqxdh.v_SERVER_RATCHETS
    initial_kdf
    ratchet_kdf

/// Bind an authenticated beacon registration candidate to its concrete
/// ratchet kernel.
/// Keeping this as a free function, rather than an inherent method on
/// `BeaconRegistrationCandidate`, ensures the proof-visible candidate type
/// has no dependency on executor function pointers or `ConcreteRatchetKernel`.
let derive_beacon_candidate_ratchet_kernel
      (candidate: Beaconcrypt_core.Pqxdh.t_BeaconRegistrationCandidate)
      (root: t_Array u8 (mk_usize 32))
      (initial_kdf:
          (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 64)))
      (ratchet_kdf:
          (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : Beaconcrypt_core.Ratchet.Concrete.t_ConcreteRatchetKernel =
  derive_initial_ratchet_kernel root
    (Beaconcrypt_core.Pqxdh.impl_BeaconRegistrationCandidate__ratchet_initialization candidate
      <:
      Beaconcrypt_core.Pqxdh.t_RatchetInitialization)
    initial_kdf
    ratchet_kdf

/// Bind an accepted server registration candidate to its concrete ratchet
/// kernel.
/// Keeping this as a free function, rather than an inherent method on
/// `ServerRegistrationCandidate`, ensures the proof-visible candidate type
/// has no dependency on executor function pointers or `ConcreteRatchetKernel`.
let derive_server_candidate_ratchet_kernel
      (candidate: Beaconcrypt_core.Pqxdh.t_ServerRegistrationCandidate)
      (root: t_Array u8 (mk_usize 32))
      (initial_kdf:
          (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 64)))
      (ratchet_kdf:
          (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : Beaconcrypt_core.Ratchet.Concrete.t_ConcreteRatchetKernel =
  derive_initial_ratchet_kernel root
    (Beaconcrypt_core.Pqxdh.impl_ServerRegistrationCandidate__ratchet_initialization candidate
      <:
      Beaconcrypt_core.Pqxdh.t_RatchetInitialization)
    initial_kdf
    ratchet_kdf
