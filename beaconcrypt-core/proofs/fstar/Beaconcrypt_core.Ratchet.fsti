/// SPDX-License-Identifier: 0BSD
module Beaconcrypt_core.Ratchet

open FStar.Mul
open Core_models

val v_RATCHET_CHAIN_SIZE : x:usize { x == mk_usize 32 }

val v_SYM_RATCHET_INFO : t_Array u8 (mk_usize 41)

val t_RatchetChain : Type0

val impl_RatchetChain__from_bytes :
  t_Array u8 (mk_usize 32) -> Tot t_RatchetChain

val t_SymmetricRatchetKdfRequest : Type0

val impl_SymmetricRatchetKdfRequest__new :
  t_Array u8 (mk_usize 32) -> Tot t_SymmetricRatchetKdfRequest
