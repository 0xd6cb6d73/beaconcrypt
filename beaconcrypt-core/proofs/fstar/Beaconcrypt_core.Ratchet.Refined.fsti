/// SPDX-License-Identifier: 0BSD
module Beaconcrypt_core.Ratchet.Refined

open FStar.Mul
open Core_models

val t_RatchetStep : Type0 -> Type0 -> Type0

val t_RefinedRatchet : Type0 -> Type0 -> Type0 -> Type0

val impl__from_counters :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  u64 ->
  u64 ->
  v_SendChain ->
  v_ReceiveChain ->
  Tot (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)

val impl__send_sequence :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material ->
  Tot u64

val impl__receive_sequence :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material ->
  Tot u64

val impl__receive_cache_len :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material ->
  Tot u8

val impl__send_chain :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material ->
  Tot v_SendChain

val impl__receive_chain :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material ->
  Tot v_ReceiveChain

val impl__receive_entry_at :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material ->
  u8 ->
  Tot (Core_models.Option.t_Option (u64 & v_Material))

val refined_seal_next :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  #v_Context:Type0 ->
  #v_Output:Type0 ->
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material ->
  (v_SendChain -> t_RatchetStep v_SendChain v_Material) ->
  v_Context ->
  (v_Material -> u64 -> v_Context -> Core_models.Option.t_Option v_Output) ->
  Tot
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      Core_models.Option.t_Option v_Output)

val t_RefinedRatchetRestore : Type0 -> Type0 -> Type0 -> Type0

val start_refined_restore :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  u64 ->
  u64 ->
  v_SendChain ->
  v_ReceiveChain ->
  Tot (t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material)

val refined_restore_receive_key :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material ->
  u64 ->
  v_Material ->
  Tot
    (t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material & bool)

val finish_refined_restore :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material ->
  Tot (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)

val refined_open_and_finish :
  #v_SendChain:Type0 ->
  #v_ReceiveChain:Type0 ->
  #v_Material:Type0 ->
  #v_Context:Type0 ->
  #v_Plaintext:Type0 ->
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material ->
  u64 ->
  (v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material) ->
  v_Context ->
  (v_Material -> u64 -> v_Context -> Core_models.Option.t_Option v_Plaintext) ->
  Tot
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      Core_models.Option.t_Option v_Plaintext)
