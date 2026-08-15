/// SPDX-License-Identifier: 0BSD
module Beaconcrypt_core.Ratchet.Control

open FStar.Mul
open Core_models

val v_RATCHET_MAX_GAP : u64

val v_RECEIVE_CACHE_CAPACITY : usize

val t_RatchetState : Type0

val impl_RatchetState__from_counters :
  u64 -> u64 -> Tot t_RatchetState

val impl_RatchetState__send_sequence :
  t_RatchetState -> Tot u64

val impl_RatchetState__receive_sequence :
  t_RatchetState -> Tot u64

val impl_RatchetState__receive_cache_len :
  t_RatchetState -> Tot u8

val impl_RatchetState__receive_key_at :
  t_RatchetState -> u8 -> Tot (Core_models.Option.t_Option u64)

val t_SendKey : Type0

val impl_SendKey__sequence :
  t_SendKey -> Tot (Core_models.Option.t_Option u64)

val impl_SendKey__is_available :
  t_SendKey -> Tot bool

val t_SendAdvance : Type0

val advance_send :
  t_RatchetState -> Tot t_SendAdvance

val t_SendFinish : Type0

val finish_send :
  t_SendKey -> Tot t_SendFinish

val t_ReceivePlan : Type0

val plan_receive_until :
  t_RatchetState -> u64 -> Tot t_ReceivePlan

val t_ReceiveAdvance : Type0

val advance_receive :
  t_RatchetState -> Tot t_ReceiveAdvance

val t_ReceiveDisposition : Type0

val t_ReceiveRemoval : Type0

val t_ReceiveFinishWithRemoval : Type0

val finish_receive_with_removal :
  t_RatchetState ->
  u64 ->
  u8 ->
  bool ->
  Tot t_ReceiveFinishWithRemoval

val t_RatchetRestore : Type0

val start_restore :
  u64 -> u64 -> Tot t_RatchetRestore

val t_ReceiveRestoreStep : Type0

val restore_receive_key_with_slot :
  t_RatchetRestore ->
  u64 ->
  Tot (Core_models.Option.t_Option t_ReceiveRestoreStep)

val finish_restore :
  t_RatchetRestore -> Tot t_RatchetState

val lookup_receive_key :
  t_RatchetState -> u64 -> Tot (Core_models.Option.t_Option u8)
