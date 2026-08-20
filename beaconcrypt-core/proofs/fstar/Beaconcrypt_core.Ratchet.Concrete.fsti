/// SPDX-License-Identifier: 0BSD
module Beaconcrypt_core.Ratchet.Concrete

open FStar.Mul
open Core_models

val t_ConcreteRatchetKernel : Type0

val impl_ConcreteRatchetKernel__new :
  Beaconcrypt_core.Ratchet.t_RatchetChain ->
  Beaconcrypt_core.Ratchet.t_RatchetChain ->
  (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest ->
    t_Array u8 (mk_usize 76)) ->
  Tot t_ConcreteRatchetKernel
