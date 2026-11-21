-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordRequestMonad

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

/-! Only reservation is an effectful leaf of the fixed-two join. Checked lengths, option control flow, vector construction and ordered extension remain the original lifted RustM calls. The reserve interface sees the actual pre-extension vector and requested capacity, and retains its returned vector and error. No allocation-success or joined-byte law is assumed. -/

namespace BeaconcryptCore.Refinement.AdapterSealJoinRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)

class Operations (E : Type) (m : Type → Type) where
  reserve : alloc.vec.Vec U8 → Usize → m (core.result.Result Unit E × alloc.vec.Vec U8)

namespace Lifted
variable {m : Type → Type} [LiftRust m]

def index (parts : Array (Slice U8) 2#usize) (position : Usize) :=
  liftRust (Array.index_usize parts position) (m := m)
def len (input : Slice U8) := liftRust (core.slice.Slice.len input) (m := m)
def checkedAdd (left right : Usize) := liftRust (core.num.Usize.checked_add left right) (m := m)
def branch {A : Type} (value : core.option.Option A) :=
  liftRust (core.option.Option.Insts.CoreOpsTry_traitTry.branch value) (m := m)
def fromResidual (value : core.option.Option core.convert.Infallible) :=
  liftRust (core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
    (alloc.vec.Vec U8) value) (m := m)
def new := liftRust (alloc.vec.Vec.new U8) (m := m)
def resultOk {E : Type} (value : core.result.Result Unit E) :=
  liftRust (core.result.Result.ok value) (m := m)
def extend (before : alloc.vec.Vec U8) (input : Slice U8) :=
  liftRust (alloc.vec.Vec.extend_from_slice core.U8.Insts.CoreCloneClone before input) (m := m)

end Lifted
end BeaconcryptCore.Refinement.AdapterSealJoinRequestMonad
