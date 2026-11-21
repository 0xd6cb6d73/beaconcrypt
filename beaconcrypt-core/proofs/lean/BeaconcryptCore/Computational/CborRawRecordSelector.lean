-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordFresh

/-! A selector on `PublicHiding` masks only the terminal observation. It never stops or changes the adaptive protocol execution. Byte shifts preserve this selector, including fresh-message handles, failed send replies, full native environment metadata and the original public transcript. Despite its existing name, `PublicHiding` is a message-shift-invariant analysis projection: it includes the environment state, produced frames, counters and hidden slot map. It is not automatically the adversary-visible native view. A concrete native claim selector still requires factorization through the actual permitted native observations and correspondence to this analysis projection. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawRecordSelector
open PqxdhRecordLiftIdeal PqxdhRecordLiftFresh
variable {n : Nat} {E X : Type}

def mask (select : PublicHiding n E X → Bool) (result : Client n E X × CtxPrivate n) : Client n E X × CtxPrivate n :=
  if select (publicHiding (ctxView result)) then result else ((none, result.1.2), result.2)

/-- Masking the terminal result conjoins its selector with the original fresh-message win. -/
theorem mask_fresh (select : PublicHiding n E X → Bool) (claim : X → Option (Nat × Pqxdh.Bytes))
    (result : Client n E X × CtxPrivate n) :
    freshEvent claim (ctxView (mask select result)) =
      (select (publicHiding (ctxView result)) && freshEvent claim (ctxView result)) := by
  simp only [mask]
  split
  all_goals simp_all [ctxView, viewOf, freshEvent, FreshHit]

theorem map_modify_invariant {A B : Type} (observe : A → B) (change : A → A)
    (unchanged : ∀ value, observe (change value) = observe value) (values : List A) (index : Nat) :
    (values.modify index change).map observe = values.map observe := by
  induction values generalizing index
  all_goals cases index <;> simp_all [List.modify]

/-- Selectors on this analysis projection cannot see a byte shift of one private fresh message. -/
theorem public_shift (index : Nat) (offsets : Nat → Fin 256) (value : X)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (environment : E)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (raw : PqxdhRecordLiftWorld.RawCounters) (slots : PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n)) :
    publicHiding (⟨some (value, shiftLedger index offsets ledger, environment), produced, raw, slots⟩ : View n E X) =
      publicHiding (⟨some (value, ledger, environment), produced, raw, slots⟩ : View n E X) := by
  simp only [publicHiding, shiftLedger, Option.map_some]
  rw [map_modify_invariant (fun entry : PqxdhDeploymentSecrecy.FreshEntry => (entry.handle, entry.reply))
    (shiftEntry offsets) (fun _ => rfl)]

theorem mask_hitAt (select : PublicHiding n E X → Bool) (claim : X → Option (Nat × Pqxdh.Bytes))
    (index length : Nat) (result : Client n E X × CtxPrivate n) :
    hitAt claim index length (ctxView (mask select result)) =
      (select (publicHiding (ctxView result)) && hitAt claim index length (ctxView result)) := by
  simp only [mask]
  split
  all_goals simp_all [ctxView, viewOf, hitAt, FreshHit]

theorem mask_shiftedHit (select : PublicHiding n E X → Bool) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : Nat) (offsets : Fin length → Fin 256)
    (result : Client n E X × CtxPrivate n) :
    shiftedHit bounds claim index length offsets (ctxView (mask select result)) =
      (select (publicHiding (ctxView result)) && shiftedHit bounds claim index length offsets (ctxView result)) := by
  simp only [mask]
  split
  all_goals simp_all [ctxView, viewOf, shiftedHit]

/-- A returned masked result always satisfies its selector. -/
theorem mask_present (select : PublicHiding n E X → Bool) (result : Client n E X × CtxPrivate n)
    (present : (ctxView (mask select result)).result.isSome = true) :
    select (publicHiding (ctxView result)) = true := by
  simp only [mask] at present
  split at present
  all_goals simp_all [ctxView, viewOf]

theorem selected_shift (select : PublicHiding n E X → Bool) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : Nat) (offsets : Fin length → Fin 256)
    (value : X) (ledger : PqxdhDeploymentSecrecy.Ledger) (environment : E)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (raw : PqxdhRecordLiftWorld.RawCounters) (slots : PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n))
    (long : FreshLong bounds ledger) :
    (select (publicHiding (⟨some (value, ledger, environment), produced, raw, slots⟩ : View n E X)) &&
      hitAt claim index length ⟨some (value, ledger, environment), produced, raw, slots⟩) =
    (select (publicHiding ⟨some (value, shiftLedger index (extend offsets) ledger, environment), produced, raw, slots⟩) &&
      shiftedHit bounds claim index length offsets
        ⟨some (value, shiftLedger index (extend offsets) ledger, environment), produced, raw, slots⟩) := by
  exact congrArg₂ (fun first second : Bool => first && second)
    (congrArg select (public_shift index (extend offsets) value ledger environment produced raw slots).symm)
    (hitAt_shift bounds claim index length offsets value ledger environment produced raw slots long)

end BeaconcryptCore.Computational.CborRawRecordSelector

/-- info: 'BeaconcryptCore.Computational.CborRawRecordSelector.mask_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordSelector.mask_fresh
/-- info: 'BeaconcryptCore.Computational.CborRawRecordSelector.map_modify_invariant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordSelector.map_modify_invariant
/-- info: 'BeaconcryptCore.Computational.CborRawRecordSelector.public_shift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordSelector.public_shift
/-- info: 'BeaconcryptCore.Computational.CborRawRecordSelector.mask_hitAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordSelector.mask_hitAt
/-- info: 'BeaconcryptCore.Computational.CborRawRecordSelector.mask_shiftedHit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordSelector.mask_shiftedHit
/-- info: 'BeaconcryptCore.Computational.CborRawRecordSelector.mask_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordSelector.mask_present
/-- info: 'BeaconcryptCore.Computational.CborRawRecordSelector.selected_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordSelector.selected_shift
