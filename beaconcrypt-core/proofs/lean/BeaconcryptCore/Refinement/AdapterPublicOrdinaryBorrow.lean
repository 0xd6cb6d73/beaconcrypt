-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicOrdinaryExtraction.Funs
/-! The isolated ordinary SDK fixture distributes two standard optional-borrow operations over their actual constructors. These laws retain the whole mutable return lens, including unchanged public-key and session binding fields. No effectful child or callback is replaced. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow
variable {A B S : Type} {m : Type → Type} [Monad m]

def optionalLens (view : A → m (B ×(B → A))) (value : Option A) :
    m (Option B ×(Option B → Option A)) :=
  match value with
  | none => pure (none, fun _ => none)
  | some input => do
      let reached ← view input
      pure (some reached.1, fun changed => some (reached.2 (changed.getD reached.1)))

theorem optional_lens [LawfulMonad m]
    (get : m (Option A ×(Option A → S))) (view : A → m (B ×(B → A))) :
    (do
      let entry ← get
      let selected ← optionalLens view entry.1
      pure (selected.1, fun changed => entry.2 (selected.2 changed))) =
    (do
      let entry ← get
      match entry.1 with
      | none => pure (none, fun _ => entry.2 none)
      | some input => do
          let reached ← view input
          pure (some reached.1, fun changed =>
            entry.2 (some (reached.2 (changed.getD reached.1))))) := by
  apply bind_congr
  intro entry
  cases entry.1 <;> simp only [optionalLens, pure_bind, bind_assoc]

omit [Monad m] in
theorem borrowed_option_branch (value : core.option.Option A)
    (next : A → RustM (core.option.Option B ×S)) (before : S) :
    (show RustM (core.option.Option B ×S) from do
      let branch ← core.option.Option.Insts.CoreOpsTry_traitTry.branch value
      match branch with
      | .Continue selected => next selected
      | .Break residual => do
          let empty ← core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual B residual
          pure (empty,before)) =
    (match value with | none => pure (none,before) | some selected => next selected) := by
  cases value <;> rfl

omit [Monad m] in
theorem remote_lens {Pk : Type} (signature : beaconcrypt_public_wrapper.shared.SignaturePk Pk)
    (remote : beaconcrypt_public_wrapper.shared.EstablishedRemote Pk) :
    beaconcrypt_public_ordinary.shared.EstablishedRemote.ratchet_mut signature remote =
      .ok (remote.peer.ratchet, fun changed =>
        {remote with peer := {remote.peer with ratchet := changed}}) := by rfl

omit [Monad m] in
theorem remote_put_get {Pk : Type} (remote : beaconcrypt_public_wrapper.shared.EstablishedRemote Pk)
    (changed : beaconcrypt_public_wrapper.ratchet.RatchetManager) :
    ({remote with peer := {remote.peer with ratchet := changed}} :
      beaconcrypt_public_wrapper.shared.EstablishedRemote Pk).peer.ratchet = changed := by rfl

omit [Monad m] in
theorem remote_get_put {Pk : Type} (remote : beaconcrypt_public_wrapper.shared.EstablishedRemote Pk) :
    ({remote with peer := {remote.peer with ratchet := remote.peer.ratchet}} :
      beaconcrypt_public_wrapper.shared.EstablishedRemote Pk) = remote := by rfl

end BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow.optional_lens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow.optional_lens

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow.borrowed_option_branch' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow.borrowed_option_branch

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow.remote_lens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow.remote_lens

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow.remote_put_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow.remote_put_get

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow.remote_get_put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryBorrow.remote_get_put
