-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementFields
import BeaconcryptCore.Computational.RegistrationNativePacketReadback
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
/-! Per-field fixed-shape HKDF extract/expand functional representation. The exact source zeroizing vector, borrowed slice and checked 32-byte conversion compose to the existing native root reply. Selected fixed-width backend/allocation errors are explicitly excluded by these primitive field contracts; general source error behavior remains proved separately. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementHkdf
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]

def expanded (functional : Pqxdh.Crypto) (request : agreement.RootKdfRequest) : alloc.vec.Vec U8 :=
  ⟨(RegistrationAgreementShared.rootResponse functional request).val, by
    rw [(RegistrationAgreementShared.rootResponse functional request).property]
    scalar_tac⟩

structure Contract (functional : Pqxdh.Crypto) where
  prk : Array U8 192#usize → material.KdfPrk
  extract : ∀ input, crypto.extract .None (Array.to_slice input) = pure (.Ok (prk input))
  expand : ∀ input info, crypto.expand 32#usize (.Some (Array.to_slice info)) (prk input) =
    pure (.Ok (expanded functional ⟨input, info⟩))

omit material primitive crypto [LawfulMonad m] in
private theorem lift_ok {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl

theorem root (functional : Pqxdh.Crypto) (contract : Contract (m := m) functional)
    (request : agreement.RootKdfRequest) :
    AdapterPublicAgreementFields.root (m := m) request =
      pure (.Some (RegistrationAgreementShared.rootResponse functional request)) := by
  rw [AdapterPublicAgreementFields.root, contract.extract, pure_bind]
  dsimp only
  rw [contract.expand, pure_bind]
  dsimp only
  simp only [zeroize.Zeroizing.new, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
    alloc.vec.Vec.as_slice, rust_primitives.sequence.seq_to_slice,
    expanded, lift_ok, pure_bind]
  change ((do let parsed ← liftRust (core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      32#usize core.U8.Insts.CoreMarkerCopy
      (RegistrationAgreementShared.rootResponse functional request).to_slice)
              liftRust (core.result.Result.ok parsed)) : RustT m (core.option.Option (Array U8 32#usize))) = _
  rw [RegistrationNativePacketReadback.copied_array]
  simp only [lift_ok, pure_bind, core.result.Result.ok]
end BeaconcryptCore.Refinement.AdapterPublicAgreementHkdf

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementHkdf.root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementHkdf.root
