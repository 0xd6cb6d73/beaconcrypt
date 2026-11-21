-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementMonadInterpreter
import BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Interpreting the actual source primitive coins in an arbitrary outer monad preserves its full Rust result and private StateT state. Mapping each individual SDK crypto field gives the same complete source executor, so an external allocation state can be retained without a whole-controller interpretation assumption. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicAgreementMonadMap
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
open RegistrationNativePlatformInterpret (state state_pure state_bind)
variable {κ State A B : Type} {spec : OracleSpec κ}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "SourceM" => StateT State (OracleComp spec)
local notation "TargetM" => StateT State m

def transform (implementation : QueryImpl spec m) (work : RustT SourceM A) : RustT TargetM A :=
  ⟨state implementation work.run⟩

omit [LawfulMonad m] in
theorem transform_pure (implementation : QueryImpl spec m) (value : A) :
    transform (State := State) implementation (pure value) = pure value := by
  apply RustT.ext
  exact state_pure implementation (RustM.ok value)

omit [LawfulMonad m] in
theorem transform_liftRust (implementation : QueryImpl spec m) (result : RustM A) :
    transform (State := State) implementation (AdapterRecordRequestMonad.liftRust result) = AdapterRecordRequestMonad.liftRust result := by
  apply RustT.ext
  exact state_pure implementation result

theorem transform_bind (implementation : QueryImpl spec m) (work : RustT SourceM A) (next : A → RustT SourceM B) :
    transform implementation (work >>= next) = (transform implementation work >>= fun value => transform implementation (next value)) := by
  apply RustT.ext
  change state implementation ((work >>= next).run) = _
  rw [RustT.run_bind, state_bind]
  change (state implementation work.run >>= fun reply => state implementation (match reply with
    | .ok value => (next value).run
    | .fail error => pure (.fail error)
    | .div => pure .div)) = _
  rw [RustT.run_bind]
  apply bind_congr
  intro reply
  cases reply <;> rfl

@[instance_reducible] def translation (implementation : QueryImpl spec m) : Transformation SourceM TargetM where
  transform := transform implementation
  lawful := Cslib.IsMonadHom.mk' (transform_pure implementation) (transform_bind implementation)
  lift := transform_liftRust implementation

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

@[instance_reducible] def operations (implementation : QueryImpl spec m) (original : CryptoOperations (RustT SourceM)) : CryptoOperations (RustT TargetM) :=
  letI : Transformation SourceM TargetM := translation implementation
  AdapterPublicAgreementMonadCrypto.operations (left := SourceM) (right := TargetM) original

noncomputable section
theorem execute (implementation : QueryImpl spec m) (original : CryptoOperations (RustT SourceM))
    {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : AdapterPublicAgreementFields.Keys)
    (phase : agreement.AgreementEffect) (rng : R) :
    letI : CryptoOperations (RustT TargetM) := operations implementation original
    beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT TargetM) generator phase keys rng =
      transform implementation (letI : CryptoOperations (RustT SourceM) := original
        beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT SourceM) generator phase keys rng) := by
  let : CryptoOperations (RustT SourceM) := original
  let : Transformation SourceM TargetM := translation implementation
  exact AdapterPublicAgreementMonadInterpreter.execute (left := SourceM) (right := TargetM) generator keys phase rng

theorem entry (implementation : QueryImpl spec m) (original : CryptoOperations (RustT SourceM))
    {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : AdapterPublicAgreementFields.Keys)
    (start : RustM agreement.AgreementEffect) (rng : R) :
    letI : CryptoOperations (RustT TargetM) := operations implementation original
    (do let phase ← AdapterRecordRequestMonad.liftRust start
        beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT TargetM) generator phase keys rng) =
      transform implementation (letI : CryptoOperations (RustT SourceM) := original
        (do let phase ← AdapterRecordRequestMonad.liftRust start
            beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT SourceM) generator phase keys rng)) := by
  let : CryptoOperations (RustT SourceM) := original
  let : Transformation SourceM TargetM := translation implementation
  exact AdapterPublicAgreementMonadInterpreter.entry (left := SourceM) (right := TargetM) generator keys start rng

theorem program (implementation : QueryImpl spec m) (original : CryptoOperations (RustT SourceM))
    {R E Value : Type} (generator : rand_core.TryCryptoRng R E) (keys : AdapterPublicAgreementFields.Keys)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : AdapterPublicAgreementInterpreter.Capture R) :
    letI : CryptoOperations (RustT TargetM) := operations implementation original
    (simulateQ (AdapterPublicAgreementInterpreter.handler (m := TargetM) generator keys) work).run before =
      transform implementation (letI : CryptoOperations (RustT SourceM) := original
        (simulateQ (AdapterPublicAgreementInterpreter.handler (m := SourceM) generator keys) work).run before) := by
  let : CryptoOperations (RustT SourceM) := original
  let : Transformation SourceM TargetM := translation implementation
  exact AdapterPublicAgreementMonadInterpreter.program (left := SourceM) (right := TargetM) generator keys work before
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.transform_pure' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.transform_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.transform_liftRust' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.transform_liftRust

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.transform_bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.transform_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.execute

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.entry

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementOracleInterpretation.program
