-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWeightedStartup
import BeaconcryptCore.Computational.RegistrationNativeRecordViewFresh
import BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace

/-! Both selector probability and selected fresh guessing remain in the same actual record view after effectful startup. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView
open RegistrationNativeRecordPackage (View nativeView)
open RegistrationNativeCanonicalSelector (Target selected)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {ι KemSK E ProviderState Value : Type} {base : OracleSpec ι}

noncomputable def selection (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget)
    (view : View n E Value) : Bool :=
  RegistrationNativeSelectedRecordTrace.viewSelected (fun result => selected crypto wire serverKeyId budget claim target result.1 result.2) view

noncomputable def winning (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget)
    (view : View n E Value) : Bool :=
  selection crypto wire serverKeyId budget claim target view && RegistrationNativeRecordViewFresh.event claim view

theorem native_selection (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget)
    (result : RegistrationNativeEntropyRun.Result n E Value) :
    selection crypto wire serverKeyId budget claim target (nativeView result.1 result.2.base.produced) =
      RegistrationNativeWeightedFresh.selection crypto wire serverKeyId budget claim target result := by
  rcases result with ⟨⟨born, control⟩, secret⟩
  cases born <;> rfl

theorem native_winning (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget)
    (result : RegistrationNativeEntropyRun.Result n E Value) :
    winning crypto wire serverKeyId budget claim target (nativeView result.1 result.2.base.produced) =
      RegistrationNativeWeightedFresh.winning crypto wire serverKeyId budget claim target result := by
  rcases result with ⟨⟨born, control⟩, secret⟩
  cases born <;> rfl
/-- The exact cold all-random native view has the same byte guessing term with no target-count factor. -/
theorem fresh_bytes (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (targetBudget : PqxdhDeploymentInterface.Budget)
    (target : Target targetBudget) :
    𝒟[winning setup.source.crypto wire serverKeyId targetBudget claim target <$>
      RegistrationNativeRecordPackage.ctx (fun _ => .random) setup (RegistrationNativeWire.ledgerCodec wire) route
        (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate
          provider providerState selectedOwner selectedAccept bounds .P adversary)] {true} ≤ ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
      𝒟[selection setup.source.crypto wire serverKeyId targetBudget claim target <$>
        RegistrationNativeRecordPackage.ctx (fun _ => .random) setup (RegistrationNativeWire.ledgerCodec wire) route
          (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate
            provider providerState selectedOwner selectedAccept bounds .P adversary)] {true} := by
  rw [RegistrationNativeSelectiveRecordViewSource.ideal_source]
  simp only [Functor.map_map, native_winning, native_selection]
  exact RegistrationNativeWeightedStartup.startup_bytes setup checks wire route source ensureInit identityIndex serverKeyId
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary claim targetBudget target
    PqxdhRecordLiftIdeal.CtxPrivate.initial

end BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView.native_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView.native_selection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView.native_winning' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView.native_winning

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView.fresh_bytes
