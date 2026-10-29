-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSource
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyStartupBound

/-! The literal origin-aware fresh hit in the permitted native record view is exactly the actual native entropy fresh event. This supplies the byte bound without re-establishing cryptographic target provenance in the all-random world. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordViewFresh
open RegistrationNativeRecordPackage (View nativeView)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {ι KemSK E ProviderState Value : Type} {base : OracleSpec ι}

def FreshHit (claim : Value → Option (Nat × Pqxdh.Bytes)) (view : View n E Value) : Prop :=
  ∃ born ∈ view.result, ∃ index guess entry, claim born.2.1.1 = some (index, guess) ∧
    born.2.1.2.ledger.fresh[index]? = some entry ∧ (view.slots entry.handle).isSome ∧ entry.message = guess

noncomputable def event (claim : Value → Option (Nat × Pqxdh.Bytes)) (view : View n E Value) : Bool :=
  @decide (FreshHit claim view) (Classical.propDecidable _)

/-- The allowed view uses the actual same control-origin map and the literal same private fresh entry. -/
theorem native_event (claim : Value → Option (Nat × Pqxdh.Bytes))
    (result : RegistrationNativeEntropyRun.Result n E Value) :
    event claim (nativeView result.1 result.2.base.produced) = RegistrationNativeEntropyFresh.event claim result := by
  rfl

/-- The exact cold all-random native view has the same byte guessing term with no target-count factor. -/
theorem fresh_bytes (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) :
    𝒟[event claim <$>
      RegistrationNativeRecordPackage.ctx (fun _ => .random) setup (RegistrationNativeWire.ledgerCodec wire) route
        (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate
          provider providerState selectedOwner selectedAccept bounds .P adversary)] {true} ≤ ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  rw [RegistrationNativeSelectiveRecordViewSource.ideal_source, Functor.map_map]
  simpa only [native_event] using RegistrationNativeSelectiveEntropyStartupBound.initial_fresh_bytes setup checks wire route source
    ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary claim

end BeaconcryptCore.Computational.RegistrationNativeRecordViewFresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordViewFresh.native_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordViewFresh.native_event
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordViewFresh.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordViewFresh.fresh_bytes
