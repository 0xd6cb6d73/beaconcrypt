-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceHidden
import BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto

/-! The actual real record observation retains the original ledger, full native trace and physical hidden slots jointly. Erasing only the reduction-owned trace gives the existing actual and ideal permitted record views, so their established record bills and fresh-byte bound remain applicable. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceView
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRecordPackage (View)
open RegistrationNativeSelectiveRecordTraceStartup (Extra program forget)
open RegistrationNativeInstallKernelStorage (Selected)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def erase (view : View n (Extra n KemSK ProviderState source) Value) :
    View n (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) Value :=
  ⟨forget view.result, view.produced, view.raw, view.slots⟩

def Hidden (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (view : View n (Extra n KemSK ProviderState source) Value) : Prop :=
  ∀ finished ∈ view.result, RegistrationNativeInstallOrdinals.Hidden finished.2.2.2.events finished.2.1.2.transcript
    view.slots (Selected setup seed scalar candidate)

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (providerState : ProviderState) (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
  (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

/-- Every real annotated actual outcome derives its same-trace, same-ledger physical hidden-slot association. -/
theorem real_hidden (view : View n (Extra n KemSK ProviderState source) Value)
    (supported : view ∈ support (RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route
      (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary))) : Hidden setup seed scalar candidate view := by
  rw [RegistrationNativeRecordViewCrypto.real_source, support_map] at supported
  obtain ⟨result, reached, rfl⟩ := supported
  have invariant := RegistrationNativeSelectiveRecordTraceHidden.initialized setup checks wire source ensureInit identityIndex serverKeyId
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary _ _ route _ result reached
  intro finished present
  cases outcome : result.1.1.1 with
  | none => simp [RegistrationNativeRecordPackage.nativeView, outcome] at present
  | some born =>
      have same : born = finished := by simpa only [RegistrationNativeRecordPackage.nativeView, outcome, Option.mem_some_iff] using present
      subst finished
      simpa only [RegistrationNativeSelectiveRecordTraceHidden.Holds, outcome, RegistrationNativeRecordPackage.nativeView] using invariant

/-- Dropping only the internal native trace recovers the identical existing real permitted record view. -/
theorem real_erase :
    erase <$> RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route
      (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary) =
      RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route
        (RegistrationNativeSelectiveRecordStartup.program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
          selectedOwner selectedAccept bounds mode adversary) := by
  rw [← RegistrationNativeSelectiveRecordTraceStartup.erase setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds mode adversary]
  rw [RegistrationNativeRecordViewCrypto.real_source, RegistrationNativeRecordViewCrypto.real_source,
    RegistrationNativeHiddenEnvironmentWorld.interpret_map]
  simp only [Functor.map_map, erase, RegistrationNativeRecordPackage.nativeView]

/-- The same erasure recovers the identical existing ideal record view, retaining its literal physical origin map. -/
theorem ctx_erase (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode) :
    erase <$> RegistrationNativeRecordPackage.ctx modes setup (RegistrationNativeWire.ledgerCodec wire) route
      (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary) =
      RegistrationNativeRecordPackage.ctx modes setup (RegistrationNativeWire.ledgerCodec wire) route
        (RegistrationNativeSelectiveRecordStartup.program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
          selectedOwner selectedAccept bounds mode adversary) := by
  rw [← RegistrationNativeSelectiveRecordTraceStartup.erase setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds mode adversary]
  rw [RegistrationNativeRecordPackage.ctx_source, RegistrationNativeRecordPackage.ctx_source,
    RegistrationNativeHiddenEnvironmentWorld.interpret_map]
  simp only [Functor.map_map, erase, RegistrationNativeRecordPackage.nativeView]

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceView
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceView.real_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceView.real_hidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceView.real_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceView.real_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceView.ctx_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceView.ctx_erase
