-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceStartup
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelTraceInvariant

/-! Actual effectful native startup establishes the installation invariant in its literal reached World. The subsequent complete selective ledger derives the same trace-to-physical-slot association, so no independent trace or origin marginal is substituted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceHidden
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveRecordTraceStartup (Outcome Extra program after)
open RegistrationNativeInstallKernelStorage (Selected)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Result (n : Nat) (KemSK ProviderState Secret Value : Type) (source : RegistrationNativeMldsa.Source) :=
  ((Outcome n KemSK ProviderState Value source × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret

def Holds (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (result : Result n KemSK ProviderState Secret Value source) : Prop :=
  match result.1.1.1 with
  | none => True
  | some finished => RegistrationNativeInstallOrdinals.Hidden finished.2.2.2.events finished.2.1.2.transcript
      (PqxdhRecordLiftIdeal.handleSlot result.1.2) (Selected setup seed scalar candidate)

/-- The same actual startup and original full ledger derive the hidden-slot association jointly with the final complete trace. -/
theorem initialized (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (secret : Secret)
    (result : Result n KemSK ProviderState Secret Value source)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds mode adversary)
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret)) :
    Holds setup seed scalar candidate result := by
  unfold program at supported
  rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
  obtain ⟨initialized, startupSupport, continued⟩ := supported
  rcases initialized with ⟨⟨⟨initialized, shell⟩, control⟩, reached⟩
  cases initialized with
  | none =>
      rw [CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at continued
      subst result
      trivial
  | some born =>
      simp only [after, RegistrationNativeHiddenEnvironmentWorld.interpret_map, support_map] at continued
      obtain ⟨observed, observedSupport, rfl⟩ := continued
      have valid := RegistrationNativeInstallKernelInitial.initialized setup ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
        providerState service codec route secret born shell control reached startupSupport
      have invariant := RegistrationNativeInstallKernelTraceInvariant.run setup checks wire
        (RegistrationNativeMldsa.owned source born.native.credential) seed scalar candidate provider service codec route selectedOwner selectedAccept
        serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩)
        (RegistrationNativeInstallKernelInitial.initial born providerState shell control reached) valid
        (RegistrationNativeInstallKernelInitial.empty born providerState shell control reached) observed observedSupport
      exact invariant.2.2

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceHidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceHidden.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceHidden.initialized
