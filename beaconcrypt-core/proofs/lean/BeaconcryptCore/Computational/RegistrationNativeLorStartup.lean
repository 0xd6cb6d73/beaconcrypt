-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorEntropy
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSource

/-! Actual effectful native startup and its shared-cache pin hash are averaged inside both LR observers. The same initialized allocation receipt supplies the exact native entropy environment; no new seed or CTX state is sampled for a target. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLorStartup
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open PqxdhRecordLiftIdeal (CtxPrivate ctxInterpreter)
open RegistrationNativeSelectiveEntropyStartup (run after run_start)
open RegistrationNativeSelectiveEntropyRun (nativeRun)
open RegistrationNativeSelectiveEntropyEnvironment (State)
open RegistrationNativeLorEntropy (winning eligible winningView eligibleView)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

theorem bind_half {A B : Type} (startup : ProbComp A) (next : A → ProbComp B) (win select : B → Prop)
    (fair : ∀ started ∈ support startup,
      Pr{let result ← next started}[win result] = 2⁻¹ * Pr{let result ← next started}[select result]) :
    Pr{let result ← startup >>= next}[win result] = 2⁻¹ * Pr{let result ← startup >>= next}[select result] := by
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro started
  by_cases supported : started ∈ support startup
  · rw [fair started supported]
    ac_rfl
  · have zero := prEvent_eq_zero_of_not_mem_support startup supported
    rw [zero]
    simp only [zero_mul, mul_zero]

/-- The actual initialized selective native interpreter has exact half fairness in its retained shared cache. -/
theorem native_lor (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (created : PqxdhLiveServerConstruction.Created Unit)
    (before : State n KemSK ProviderState source) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (valid : RegistrationNativeSelectiveAllocationJoint.Holds (((before, shell), control), secret)) :
    𝒟[winning setup.source.crypto wire serverKeyId budget filter guess target <$>
      nativeRun (fun _ => .random) id setup checks wire (RegistrationNativeWire.ledgerCodec wire) route source credential seed scalar candidate provider selectedOwner selectedAccept
        serverKeyId bounds .P work created before shell control secret] {true} =
      2⁻¹ * 𝒟[eligible setup.source.crypto wire serverKeyId budget filter target <$>
        nativeRun (fun _ => .random) id setup checks wire (RegistrationNativeWire.ledgerCodec wire) route source credential seed scalar candidate provider selectedOwner selectedAccept
          serverKeyId bounds .P work created before shell control secret] {true} := by
  rw [RegistrationNativeSelectiveEntropyRun.run_source (fun _ => .random) id setup checks wire route source credential seed scalar candidate provider selectedOwner selectedAccept
    serverKeyId bounds .P work created before shell control secret valid]
  exact RegistrationNativeLorEntropy.initialized_lor setup wire route _ serverKeyId bounds budget work filter guess target created before shell control secret

/-- Exact fairness averages the real effectful startup and all failures, retaining the original native test bit. -/
theorem startup_lor (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (secret : CtxPrivate n) :
    𝒟[winning setup.source.crypto wire serverKeyId budget filter guess target <$>
      run (n := n) (fun _ => .random) id setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds .P adversary secret] {true} =
      2⁻¹ * 𝒟[eligible setup.source.crypto wire serverKeyId budget filter target <$>
        run (n := n) (fun _ => .random) id setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
          selectedOwner selectedAccept bounds .P adversary secret] {true} := by
  simp only [← prEvent_eq_evalDist_singleton _ true, prEvent_map, run_start]
  apply bind_half
  intro started supported
  rcases started with ⟨⟨⟨initialized, shell⟩, control⟩, reached⟩
  cases initialized with
  | none => simp [after, winning, eligible, winningView, eligibleView, RegistrationNativeRecordPackage.nativeView]
  | some born =>
      dsimp only [after]
      have valid := RegistrationNativeHiddenAllocationStartup.initialized setup ensureInit identityIndex serverKeyId
        (setup.joint.publicKeys seed) providerState (ctxInterpreter (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire))
        (RegistrationNativeWire.ledgerCodec wire) route secret born shell control reached supported
      simpa only [← prEvent_eq_evalDist_singleton _ true, prEvent_map] using
        native_lor setup checks wire route source born.native.credential seed scalar candidate provider selectedOwner selectedAccept serverKeyId bounds
          (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩) budget filter guess target born.created
          (born.native.frontend, RegistrationNativeSelectiveHiddenInterpreter.initial providerState) shell control reached valid

/-- The literal native all-random record view has exact canonical LR fairness, with every startup effect inside the same program. -/
theorem record_lor (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) :
    𝒟[winningView setup.source.crypto wire serverKeyId budget filter guess target <$>
      RegistrationNativeRecordPackage.ctx (fun _ => .random) setup (RegistrationNativeWire.ledgerCodec wire) route
        (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate
          provider providerState selectedOwner selectedAccept bounds .P adversary)] {true} =
      2⁻¹ * 𝒟[eligibleView setup.source.crypto wire serverKeyId budget filter target <$>
        RegistrationNativeRecordPackage.ctx (fun _ => .random) setup (RegistrationNativeWire.ledgerCodec wire) route
          (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate
            provider providerState selectedOwner selectedAccept bounds .P adversary)] {true} := by
  rw [RegistrationNativeSelectiveRecordViewSource.ideal_source]
  simp only [Functor.map_map]
  exact startup_lor setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept
    bounds adversary budget filter guess target CtxPrivate.initial

end BeaconcryptCore.Computational.RegistrationNativeLorStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorStartup.bind_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorStartup.bind_half
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorStartup.native_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorStartup.native_lor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorStartup.startup_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorStartup.startup_lor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorStartup.record_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorStartup.record_lor
