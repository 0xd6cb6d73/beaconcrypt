-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWeightedInitialized
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyStartup

/-! The weighted native entropy bound averages actual effectful startup rather than replacing it by a cold state. Both the winning event and selector mass retain the same startup distribution. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeWeightedStartup
open RegistrationNativeCanonicalSelector (Target analysisSelector)
open RegistrationNativeWeightedFresh (selection winning)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open PqxdhRecordLiftIdeal (CtxPrivate ctxInterpreter)
open RegistrationNativeSelectiveEntropyStartup (run after run_start)
open RegistrationNativeSelectiveEntropyRun (nativeRun)
open RegistrationNativeSelectiveEntropyEnvironment (State)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

theorem bind_weighted {A B : Type} (startup : ProbComp A) (next : A → ProbComp B)
    (win select : B → Prop) (epsilon : ℝ≥0∞)
    (bound : ∀ started ∈ support startup,
      Pr{let result ← next started}[win result] ≤ epsilon * Pr{let result ← next started}[select result]) :
    Pr{let result ← startup >>= next}[win result] ≤
      epsilon * Pr{let result ← startup >>= next}[select result] := by
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun started => ?_
  by_cases supported : started ∈ support startup
  · calc _ ≤ Pr{let result ← startup}[result = started] *
        (epsilon * Pr{let result ← next started}[select result]) := mul_le_mul' le_rfl (bound started supported)
      _ = _ := by ac_rfl
  · have zero := prEvent_eq_zero_of_not_mem_support startup supported
    rw [zero]
    simp only [zero_mul, mul_zero, le_refl]

/-- Actual thin native record-ideal fresh guessing retains its byte-accurate entropy term and full original ledger. -/
theorem fresh_bytes (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (targetBudget : PqxdhDeploymentInterface.Budget)
    (target : Target targetBudget) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (before : State n KemSK ProviderState source) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (valid : RegistrationNativeSelectiveAllocationJoint.Holds (((before, shell), control), secret)) :
    𝒟[winning setup.source.crypto wire serverKeyId targetBudget claim target <$>
      nativeRun (fun _ => .random) id setup checks wire (RegistrationNativeWire.ledgerCodec wire) route source credential seed scalar candidate provider selectedOwner selectedAccept
        serverKeyId bounds .P work created before shell control secret] {true} ≤ ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
      𝒟[selection setup.source.crypto wire serverKeyId targetBudget claim target <$>
        nativeRun (fun _ => .random) id setup checks wire (RegistrationNativeWire.ledgerCodec wire) route source credential seed scalar candidate provider selectedOwner selectedAccept
          serverKeyId bounds .P work created before shell control secret] {true} := by
  rw [RegistrationNativeSelectiveEntropyRun.run_source (fun _ => .random) id setup checks wire route source credential seed scalar candidate provider selectedOwner selectedAccept
    serverKeyId bounds .P work created before shell control secret valid]
  exact RegistrationNativeWeightedInitialized.fresh_bytes setup wire route _ serverKeyId bounds targetBudget work claim target created before shell control secret

/-- The complete actual native mode-P program has byte-accurate fresh entropy after its actual effectful initialization and ML pin hash. -/
theorem startup_bytes (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (targetBudget : PqxdhDeploymentInterface.Budget)
    (target : Target targetBudget) (secret : CtxPrivate n) :
    𝒟[winning setup.source.crypto wire serverKeyId targetBudget claim target <$>
      run (n := n) (fun _ => .random) id setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
        selectedOwner selectedAccept bounds .P adversary secret] {true} ≤ ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
      𝒟[selection setup.source.crypto wire serverKeyId targetBudget claim target <$>
        run (n := n) (fun _ => .random) id setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
          selectedOwner selectedAccept bounds .P adversary secret] {true} := by
  simp only [← prEvent_eq_evalDist_singleton _ true, prEvent_map, run_start]
  apply bind_weighted
  intro started supported
  rcases started with ⟨⟨⟨initialized, shell⟩, control⟩, reached⟩
  cases initialized with
  | none => simp [after, winning, selection]
  | some born =>
      dsimp only [after]
      have valid := RegistrationNativeHiddenAllocationStartup.initialized setup ensureInit identityIndex serverKeyId
        (setup.joint.publicKeys seed) providerState
        (ctxInterpreter (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire))
        (RegistrationNativeWire.ledgerCodec wire) route secret born shell control reached supported
      simpa only [← prEvent_eq_evalDist_singleton _ true, prEvent_map] using
        fresh_bytes setup checks wire route source born.native.credential seed scalar candidate provider
          selectedOwner selectedAccept serverKeyId bounds
          (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩) claim targetBudget target born.created
          (born.native.frontend, RegistrationNativeSelectiveHiddenInterpreter.initial providerState) shell control reached valid

end BeaconcryptCore.Computational.RegistrationNativeWeightedStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedStartup.bind_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedStartup.bind_weighted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedStartup.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedStartup.fresh_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedStartup.startup_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedStartup.startup_bytes
