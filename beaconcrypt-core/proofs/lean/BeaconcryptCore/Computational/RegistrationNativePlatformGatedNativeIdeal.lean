-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedLorInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedWeightedInitial
import BeaconcryptCore.Computational.RegistrationNativeLorEntropy
import BeaconcryptCore.Computational.RegistrationNativeWeightedFresh

/-! The actual stateful gated native stage restores the original ledger, test bit and public ML pins before applying the random-record baseline. LR eligibility explicitly includes the physical hidden-test condition; this does not discharge designation provenance for the broader native event. The APP selector and its probability are retained on the same complete execution. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeIdeal
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformGatedNativeEntropy (run reserveLift)
variable {n : Nat} {I KemSK E Failure Value : Type} {base : OracleSpec I}

/-- Exact native hidden-test fairness at any reached cache, cursor and private state. -/
theorem lor (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (env : RegistrationNativeEntropyInterface.Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (created : PqxdhLiveServerConstruction.Created Unit) (initial : E)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : PqxdhRecordLiftIdeal.CtxPrivate n) :
    𝒟[RegistrationNativeLorEntropy.winning setup.source.crypto wire serverKeyId budget filter guess target <$>
      run (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire) route env reserve serverKeyId bounds .P work created initial shell control secret] {true} =
      2⁻¹ * 𝒟[RegistrationNativeLorEntropy.eligible setup.source.crypto wire serverKeyId budget filter target <$>
        run (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire) route env reserve serverKeyId bounds .P work created initial shell control secret] {true} := by
  rw [← RegistrationNativePlatformGatedNativeEntropy.run_transport]
  simp only [Functor.map_map, RegistrationNativeLorEntropy.project_winning, RegistrationNativeLorEntropy.project_eligible]
  exact RegistrationNativePlatformGatedLorInitial.lor setup (RegistrationNativeWire.ledgerCodec wire) route
    (RegistrationNativeEntropyPort.environment env) (reserveLift reserve) serverKeyId bounds
    (RegistrationNativeEntropyCompile.compile .P work) (RegistrationNativeLorEntropy.analysisDecision guess)
    (RegistrationNativeLorEntropy.analysisEligible setup.source.crypto wire serverKeyId budget filter target)
    created (((([], initial), shell), control), secret)

/-- Exact selector-weighted native fresh guessing, retaining its original claim and selector mass. -/
theorem fresh_bytes (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (env : RegistrationNativeEntropyInterface.Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : RegistrationNativeCanonicalSelector.Target budget)
    (created : PqxdhLiveServerConstruction.Created Unit) (initial : E)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : PqxdhRecordLiftIdeal.CtxPrivate n) :
    𝒟[RegistrationNativeWeightedFresh.winning setup.source.crypto wire serverKeyId budget claim target <$>
      run (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire) route env reserve serverKeyId bounds .P work created initial shell control secret] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[RegistrationNativeWeightedFresh.selection setup.source.crypto wire serverKeyId budget claim target <$>
          run (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire) route env reserve serverKeyId bounds .P work created initial shell control secret] {true} := by
  rw [← RegistrationNativePlatformGatedNativeEntropy.run_transport]
  simp only [Functor.map_map, RegistrationNativeWeightedFresh.project_winning, RegistrationNativeWeightedFresh.project_selection]
  exact RegistrationNativePlatformGatedWeightedInitial.fresh_bytes setup (RegistrationNativeWire.ledgerCodec wire) route
    (RegistrationNativeEntropyPort.environment env) (reserveLift reserve) serverKeyId bounds
    (RegistrationNativeEntropyCompile.compile .P work) claim
    (RegistrationNativeCanonicalSelector.analysisSelector setup.source.crypto wire serverKeyId budget claim target)
    created (((([], initial), shell), control), secret)

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeIdeal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeIdeal.lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeIdeal.lor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeIdeal.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeIdeal.fresh_bytes
