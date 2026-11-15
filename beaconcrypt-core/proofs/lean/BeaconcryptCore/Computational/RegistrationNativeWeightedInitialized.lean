-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordWeightedInitial
import BeaconcryptCore.Computational.RegistrationNativeWeightedFresh
import BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized

/-! Weighted guessing after actual initialized native startup. The exact cursor, counters and CTX cache reached by the constructor are retained. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeWeightedInitialized
open RegistrationNativeCanonicalSelector (Target analysisSelector)
open RegistrationNativeWeightedFresh (selection winning project_selection project_winning)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK E Value Reader Response : Type} {base : OracleSpec ι}
/-- Native selector-weighted entropy retains the original messages and complete execution, with the same selector probability on the right. -/
theorem fresh_bytes (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (env : RegistrationNativeEntropyInterface.Environment n E)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : PqxdhRecordLiftIdeal.CtxPrivate n) :
    𝒟[winning setup.source.crypto wire serverKeyId budget claim target <$>
      RegistrationNativeEntropyInitialized.run (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire)
        route env serverKeyId bounds .P work created initial shell control secret] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[selection setup.source.crypto wire serverKeyId budget claim target <$>
          RegistrationNativeEntropyInitialized.run (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire)
            route env serverKeyId bounds .P work created initial shell control secret] {true} := by
  rw [← RegistrationNativeEntropyInitialized.run_transport]
  simp only [Functor.map_map, project_winning, project_selection]
  exact CborRawRecordWeightedInitial.fresh_bytes setup (RegistrationNativeWire.ledgerCodec wire) route
    (RegistrationNativeEntropyPort.environment env) serverKeyId bounds
    (RegistrationNativeEntropyCompile.compile .P work) claim
    (analysisSelector setup.source.crypto wire serverKeyId budget claim target) created (((([], initial), shell), control), secret)

end BeaconcryptCore.Computational.RegistrationNativeWeightedInitialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedInitialized.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedInitialized.fresh_bytes
