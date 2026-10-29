-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyNativeGuesser

/-! The raw anomaly CCA predictor owns its dummy secret and every nonselected KEM key, receives only the selected public key and its decapsulation oracle, and executes the original raw secrecy ledger. Its output is the actual raw transcript's preselected successful-finish ciphertext. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyGuesser
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemCCAOracleSpec)
open PqxdhPrivateKemSource (ccaCoins evalKem)
open PqxdhInitializerSecrecy (kemAmbientImpl)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

noncomputable def guesser (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (publicKey : MlKem768PublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKem768Ciphertext) := do
  let dummy ← ccaCoins (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  let others ← ccaCoins (PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count)
  let born ← ccaCoins ((PqxdhLiveServerConstruction.construct setup.joint ensureInit 0 setup.serverKeyId none).run runtime)
  match born.1 with
  | none => pure none
  | some created => do
      let result ← (simulateQ (CborRawAnomalyNativeGuesser.native setup wire parse checks target
        ⟨(publicKey, dummy.2), others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ created)
        (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
          setup.serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode adversary))).run
            (PqxdhDeploymentNative.initial created)
      pure (PqxdhDeploymentIdealGuess.guessCt (CborTaggedSimulation.boundaryWire wire parse)
        target result.1.2.transcript)

end BeaconcryptCore.Computational.CborRawAnomalyGuesser
