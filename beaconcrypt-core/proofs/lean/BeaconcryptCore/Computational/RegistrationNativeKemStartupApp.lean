-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemStartupSource
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical

/-! The original native CE-APP event has a concrete whole-startup selected-KEM reduction at its single parsed-accept by owner target. This is the KEM hop to the explicit total uniform hybrid; target-to-hidden-root identification and the final record bound are separate obligations. Inactive dummy-ciphertext substitution remains part of this hybrid. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemStartupApp
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeWire (Wire)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

noncomputable def decision (setup : Setup base KemSK) (wire : Wire) (serverKeyId : U64)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (observed : Value × RegistrationNativeLedger.State) : Bool :=
  RegistrationNativeParsedTargetCanonical.event setup.source.crypto wire serverKeyId budget target claim
    (observed.1, (observed.2, ()))

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
  (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
  (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))

noncomputable def adversary : PqxdhKemIndCca.OneKeyAdversary setup.kem :=
  RegistrationNativeKemStartupGame.adversary (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
    bounds mode work budget target.1.val target.2 0 (decision setup wire serverKeyId budget target claim)

noncomputable def hybrid : ProbComp Bool :=
  RegistrationNativeKemStartupGame.hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
    bounds mode work budget target.1.val target.2 0 (decision setup wire serverKeyId budget target claim) false

/-- Original native canonical CE-APP, with actual startup and literal secrecy draws, admits one ordinary selected-KEM hop and one correctness error. -/
theorem app_hop (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (bounded : ∀ publicState, RegistrationNativeInterface.Respects budget (work publicState)) :
    (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work (RegistrationNativeParsedTargetCanonical.event setup.source.crypto wire serverKeyId budget target claim)).boolDistance
      (hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode work budget target claim) ≤
    (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
      (adversary (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode work budget target claim).toINDCCA).toReal +
      RegistrationNativeKemTotalCorrectness.correctnessError setup.baseImpl setup.kem := by
  exact RegistrationNativeKemStartupSource.source_close (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
    bounds mode functional work budget bounded target.1.val target.2 0 (decision setup wire serverKeyId budget target claim)

end BeaconcryptCore.Computational.RegistrationNativeKemStartupApp

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemStartupApp.app_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemStartupApp.app_hop
