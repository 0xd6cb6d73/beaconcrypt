-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProductionKeyBound
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformValue
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedMarginal

/-! The production target's one KEM adversary owns the entire unchanged seed/scalar/effectful startup client. Its pure final observation reads only the original value and ledger, retaining the public accepted-prekey equality. The mathematical candidate is absent from the executing client and ignored by this target decision. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProductionPrior
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def decision (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    {source : RegistrationNativeMldsa.Source} (result : RegistrationNativeG3NativeStartupUniformValue.Result source n Value) : Bool :=
  result.2.elim false (fun outcome => RegistrationNativeProductionKeyBound.decision setup wire serverKeyId budget target claim outcome.1.1)

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))

noncomputable def work :=
  RegistrationNativeG3NativeStartupUniformValue.program (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
    target.2.val target.1.val bounds .P adversary

noncomputable def normal : ProbComp Bool :=
  RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
    (simulateQ RegistrationNativeOpenKey.native (decision setup wire serverKeyId budget target claim <$>
      work setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target))

noncomputable def uniform : ProbComp Bool :=
  RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
    (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native (work setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target))
    (fun _ result => decision setup wire serverKeyId budget target claim result) budget.create target.2 false

noncomputable def adversaryKem : PqxdhKemIndCca.OneKeyAdversary setup.kem :=
  RegistrationNativeKemEarlyObservedGame.adversary setup.baseImpl setup.kem
    (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native (work setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target))
    (fun _ result => decision setup wire serverKeyId budget target claim result) budget.create target.2

noncomputable def kemLoss : ℝ :=
  (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
    (adversaryKem setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim).toINDCCA).toReal +
    RegistrationNativeKemEarlyCorrectness.correctnessError setup.baseImpl setup.kem

/-- One whole-client ordinary KEM-CCA advantage and one unconditional correctness error reach the genuine uniform-prior target game. -/
theorem kem_bound (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    (normal setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim).boolDistance
      (uniform setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim) ≤
        kemLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim := by
  have bills := RegistrationNativeG3NativeStartupUniformValue.resource_bounds (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
    target.2.val target.1.val bounds .P adversary budget bounded
  exact RegistrationNativeOpenKeyKemEarlyObservedMarginal.normal_close setup.baseImpl setup.kem functional
    (work setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target)
    (decision setup wire serverKeyId budget target claim) budget.create target.2 bills.1 bills.2

end BeaconcryptCore.Computational.RegistrationNativeProductionPrior
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProductionPrior.kem_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProductionPrior.kem_bound
