-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasOuterRepeatBound
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource
import BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatOpenKey

/-! The actual candidate-retaining ordinary KEM uniform branch has one whole-context suffix-key recovery adversary. Its candidate-independent alias code samples the actual key family/challenge prior internally, retaining target multiplicity and the same evaluated original G2 trace. Original Respects supplies every material bill and the actual cold lifecycle facts supply same-run literal exposure. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatUniformBound
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeSecretWordAliasOuter (Profile)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
attribute [local irreducible] uniformSample RegistrationNativeSuffixKeyPrf.value

noncomputable def prior (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (count : Nat) (selected : Fin (count + 1)) : ProbComp (Profile KemSK) := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  pure ⟨List.ofFn (selected.insertNth chosen others), chosen.1, pair.1⟩

noncomputable def observation (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    {source : RegistrationNativeMldsa.Source} : MlKemSharedSecret → RegistrationNativeG3NativeCheckedUniformSource.Result source Value → Bool := by
  classical
  exact fun candidate result => decide (RegistrationNativeG3AuditRepeatOpenKey.Event setup seed scalar candidate result)

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
  (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativeSecretWordMessage.State source) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)

noncomputable def actual (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) :=
  RegistrationNativeSecretWordAliasOuter.client setup checks wire source route sign seed scalar selected.val selectedAccept publicPrekey serverKeyId
    bounds mode work front ordinary (RegistrationNativeSecretWordKemPool.empty, none) (prior setup.baseImpl setup.kem budget.create selected)

private theorem bytes_source (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) :
    RegistrationNativeSecretWordRecoveryBound.bytesView setup.source
      (fun candidate result => observation setup seed scalar candidate (RegistrationNativeG3NativeCheckedAliasSource.view candidate result.1))
      (actual setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front ordinary budget selected) =ᵈ
      RegistrationNativeG3NativeCheckedUniformSource.bytesView setup checks wire source route sign selected.val selectedAccept publicPrekey serverKeyId
        bounds mode seed scalar (setup.joint.staticDh seed (setup.dh.publicKey scalar)) work front ordinary budget selected (observation setup seed scalar) := by
  have outer := RegistrationNativeSecretWordAliasOuter.bytesView_source setup checks wire source route sign seed scalar selected.val selectedAccept publicPrekey serverKeyId
    bounds mode work front ordinary (RegistrationNativeSecretWordKemPool.empty, none) (prior setup.baseImpl setup.kem budget.create selected)
    (fun candidate result => observation setup seed scalar candidate (RegistrationNativeG3NativeCheckedAliasSource.view candidate result.1))
  refine outer.trans ?_
  unfold prior RegistrationNativeG3NativeCheckedUniformSource.bytesView
  simp only [bind_assoc, pure_bind]
  exact .rfl

attribute [local irreducible] actual prior

/-- The complete candidate-retaining ordinary KEM uniform branch pays twice one explicit recovery advantage for the whole actual KEM context, with original numerical allowances. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (selected : Fin (budget.create + 1))
    (sessions : front.server.sessions = []) (parsed : front.parsedAccepts = 0) (owners : front.beacons = []) :
    Pr{let result ← (RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (RegistrationNativeG3NativeCheckedUniformSource.openProgram setup checks wire source route sign selected.val selectedAccept publicPrekey serverKeyId
          bounds mode seed scalar (setup.joint.staticDh seed (setup.dh.publicKey scalar)) work front ordinary))
      (observation setup seed scalar) budget.create selected false)}[result = true] ≤
      2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source
          (RegistrationNativeSecretWordRecoveryCompiler.guesses
            (actual setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front ordinary budget selected)))) +
      (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
      (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹) := by
  have sourceEq := RegistrationNativeG3NativeCheckedUniformSource.uniform_source setup checks wire source route sign selectedAccept publicPrekey serverKeyId
    bounds mode seed scalar (setup.joint.staticDh seed (setup.dh.publicKey scalar)) work front ordinary sessions budget bounded selected (observation setup seed scalar)
  rw [sourceEq.prEvent_eq (fun result => result = true), ← (bytes_source setup checks wire source route sign selectedAccept publicPrekey serverKeyId
    bounds mode seed scalar work front ordinary budget selected).prEvent_eq (fun result => result = true)]
  have estimated := RegistrationNativeSecretWordAliasOuterRepeatBound.bytes_bound setup checks wire source route sign seed scalar selected.val selectedAccept publicPrekey serverKeyId
    bounds mode work front ordinary (RegistrationNativeSecretWordKemPool.empty, none) (prior setup.baseImpl setup.kem budget.create selected)
    budget bounded sessions parsed owners rfl
  simpa only [RegistrationNativeSecretWordRecoveryBound.bytesView, map_bind, bind_pure_comp, Functor.map_map, prEvent_map, observation,
    RegistrationNativeG3AuditRepeatOpenKey.Event, RegistrationNativeG3NativeCheckedAliasSource.view,
    RegistrationNativeSecretWordCheckedTrace.state, Prod.map, id_eq, decide_eq_true_eq, actual] using estimated

end BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatUniformBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatUniformBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatUniformBound.bound
