-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatBound

/-! The actual cold marked G3 repeat audit is bounded through its same complete original G2 trace. The uniform reserved KEM provider and the mathematical candidate are sampled once; every material table, record seed and reached startup World/cache stays in the source. This comparison stays entirely on the uniform side and adds no KEM loss. Original Respects and actual cold frontend fields discharge all internal resource/lifecycle obligations. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformAuditBound
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
attribute [local irreducible] uniformSample RegistrationNativeSuffixKeyPrf.value

noncomputable def ordinary {n : Nat} (world : PqxdhRecordLiftWorld.State n) : RegistrationNativePublicInterpreter.State n KemSK :=
  ⟨RegistrationNativeReferenceInterpreter.initial, world, PqxdhLiveKemBirth.empty, []⟩

private theorem reference_values {A P : Type}
    (provider : RegistrationNativeSecretWordNativePlain.NativeProvider KemSK P)
    (work : OracleComp (RegistrationNativeOpenKey.Spec KemSK) A) (state : P)
    (table : RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ ((PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase
        (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)).flattenStateT) work).run' (state, table) =
      (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work).run' state)).run' table := by
  have actual := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT PqxdhRegistrationJointKemSecondEntry.lazyImpl
    (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work state table
  have observed := congrArg (Functor.map (fun result => result.1.1)) actual
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using observed.symm

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
  (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativeSecretWordMessage.State source)

noncomputable def audit (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) budget.create
  let pair ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let candidate ← $ᵗ MlKemSharedSecret
  let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
  let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
  let result ← RegistrationNativeG3AuditRepeatEvent.original setup (RegistrationNativeWire.ledgerCodec wire) route seeds wire sign seed scalar candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 candidate)
    checks source selected.val selectedAccept publicPrekey serverKeyId bounds mode work (front.eval RegistrationNativeSecretWordMessage.zero)
    (RegistrationNativeHiddenInterpreter.initial none, ∅) (RegistrationNativeG3LocalMaterialCompletedSource.cache materials) world
  pure result.2.2

noncomputable def uniform (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) : ProbComp Bool :=
  RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
    (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native
      (RegistrationNativeG3NativeRepeatBound.program setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front (ordinary world) selected.val))
    (RegistrationNativeG3NativeRepeatUniformBound.observation setup seed scalar) budget.create selected false

noncomputable def loss (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) : ℝ≥0∞ :=
  2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
    (RegistrationNativeSuffixKeyRecovery.adversary setup.source
      (RegistrationNativeSecretWordRecoveryCompiler.guesses
        (RegistrationNativeG3NativeRepeatUniformBound.actual setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front (ordinary world) budget selected)))) +
    (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ +
    (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹)

/-- The actual marked audit is compared directly on the uniform KEM side to the same candidate-observed original G2 trace. -/
theorem audit_le_uniform (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (selected : Fin (budget.create + 1)) (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (unused : ∀ slot role, world.used slot role = false) :
    Pr{let marked ← audit setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front budget selected world}[marked = true] ≤
      Pr{let repeated ← uniform setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front budget selected world}[repeated = true] := by
  classical
  have bills := RegistrationNativeG3NativeCheckedUniformSource.resource_bounds setup checks wire source route sign selected.val selectedAccept publicPrekey serverKeyId
    bounds mode seed scalar (setup.joint.staticDh seed (setup.dh.publicKey scalar)) work front (ordinary world) budget bounded
  have sourceEq := RegistrationNativeOpenKeyKemEarlyObservedUniform.uniform_source setup.baseImpl setup.kem
    (RegistrationNativeG3NativeRepeatBound.program setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front (ordinary world) selected.val)
    (RegistrationNativeG3NativeRepeatUniformBound.observation setup seed scalar) budget.create selected bills.1 bills.2
  unfold uniform
  rw [sourceEq.prEvent_eq (fun repeated => repeated = true)]
  unfold audit RegistrationNativeOpenKeyKemEarlyObservedUniform.source
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun chosen => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun others => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pair => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun candidate => ?_
  rw [prEvent_map, RegistrationNativeOpenKeyKemEarlySource.reference, reference_values]
  have point := RegistrationNativeG3AuditRepeatOpenKey.bound setup wire route sign seed scalar candidate checks source
    selected.val selectedAccept publicPrekey serverKeyId bounds mode work (front.eval RegistrationNativeSecretWordMessage.zero)
    budget bounded
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 candidate)
    (RegistrationNativeHiddenInterpreter.initial none) world unused
  simp only [RegistrationNativeG3NativeRepeatBound.program, RegistrationNativeG3NativeCheckedUniformSource.openProgram,
    RegistrationNativeG3MaterializedRetainedLazy.client, RegistrationNativeG3MaterializedRetainedSource.ordinary,
    RegistrationNativeG3NativeRepeatUniformBound.observation, RegistrationNativeG3AuditRepeatOpenKey.Event,
    ordinary, RegistrationNativeHiddenInterpreter.initial, decide_eq_true_eq] at point ⊢
  convert point using 1; rfl

/-- The actual uniform-side marked G3 audit pays twice one whole-prior recovery loss and no additional KEM loss. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (selected : Fin (budget.create + 1)) (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (unused : ∀ slot role, world.used slot role = false)
    (sessions : front.server.sessions = []) (parsed : front.parsedAccepts = 0) (owners : front.beacons = []) :
    Pr{let marked ← audit setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front budget selected world}[marked = true] ≤
      loss setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front budget selected world := by
  apply (audit_le_uniform setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front budget bounded selected world unused).trans
  exact RegistrationNativeG3NativeRepeatUniformBound.bound setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front (ordinary world)
    budget bounded selected sessions parsed owners

end BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformAuditBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformAuditBound.audit_le_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformAuditBound.audit_le_uniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformAuditBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformAuditBound.bound
