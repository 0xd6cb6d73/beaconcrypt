-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeRepeatBound

/-! The actual cold marked G3 repeat audit is bounded through its same complete original G2 trace. The literal real reserved KEM provider and its explicit real first-getter challenge are sampled once; every material table, record seed and reached startup World/cache stays in the source. Original Respects and actual cold frontend fields discharge all internal resource/lifecycle obligations. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeAuditRepeatBound
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
  let _ ← $ᵗ MlKemSharedSecret
  let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
  let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
  let result ← RegistrationNativeG3AuditRepeatEvent.original setup (RegistrationNativeWire.ledgerCodec wire) route seeds wire sign seed scalar pair.2
    (RegistrationNativeOpenKeyKemEarlyRealSource.provider setup.baseImpl setup.kem (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 pair.2)
    checks source selected.val selectedAccept publicPrekey serverKeyId bounds mode work (front.eval RegistrationNativeSecretWordMessage.zero)
    (RegistrationNativeHiddenInterpreter.initial none, ∅) (RegistrationNativeG3LocalMaterialCompletedSource.cache materials) world
  pure result.2.2

/-- Every actual marked cold G3 audit is bounded by the same candidate-observed full G2 execution of its actual real KEM provider and complete original ledger. -/
theorem audit_le_real (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (selected : Fin (budget.create + 1)) (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (unused : ∀ slot role, world.used slot role = false) :
    Pr{let marked ← audit setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front budget selected world}[marked = true] ≤
      Pr{let repeated ← (RegistrationNativeG3NativeRepeatBound.real setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front
        (ordinary world) budget selected)}[repeated = true] := by
  classical
  unfold audit RegistrationNativeG3NativeRepeatBound.real RegistrationNativeOpenKeyKemEarlyObservedReal.source
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun chosen => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun others => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pair => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun unusedDraw => ?_
  rw [prEvent_map, RegistrationNativeOpenKeyKemEarlyRealSource.reference, reference_values]
  have point := RegistrationNativeG3AuditRepeatOpenKey.bound setup wire route sign seed scalar pair.2 checks source
    selected.val selectedAccept publicPrekey serverKeyId bounds mode work (front.eval RegistrationNativeSecretWordMessage.zero)
    budget bounded
    (RegistrationNativeOpenKeyKemEarlyRealSource.provider setup.baseImpl setup.kem (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 pair.2)
    (RegistrationNativeHiddenInterpreter.initial none) world unused
  simp only [RegistrationNativeG3NativeRepeatBound.program, RegistrationNativeG3NativeCheckedUniformSource.openProgram,
    RegistrationNativeG3MaterializedRetainedLazy.client, RegistrationNativeG3MaterializedRetainedSource.ordinary,
    RegistrationNativeG3NativeRepeatUniformBound.observation, RegistrationNativeG3AuditRepeatOpenKey.Event,
    ordinary, RegistrationNativeHiddenInterpreter.initial, decide_eq_true_eq] at point ⊢
  convert point using 1; rfl

/-- The actual marked audit has one ordinary KEM-CCA advantage, one unconditional correctness error and twice one explicit whole-prior suffix-key recovery loss, preserving the actual startup cache. -/
theorem bound (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (selected : Fin (budget.create + 1)) (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (unused : ∀ slot role, world.used slot role = false)
    (sessions : front.server.sessions = []) (parsed : front.parsedAccepts = 0) (owners : front.beacons = []) :
    Pr{let marked ← audit setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front budget selected world}[marked = true] ≤
      RegistrationNativeG3NativeRepeatBound.loss setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front
        (ordinary world) budget selected :=
  (audit_le_real setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front budget bounded selected world unused).trans
    (RegistrationNativeG3NativeRepeatBound.bound setup checks wire source route sign selectedAccept publicPrekey serverKeyId bounds mode seed scalar work front
      (ordinary world) functional budget bounded selected sessions parsed owners)

end BeaconcryptCore.Computational.RegistrationNativeG3NativeAuditRepeatBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeAuditRepeatBound.audit_le_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeAuditRepeatBound.audit_le_real
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeAuditRepeatBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeAuditRepeatBound.bound
