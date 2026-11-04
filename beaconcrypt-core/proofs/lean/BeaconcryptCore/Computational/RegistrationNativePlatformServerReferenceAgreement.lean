-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerReferencePrefix
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Private interpretation of the public root-reference agreement restores the actual earlier root through the selected primitive functional relation. The executable client receives only its reference; the complete shared platform state and native Local poststate are retained. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAgreement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationServerReferenceRoot (Ready PrepareSpec)
open RegistrationNativePlatformServerReferencePrefix
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def prepareSource (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) : QueryImpl PrepareSpec (StateT (PqxdhRecordLiftWorld.State n) m) :=
  fun message => pure ((RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message).map fun _ => message)

theorem prepare_source (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp PrepareSpec Value) (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ (prepareSource setup seed scalar) work).run before =
      (fun value => (value, before)) <$>
        simulateQ coins (simulateQ (RegistrationServerReferenceSourceClient.prepare setup.source setup.joint setup.dh seed scalar) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, prepareSource, RegistrationServerReferenceSourceClient.prepare,
      pure_bind]
    exact ih _

private theorem close_pure (value : Value) (before : RegistrationServerReferenceCompilerNative.Local n) :
    (closeEnvironment (pure value : StateT Environment (StateT (PqxdhRecordLiftWorld.State n) m) Value)).run before = pure (value, before) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$> (pure ((value, before.1), before.2) : m _) = _
  simp only [map_pure]

theorem agreement_source (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerReferenceCompilerNative.Local n) :
    Prod.map id RegistrationWorldAgreementProgramCompiler.project <$>
      (closeEnvironment (localAgreement (effects coins) (prepareSource setup seed scalar) setup checks packet authenticated)).run before =
      simulateQ coins ((RegistrationServerReferenceSourceStage.referenceStage setup checks seed scalar packet authenticated).run
        (RegistrationWorldAgreementProgramCompiler.project before)) := by
  unfold localAgreement RegistrationServerReferenceSourceStage.referenceStage
  rw [close_bind, StateT.run_bind, map_bind]
  simp only [StateT.run_bind, simulateQ_bind]
  rw [← collect_source coins setup checks packet authenticated before, bind_map_left]
  apply bind_congr
  rintro ⟨input, current⟩
  cases input with
  | none => simp only [close_pure, Prod.map, id_eq, StateT.run_pure, simulateQ_pure, map_pure]
  | some input =>
    rw [close_lift, prepare_source coins]
    simp only [StateT.run_lift, bind_pure_comp, simulateQ_map, Functor.map_map, Prod.map, id_eq]


theorem native (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (control : pqxdh.ServerState) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerReferenceCompilerNative.Local n) :
    Prod.map (RegistrationServerReferenceSourceClient.restore
      (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar))
      RegistrationWorldAgreementProgramCompiler.project <$>
      (closeEnvironment (localAgreement (effects coins) (prepareSource setup seed scalar) setup checks packet authenticated)).run before =
    simulateQ coins ((simulateQ (RegistrationWorldAgreement.agreement setup.source
      (RegistrationServerRoleBackend.native setup checks representation seed))
      (RegistrationAgreementExecutor.server control .Fresh authenticated)).run
      (RegistrationWorldAgreementProgramCompiler.project before)) := by
  have compared := congrArg (fun work => Prod.map (RegistrationServerReferenceSourceClient.restore
      (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar)) id <$> work)
    (agreement_source coins setup checks seed scalar packet authenticated before)
  rw [← simulateQ_map, RegistrationServerReferenceSourceStage.reference_native setup checks representation correct
    seed scalar control packet authenticated (RegistrationWorldAgreementProgramCompiler.project before)] at compared
  simpa only [Functor.map_map, Prod.map_def, id_eq] using compared

end BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAgreement.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAgreement.prepare_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAgreement.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAgreement.agreement_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAgreement.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAgreement.native
