-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemTotalSource
import BeaconcryptCore.Computational.RegistrationNativeKemInitializedSource

/-! The original native raw experiment and original private secrecy ledger have an unconditional selected-KEM hop. Its genuine reserved source and resource bills come from actual startup and controllers. The target-to-root identification is separate; the uniform hybrid explicitly retains candidate substitution on an inactive dummy challenge ciphertext. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemFullTotal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeExperiment (Initial)
open RegistrationNativeWire (Wire)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (parsed : Nat)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    OracleComp (RegistrationNativeKemParsedRouting.Spec n mlSource KemSK) Bool :=
  decision <$> RegistrationNativeKemFullSource.program setup checks wire serverKeyId bounds mode work parsed

noncomputable def real (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (initial : Initial n KemSK source)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :=
  (fun observed => decision (observed.1, observed.2.1)) <$>
    RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state

/-- Actual generated startup and original public caps yield the complete genuine selected-key source for every original ledger decision. -/
theorem initialized_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (parsed : Nat) (selected : Fin (budget.create + 1))
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    EvalDistEq (real setup checks wire route representation source initial bounds mode work decision)
      (RegistrationNativeKemTotalSource.source setup.baseImpl setup.kem
        (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
        (pure (RegistrationNativeKemServerState.project initial.state))
        (client (mlSource := source) setup checks wire initial.created.server.server.metadata.sender bounds mode work parsed decision)
        budget.create selected) := by
  have law := (RegistrationNativeKemInitializedSource.initialized_source setup checks wire route representation source
    ensureInit identityIndex serverKeyId initial started bounds mode work budget bounded parsed selected).map
      (fun observed => (observed.map fun value => decision (value.1, value.2.1)).getD false)
  simpa only [real, client, RegistrationNativeKemTotalSource.source,
    RegistrationNativeKemInitializedSource.reserved, RegistrationNativeKemInitializedSource.observe,
    RegistrationNativeKemDispatcherCompiler.fullProject, simulateQ_map, OptionT.run_map,
    StateT.run_map, map_bind, Functor.map_map, pure_bind, bind_pure_comp, Option.map_some,
    Option.getD_some, RegistrationNativeKemPoolSource.project, Prod.map, id_eq,
    Option.map_map, Function.comp_def] using law

/-- Every original native raw ledger decision has an unconditional ordinary selected-KEM hop with coefficient-one CCA and correctness losses. -/
theorem source_close (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (parsed : Nat) (selected : Fin (budget.create + 1)) (index : Nat)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    (real setup checks wire route representation source initial bounds mode work decision).boolDistance
      (RegistrationNativeKemTotalGame.branch setup.baseImpl setup.kem
        (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
        (pure (RegistrationNativeKemServerState.project initial.state))
        (client (mlSource := source) setup checks wire initial.created.server.server.metadata.sender bounds mode work parsed decision)
        budget.create selected index false) ≤
    (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
      (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
      (RegistrationNativeKemTotalGame.adversary setup.baseImpl setup.kem
        (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
        (pure (RegistrationNativeKemServerState.project initial.state))
        (client (mlSource := source) setup checks wire initial.created.server.server.metadata.sender bounds mode work parsed decision)
        budget.create selected index).toINDCCA).toReal +
      RegistrationNativeKemTotalCorrectness.correctnessError setup.baseImpl setup.kem := by
  have original := initialized_source setup checks wire route representation source ensureInit identityIndex serverKeyId
    initial started bounds mode work budget bounded parsed selected decision
  have reconstruction := RegistrationNativeKemTotalSource.source_real setup.baseImpl setup.kem
    (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
    (pure (RegistrationNativeKemServerState.project initial.state))
    (client (mlSource := source) setup checks wire initial.created.server.server.metadata.sender bounds mode work parsed decision)
    budget.create selected index
  have same := original.trans reconstruction.symm
  have eventEq := same.prEvent_eq (fun result => result = true)
  have bound := RegistrationNativeKemTotalCorrectness.source_close setup.baseImpl setup.kem functional
    (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
    (pure (RegistrationNativeKemServerState.project initial.state))
    (client (mlSource := source) setup checks wire initial.created.server.server.metadata.sender bounds mode work parsed decision)
    budget.create selected index
  simpa only [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton, eventEq] using bound

end BeaconcryptCore.Computational.RegistrationNativeKemFullTotal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullTotal.initialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullTotal.initialized_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullTotal.source_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullTotal.source_close
