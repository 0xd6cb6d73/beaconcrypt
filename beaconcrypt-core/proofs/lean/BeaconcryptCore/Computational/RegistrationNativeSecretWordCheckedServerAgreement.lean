-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparationProgram

/-! The actual ordered Server collector and checked root capability compose without exposing the selected word. Every reached local environment and optional preparation failure is retained before the one-use session is stored. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAgreement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message input ServerState)
open RegistrationNativeSecretWordChecked (Spec native implementation)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- The concrete collector equality retains the actual current environment and all optional exits. -/
theorem collect (setup : Setup base KemSK) (checks : Checks)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Environment) :
    simulateQ (native (n := n) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated).run before) =
      Prod.map (Option.map (RegistrationNativeSecretWordServerCollect.eval candidate)) id <$>
        simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated).run before) := by
  unfold native
  rw [QueryImpl.simulateQ_compose, RegistrationNativeSecretWordServerSource.collector_source, simulateQ_map]

attribute [local irreducible] RegistrationNativeKemReferenceCompiler.collect
  RegistrationNativeSecretWordServerCompiler.collect RegistrationServerReferenceRoot.client
  RegistrationNativeSecretWordServerRoot.client RegistrationNativeSecretWordChecked.native
  RegistrationNativeSecretWordChecked.implementation

/-- The actual Server agreement combines the native collector with its checked echo preparation and restores the entire state. -/
theorem agreement (setup : Setup base KemSK) (checks : Checks)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment) :
    simulateQ (native (n := n) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run (before.eval candidate)).run env) =
      (fun result => ((RegistrationNativeSecretWordServerRoot.restore candidate result.1.1, result.1.2.eval candidate), result.2)) <$>
        simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          (((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before).run env) := by
  simp only [RegistrationServerOpenReferenceCompiler.agreement, RegistrationNativeSecretWordServerCompiler.agreement,
    StateT.run_bind, StateT.run_lift, StateT.run_pure, simulateQ_bind, map_bind]
  rw [collect setup checks inside candidate seed scalar packet authenticated env, bind_map_left]
  simp only [simulateQ_pure, bind_pure_comp, bind_map_left]
  apply bind_congr
  intro reached
  cases selected : reached.1 with
  | none =>
      simp only [Prod.map, selected, Option.map_none, StateT.run_pure, simulateQ_pure, map_pure, RegistrationNativeSecretWordServerRoot.restore]
      rfl
  | some collected =>
      simp only [Prod.map, selected, Option.map_some, StateT.run_map, StateT.run_lift, bind_pure_comp, simulateQ_map, Functor.map_map]
      rw [RegistrationNativeSecretWordCheckedPreparationProgram.server setup.source inside candidate
        setup.joint setup.dh seed scalar authenticated.binding collected]
      simp only [Functor.map_map, id_eq]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAgreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAgreement.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAgreement.collect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAgreement.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAgreement.agreement
