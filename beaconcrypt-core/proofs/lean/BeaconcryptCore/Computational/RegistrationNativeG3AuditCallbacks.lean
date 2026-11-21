-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditQuiet
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore

/-! The actual selective callback interpreter can emit a materialized hidden installation only for the literal hidden installation callback itself. Preparation, demand, current signing/publication, routed KEM and records preserve the audited used-map and flag. Their footprints are derived from the actual source ASTs, including failure branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditCallbacks
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State handler onBase onKeys)
open RegistrationNativeG3KnownWorldFrameCore (Allowed)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
open RegistrationNativeHiddenAllocationCore (mapped simulation)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def Quiet : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer _ _ (.hidden _))))))) => False
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon _ _ (.hidden _))))))) => False
  | _ => True

private theorem all_true {Index Result : Type} {spec : OracleSpec Index} (work : OracleComp spec Result) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩

private theorem coins (work : ProbComp Value) :
    AllQueriesSatisfy (simulateQ (PqxdhRecordLiftInterface.coinLift (n := n)) work) Allowed := by
  apply simulation _ (fun _ => True) Allowed _ work (all_true work)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem environment (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (bounded : ∀ role, work.IsQueryBoundP (InstallEnv role) 0) :
    AllQueriesSatisfy (simulateQ PqxdhRecordLiftInterface.effectLift work) Allowed := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      have head := fun role => (isQueryBoundP_query_bind_iff _ _ _ _).mp (bounded role)
      have quiet : ∀ role, ¬ InstallEnv role query := fun role => (head role).1.resolve_right (by omega)
      simp only [simulateQ_bind, simulateQ_spec_query]
      apply allQueriesSatisfy_bind
      · apply (allQueriesSatisfy_query_iff _ _).mpr
        cases query with
        | inl coin => trivial
        | inr capability => cases capability with
          | installServer keyId binding kernel => exact False.elim (quiet .server rfl)
          | installBeacon owner shell kernel => exact False.elim (quiet .beacon rfl)
          | _ => simp [Allowed, RegistrationNativeSeedDelayFrames.ReadsSeed]
      · intro reply
        exact ih reply (fun role => by simpa only [Nat.zero_sub, ite_self] using (head role).2 reply)

/-- The actual selective callback has no hidden World installation unless its original low callback is that literal installation. -/
theorem query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (request : (Spec n KemSK).Domain) (before : State n KemSK ProviderState) (quiet : Quiet request) :
    AllQueriesSatisfy ((handler setup wire sign seed scalar candidate provider request).run before) Allowed := by
  rcases request with (prepare | (demand | (publication | effects)) | kem) | record
  · simp only [handler, onBase, RegistrationNativeHiddenInterpreter.handler,
      RegistrationNativeHiddenInterpreter.onKeys, RegistrationNativeHiddenService.prepare,
      StateT.run, simulateQ_pure, map_pure]
    trivial
  · simp only [handler, onKeys, StateT.run]
    apply mapped
    apply environment
    intro role
    apply IsQueryBoundP.of_imp _ (RegistrationNativeSelectiveHiddenServiceInvariant.demand_free setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate demand (before.1.keys, before.2))
    intro query counted
    cases query with
    | inl coin => exact counted.elim
    | inr capability => trivial
  · simp only [handler, onBase, RegistrationNativeHiddenInterpreter.handler,
      RegistrationNativeHiddenInterpreter.publication, StateT.run]
    apply mapped
    apply mapped
    exact environment _ (fun role => RegistrationNativeSecretWordAtomInstallCompiler.publication_free role setup.source wire.frameWrite sign publication before.1.receipts)
  · change AllQueriesSatisfy
      ((onBase (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider
        (.inl (.inr (.inl (.inr (.inr effects))))))).run before) Allowed
    simp only [onBase, StateT.run]
    apply mapped
    change AllQueriesSatisfy ((RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider
      (.inl (.inr (.inl (.inr (.inr effects)))))).run before.1) Allowed
    rw [RegistrationNativeHiddenInterpreter.effect_query]
    apply mapped
    apply (allQueriesSatisfy_query_iff _ _).mpr
    cases effects with
    | inl coin => trivial
    | inr capability => cases capability with
      | installServer keyId binding kernel | installBeacon owner shell kernel =>
          cases kernel with
          | known kernel => intro impossible; cases impossible
          | hidden slot => exact quiet.elim
      | _ => simp [Allowed, RegistrationNativeSeedDelayFrames.ReadsSeed]
  · simp only [handler, onBase, RegistrationNativeHiddenInterpreter.handler,
      RegistrationNativeHiddenInterpreter.routed, StateT.run]
    apply mapped
    apply mapped
    exact coins _
  · change AllQueriesSatisfy ((onBase (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider (.inr record))).run before) Allowed
    simp only [onBase, StateT.run]
    apply mapped
    change AllQueriesSatisfy ((RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider (.inr record)).run before.1) Allowed
    rw [RegistrationNativeHiddenInterpreter.record_query]
    exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)

end BeaconcryptCore.Computational.RegistrationNativeG3AuditCallbacks
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditCallbacks.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditCallbacks.query
