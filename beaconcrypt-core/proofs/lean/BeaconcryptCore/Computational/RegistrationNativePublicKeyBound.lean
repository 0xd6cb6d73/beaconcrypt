-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicCaps

/-! The complete generated reference profile has its original build-plus-finish material bill and a computational five-loss key-schedule bound beginning before preparation. The observed event is the broad original CE APP selected-owner subevent. This endpoint does not assume equality to the SDK source profile or a repeated-role hidden-install relation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicKeyBound
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativePublicRetainedStartup (client)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- Real constructor/ML/init/hash draws add no material demand to the original raw adversary allowance. -/
theorem client_bound (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) :
    (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary publicValue).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand (budget.cap 4 + budget.cap 5) := by
  unfold client
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) ?_ ?_).mono (by omega)
  · apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro coin
    simp [RegistrationNativePublicRetained.coins, RegistrationNativeRetainedService.IsDemand, isQueryBoundP_query_iff]
  · intro initialized _reached
    cases initialized.1 with
    | none => trivial
    | some started =>
        apply RegistrationNativePublicCaps.retained_bound
        rw [RegistrationNativePublicRetainedStartup.observed, isQueryBoundP_map_iff]
        exact RegistrationNativePublicCaps.run_bound setup checks wire source
          (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicValue.prekey serverKeyId bounds .P
          (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) budget
          (bounded _) started.frontend

/-- The actual complete reference experiment after its ideal related-root hop has the five primitive losses with no additional scheduling-cap premise. -/
theorem key_bound (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    ((simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      (RegistrationNativePublicStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds budget claim adversary publicValue)).run' ∅).boolDistance
      (RegistrationNativeKeyServiceBound.g2 setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
        (RegistrationNativeRetainedService.client
          (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary publicValue))) ≤
    ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
      (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac
        (RegistrationNativeKeyCompiler.client setup.source
          (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
          (RegistrationNativeRetainedService.client
            (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary publicValue))
          RegistrationNativeKeyPhases.emptyMeta) index) := by
  rw [RegistrationNativePublicRetainedStartup.client_source]
  exact RegistrationNativeRetainedSource.key_bound setup.source setup.hmac correct _ _ _ _
    (client_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary bounded publicValue)

end BeaconcryptCore.Computational.RegistrationNativePublicKeyBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicKeyBound.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicKeyBound.client_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicKeyBound.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicKeyBound.key_bound
