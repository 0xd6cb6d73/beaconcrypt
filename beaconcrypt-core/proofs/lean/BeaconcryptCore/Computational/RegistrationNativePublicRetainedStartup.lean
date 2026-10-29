-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicRetained
import BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame

/-! The complete generated native reference experiment, including both roles and the original complete CE ledger, is an actual client of the before-prepare private material service. This composition relocates root bookkeeping only; equality to the SDK source sampling schedule and the hidden-install alias/event bridges remain distinct obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicRetainedStartup
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicInterpreter (State)
open RegistrationNativeRetainedService (Spec)
open RegistrationNativeWire (Wire)
open PqxdhSecretInputKdf (HmacOracle)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- The concrete startup forwards its real draws and leaves the separate private root cache unchanged. -/
theorem start_root (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : State n KemSK) (cache : HmacOracle.QueryCache) :
    (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      ((RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId identity).run before)).run cache =
      (fun result => ((result.1, { before with world := result.2 }), cache)) <$>
        (RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run before.world := by
  rw [RegistrationNativePublicStartupFrame.start_world,
    RegistrationNativePublicRootCoins.root_run setup.source setup.hmac setup.joint setup.dh seed scalar _
      (RegistrationNativePublicRootFrame.world_free _ before)]
  simp only [RegistrationNativePublicInterpreter.world, StateT.run, simulateQ_map,
    ← QueryImpl.simulateQ_compose]
  have coins : RegistrationNativePublicRootCoins.localImpl setup.hmac ∘ₛ
      RegistrationNativePublicInterpreter.coins = QueryImpl.ofLift unifSpec ProbComp := rfl
  rw [coins, simulateQ_ofLift_eq_self]
  simp only [Functor.map_map]

noncomputable def observed (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (source : RegistrationNativeMldsa.Source) (selectedOwner selectedAccept : Nat)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (started : RegistrationNativePublicStartup.Started source) :
    OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Bool :=
  (fun result => RegistrationNativeSelectedEvents.ceAppOwnerEvent setup.source.crypto wire serverKeyId budget selectedOwner claim
    (result.1.1, (result.1.2, result.2))) <$>
      RegistrationNativePublicFrontend.run setup checks wire source
        (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicValue.prekey serverKeyId bounds .P
        (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) started.frontend

/-- The executable complete client receives public references and material replies, with no selected private key, retained root or PRK in its state. -/
noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp Spec Bool := do
  let initialized ← simulateQ RegistrationNativePublicRetained.coins
    ((RegistrationNativePublicStartupFrame.startup (n := n) setup source ensureInit identityIndex serverKeyId publicValue.identity).run
      PqxdhRecordLiftWorld.initial)
  match initialized.1 with
  | none => pure false
  | some started =>
      RegistrationNativePublicRetained.client setup wire route
        (RegistrationNativeMldsa.owned source started.credential)
        (observed setup checks wire source selectedOwner selectedAccept publicValue serverKeyId bounds budget claim adversary started)
        { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 }

/-- Actual ideal-root interpretation of the complete reference profile equals this constructed retained-service client. -/
theorem client_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      (RegistrationNativePublicStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds budget claim adversary publicValue)).run' ∅ =
      (simulateQ (RegistrationNativeRetainedSource.implementation setup.source setup.hmac
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))))
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary publicValue)).run'
          RegistrationNativeRetainedSource.initial := by
  simp only [RegistrationNativePublicStartup.client, client, StateT.run'_eq, simulateQ_bind,
    StateT.run_bind, map_bind]
  rw [start_root]
  simp only [bind_map_left]
  delta RegistrationNativePublicRetained.coins
  rw [RegistrationNativePublicRootCoins.retained_coins]
  simp only [bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro initialized _reached
  cases initialized.1 with
  | none => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | some started =>
      have comparison := RegistrationNativePublicRetained.client_source setup wire route
        (RegistrationNativeMldsa.owned source started.credential) seed scalar
        (observed (n := n) setup checks wire source selectedOwner selectedAccept publicValue serverKeyId bounds budget claim adversary started)
        { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 } ∅
      simp only [RegistrationNativePublicInterpreter.run, observed, StateT.run'_eq, simulateQ_map,
        StateT.run_map, bind_pure_comp, Functor.map_map, RegistrationNativePublicInterpreter.initial,
        RegistrationNativeRetainedSource.initial] at comparison ⊢
      convert comparison using 1; rfl


end BeaconcryptCore.Computational.RegistrationNativePublicRetainedStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRetainedStartup.start_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRetainedStartup.start_root
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRetainedStartup.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRetainedStartup.client_source
