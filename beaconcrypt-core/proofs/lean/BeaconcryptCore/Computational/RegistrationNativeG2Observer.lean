-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG2Trace
import BeaconcryptCore.Computational.RegistrationNativeOpenStartupMaterialCaps

/-! The concrete G2 observer runs the full generated native frontend and original secrecy ledger with the pure chronological trace. Selected source challenges are sampled locally inside the post-key reduction. The final observer can inspect the actual descriptor/install trace; it needs neither a new public oracle nor access to the private KEM pool or key-table cache. Ignoring the trace recovers the existing open client exactly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG2Observer
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Outcome (Value : Type) := (Value × RegistrationNativeLedger.State) × RegistrationNativeG2Trace.State

noncomputable def retained (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (observe : Outcome Value → Bool) (publicValue : PqxdhJointGapDh.PublicChallenge) :
    OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Bool := do
  let initialized ← RegistrationNativeOpenRetainedStartup.start (n := n)
    setup source ensureInit identityIndex serverKeyId publicValue.identity
  match initialized.1 with
  | none => pure false
  | some started =>
      RegistrationNativeOpenRetained.client setup wire route (RegistrationNativeMldsa.owned source started.credential)
        ((fun result => observe (result.1.1, result.2)) <$>
          RegistrationNativeG2Trace.program
            (RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source started.credential)
              selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
              (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) started.frontend))
        { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 }

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (observe : PqxdhJointIdentity.IdentitySeed → PqxdhJointGapDh.ScalarBytes → Outcome Value → Bool) :
    OracleComp (RegistrationNativeOpenKey.Spec KemSK) Bool := do
  let seed ← simulateQ RegistrationNativeOpenKeyStartup.coins PqxdhJointIdentity.sampleSeed
  let scalar ← simulateQ RegistrationNativeOpenKeyStartup.coins PqxdhJointGapDh.sampleScalar
  RegistrationNativeOpenKey.client setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    (retained (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
      bounds mode adversary (observe seed scalar) (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))

noncomputable def nativeClient (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (observe : PqxdhJointIdentity.IdentitySeed → PqxdhJointGapDh.ScalarBytes → Outcome Value → Bool) :
    OracleComp (RegistrationNativeOpenKey.NativeSpec KemSK) Bool :=
  simulateQ RegistrationNativeOpenKey.native
    (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
      bounds mode adversary observe)

/-- Erasing the pure chronological trace recovers the complete original open retained client, including optional startup failure. -/
theorem retained_erase (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) (publicValue : PqxdhJointGapDh.PublicChallenge) :
    retained (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
      bounds mode adversary (fun result => decision result.1) publicValue =
      RegistrationNativeOpenRetainedStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary decision publicValue := by
  unfold retained RegistrationNativeOpenRetainedStartup.client
  apply bind_congr
  intro initialized
  cases initialized.1 with
  | none => rfl
  | some started =>
      simp only []
      have actual := congrArg (fun work => (decision ∘ Prod.fst) <$> work)
        (RegistrationNativeG2Trace.program_erase (n := n) (KemSK := KemSK)
          (RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source started.credential)
            selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
            (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) started.frontend)
          RegistrationNativeG2Trace.initial)
      simp only [Functor.map_map, RegistrationNativeG2Trace.program, Function.comp_def] at actual ⊢
      rw [actual]

/-- The actual G2 client with a ledger-only observation is unchanged by installing the trace layer. -/
theorem client_erase (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
      bounds mode adversary (fun _ _ result => decision result.1) =
      RegistrationNativeOpenKeyStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary decision := by
  unfold client RegistrationNativeOpenKeyStartup.client
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  rw [retained_erase]

noncomputable def aliasObserver (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (outcome : Outcome Value) : Bool := by
  classical
  exact decide (RegistrationNativeG2Trace.SameRoleAlias
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) outcome.2.events)

noncomputable def attemptAliasObserver (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (outcome : Outcome Value) : Bool := by
  classical
  exact decide (RegistrationNativeG2Trace.RepeatedRoleAttempt
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) outcome.2.events)

end BeaconcryptCore.Computational.RegistrationNativeG2Observer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Observer.retained_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Observer.retained_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Observer.client_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Observer.client_erase
