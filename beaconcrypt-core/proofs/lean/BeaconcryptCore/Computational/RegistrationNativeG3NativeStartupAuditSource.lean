-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields
import BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformAuditBound

/-! The actual startup audit is factored through the same complete original native frontend and reached World. Only the independently completed empty material/seed caches are simplified; the real startup hash cache is kept literally. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditSource
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK P Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (serverKeyId : U64) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK P) (providerState : P)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (born : RegistrationNativeHiddenStartup.Started source) (world : PqxdhRecordLiftWorld.State n)

noncomputable def after : ProbComp Bool := do
  let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
  let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
  let result ← RegistrationNativeG3AuditRepeatEvent.original setup (RegistrationNativeWire.ledgerCodec wire) route seeds wire
    (RegistrationNativeMldsa.owned source born.native.credential) seed scalar candidate provider checks source selectedOwner selectedAccept
    (setup.dh.publicKey scalar) serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩) born.native.frontend
    (RegistrationNativeHiddenInterpreter.initial providerState, ∅)
    (RegistrationNativeG3LocalMaterialCompletedSource.cache materials) world
  pure result.2.2

/-- The successful actual startup continuation uses the same original frontend, original full compiler and reached cache. -/
theorem after_source (seeds_empty : world.seeds = PqxdhRecordLiftLazyTable.initial) :
    RegistrationNativeG3MaterializedStartup.auditAfter setup checks wire route source serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary (some born, world) =
      after setup checks wire source route serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary born world := by
  unfold RegistrationNativeG3MaterializedStartup.auditAfter after
  apply bind_congr
  intro materials
  simp only [RegistrationNativeG3MaterializedProtocolLazy.auditRun, bind_assoc, pure_bind]
  apply bind_congr
  intro seeds
  have overlay : RegistrationNativeG3GuardedCoupling.overlay world seeds = seeds := by
    funext slot
    simp [RegistrationNativeG3GuardedCoupling.overlay, seeds_empty, PqxdhRecordLiftLazyTable.initial, OracleComp.completeTable]
  rw [overlay]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditSource.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditSource.after_source
