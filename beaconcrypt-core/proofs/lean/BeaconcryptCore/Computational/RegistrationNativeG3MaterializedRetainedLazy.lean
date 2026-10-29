-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendCaps
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure

/-! The actual cold known108 materialized frontend has the original native open-key client law under the ordinary lazy108-byte table. Selected material44/seed64 draws, actual nonselected caching, full original result/trace and the reached startup World/cache are all carried through the source equations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedLazy
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3MaterializedRetainedSource (ordinary)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)

noncomputable def client (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (frame : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState) (world : PqxdhRecordLiftWorld.State n) :=
  RegistrationNativeOpenKey.client setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    (RegistrationNativeOpenRetained.client setup wire route sign work (ordinary (frame, ∅) world))

/-- The actual sampled selected-table source equals the original candidate-independent open-key client closed by the same literal provider and ordinary lazy byte table. -/
theorem program_source (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) n)
    (frame : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState) (world : PqxdhRecordLiftWorld.State n) :
    LazyOracleDiscard.LawEq (do
      let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
      (simulateQ (RegistrationNativeG3MaterializedLocal.handler true materials seeds setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider) work).run'
        (RegistrationNativeG3AuditTraceRun.cold (frame, ∅) ∅, world))
      ((simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
          (client setup wire route sign seed scalar work frame world)).run' (frame.pool, frame.provider))).run' ∅) := by
  let retained := RegistrationNativeG3RetainedFrontendRun.retainedClient setup wire route sign provider work
    (ordinary (frame, ∅) world, frame.provider)
  have cap := RegistrationNativeG3RetainedFrontendCaps.client_bound setup wire route sign seed scalar provider work n bounded (frame, ∅) world
  have source := RegistrationNativeG3SelectiveDirectGame.lazy_source setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate retained cap
  have sampled : (do
      let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
      (simulateQ (RegistrationNativeG3MaterializedLocal.handler true materials seeds setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider) work).run'
        (RegistrationNativeG3AuditTraceRun.cold (frame, ∅) ∅, world)) = (do
      let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
      (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds) retained).run'
          (RegistrationNativeHiddenService.initial, ∅)) := by
    apply bind_congr
    intro materials
    apply bind_congr
    intro seeds
    exact RegistrationNativeG3MaterializedRetainedSource.program_source setup wire route sign seed scalar candidate provider materials seeds work bounded (frame, ∅) world
  have closed : (simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
      (client setup wire route sign seed scalar work frame world)).run' (frame.pool, frame.provider) =
      RegistrationNativeG3SelectiveDirectGame.compiled setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) retained := by
    rw [client, RegistrationNativeOpenKeyClosure.key_close]
    rfl
  rw [sampled, closed]
  exact source.symm

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedLazy
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedLazy.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedLazy.program_source
