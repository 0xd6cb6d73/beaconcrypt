-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitializedIdentityCollision
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainFull
import BeaconcryptCore.Computational.RegistrationNativeSharedMatchRun

/-! The original public SharedMatch event of the actual initialized Native run gives a collision in that same execution's private generated-identity table. Full native realization, original-ledger session uniqueness and publication receipts are derived from the execution; no public ownership, AD agreement or enrollment premise is added. The independent zero-query collision reduction supplies its probability loss separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeInitializedSharedMatch
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentServerAuthEvent (regsOf)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainSource (implementation project)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- The unchanged public matching event is transported to the private pool reached by the same initialized original-ledger execution. -/
theorem source_collision (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (readback : RegistrationNativeWire.InitReadBack wire)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (context : RegistrationNativeIdentityWorld.Context n KemSK)
    (result : (Value × (RegistrationNativeLedger.State × State n KemSK source)) × SourceState)
    (supported : result ∈ support ((simulateQ (implementation setup.joint)
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work
        ⟨context, []⟩)).run PqxdhDynamicIdentityPool.initialState))
    (first second : Nat)
    (shared : RegistrationNativeSharedMatchCollision.SharedMatch setup.source.crypto
      (RegistrationNativeWire.ledgerCodec wire) first second (regsOf result.1.2.1.ledger.transcript)) :
    PqxdhDeploymentServerAuthInjective.Collision setup.joint result.2.seeds := by
  have initialOwned := (RegistrationNativeIdentityMainHistoryRun.initial_inv
    (mlSource := source) setup.joint context).1.1
  have actual : RegistrationNativeIdentityMainFull.observedProject result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work
        (project ((⟨context, []⟩ : State n KemSK source), PqxdhDynamicIdentityPool.initialState))) := by
    rw [← RegistrationNativeIdentityMainFull.full_source setup checks wire route representation created credential
      bounds mode work _ initialOwned, support_map]
    exact Set.mem_image_of_mem _ supported
  have collision := RegistrationNativeSharedMatchRun.run_collision setup checks wire route representation created
    credential readback bounds mode work _ _ actual first second shared
  obtain ⟨leftIndex, rightIndex, different, leftSeed, rightSeed, leftAt, rightAt, same⟩ := collision
  simp only [List.getElem?_map, Option.map_eq_some_iff] at leftAt rightAt
  obtain ⟨left, leftAt, leftSeedEq⟩ := leftAt
  obtain ⟨right, rightAt, rightSeedEq⟩ := rightAt
  rw [← leftSeedEq, ← rightSeedEq] at same
  exact RegistrationNativeInitializedIdentityCollision.initialized_collision setup checks wire route representation
    created credential bounds mode work context result supported leftIndex rightIndex different left right leftAt rightAt same

end BeaconcryptCore.Computational.RegistrationNativeInitializedSharedMatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializedSharedMatch.source_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializedSharedMatch.source_collision
