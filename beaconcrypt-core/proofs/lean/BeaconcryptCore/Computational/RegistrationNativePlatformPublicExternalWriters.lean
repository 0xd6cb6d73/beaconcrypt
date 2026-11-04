-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
/-! Reifying individual P primitives preserves their exact free external-coin tree. The concrete source helper and registration writer use public capacity reservations; actual serialization is pure. Full Init and admitted/refused Response writer costs derive from the actual source body, at most one reached reservation each. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicFrontend
open RegistrationNativePlatformPublicExternalLocal (IsLocalExternal platform_bound)
variable {n : Nat} {Platform E A : Type} {KemSK : Type}

/-- Stateful P-program reification commutes query by query, retaining complete values and every reached poststate. -/
theorem reify_program {J K : Type} {input : OracleSpec J} {output : OracleSpec K}
    (coins : QueryImpl unifSpec (OracleComp output))
    (implementation : QueryImpl input (StateT Platform ProbComp)) (work : OracleComp input A) (before : Platform) :
    ((simulateQ (r := StateT Platform (OracleComp output)) (fun query current => simulateQ coins ((implementation query).run current)) work).run before) =
      simulateQ coins ((simulateQ implementation work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact bind_congr (fun result => ih result.1 result.2)

private theorem total_map_iff {J X Y : Type} {queries : OracleSpec J}
    (work : OracleComp queries X) (change : X → Y) (cap : Nat) :
    (change <$> work).IsTotalQueryBound cap ↔ work.IsTotalQueryBound cap :=
  isQueryBound_map_iff work change cap _ _

/-- The literal source writer reification retains its full free external-coin tree. -/
theorem writer_program (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (AdapterRegistrationWriterRequestMonad.Spec E) A) (before : Platform) :
    ((simulateQ (writer (n := n) (KemSK := KemSK) implementation) work).run before) =
      simulateQ (localCoin (n := n) (KemSK := KemSK)) ((simulateQ implementation work).run before) :=
  reify_program (localCoin (n := n) (KemSK := KemSK)) implementation work before

/-- The concrete helper's allocation sees only capacity; its actual serializer contributes no uniform queries. -/
theorem helper_bound (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (cap : Nat) (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound cap)
    (query : (AdapterRecordHelperRequestMonad.Spec E).Domain) (before : Platform) :
    ((RegistrationNativePlatformConcreteSource.helper reserve query).run before).IsTotalQueryBound cap := by
  cases query with
  | reserve original capacity =>
    simpa only [RegistrationNativePlatformConcreteSource.helper, AdapterRecordRawBytes.helper,
      RegistrationNativePlatformConcreteSource.rawAllocation, StateT.run_map, total_map_iff] using bounded capacity.val before
  | encodeFrame sequence sender parts output => trivial

/-- Actual source registration serializers are pure; only the literal capacity reservation has its supplied external cap. -/
theorem writer_bound (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (cap : Nat) (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound cap)
    (query : (AdapterRegistrationWriterRequestMonad.Spec E).Domain) (before : Platform) :
    ((RegistrationNativePlatformConcreteSource.writer reserve query).run before).IsTotalQueryBound cap := by
  cases query with
  | reserve original capacity =>
    simpa only [RegistrationNativePlatformConcreteSource.writer, RegistrationSourceWriterBody.platform,
      StateT.run_map, total_map_iff] using bounded capacity before
  | encodeInit packet output | encodeResponse packet output => trivial

/-- The complete actual Init source writer pays one6757 reservation, including its failure, under the NEW local external-coin interface. -/
theorem init_bound (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (cap : Nat) (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound cap)
    (view : registration.SignedInitView) (before : Platform) :
    ((simulateQ (writer (n := n) (KemSK := KemSK) (RegistrationNativePlatformConcreteSource.writer reserve))
      (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run).run before).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) cap := by
  rw [writer_program]
  apply platform_bound
  rw [RegistrationNativePlatformConcreteSource.init_writer]
  simpa only [StateT.run_map, total_map_iff] using bounded 6757#usize before

/-- Every admitted or refused actual Response source writer pays at most its one capacity reservation and retains the failure/P state. -/
theorem response_bound (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (cap : Nat) (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound cap)
    (view : registration.SignedResponseView) (before : Platform) :
    ((simulateQ (writer (n := n) (KemSK := KemSK) (RegistrationNativePlatformConcreteSource.writer reserve))
      (AdapterRegistrationWriterRequestExtraction.encodeResponse (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.responsePacket view)).run).run before).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) cap := by
  rw [writer_program]
  apply platform_bound
  by_cases admitted : RegistrationSerializerResponseBytes.totalLength (RegistrationNativeSourceEncoders.responseSyntax view) ≤ CborSizing.maxMessageSize
  · obtain ⟨capacity, _sized, source⟩ := RegistrationNativePlatformConcreteSource.response_writer reserve view admitted
    rw [source]
    simpa only [StateT.run_map, total_map_iff] using bounded capacity before
  · rw [RegistrationNativePlatformConcreteSource.response_rejected reserve view (Nat.lt_of_not_ge admitted)]
    trivial
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.reify_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.reify_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.writer_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.writer_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.helper_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.helper_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.writer_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.writer_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.init_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.init_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.response_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters.response_bound
