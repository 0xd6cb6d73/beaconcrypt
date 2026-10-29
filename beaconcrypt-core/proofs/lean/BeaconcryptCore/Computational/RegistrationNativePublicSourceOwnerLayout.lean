-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution

/-! The complete mixed frontend's owner operations use exactly the literal private source handler on the caller's current owner/environment state. Reassembly retains Server capabilities and parsed attempts; no captured old environment is restored after a callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerLayout
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceEffects (Private toPrivate fromPrivate)
open RegistrationNativePublicSourceExecution (execute)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def rebuild (before : RegistrationNativePublicFrontend.State source)
    (result : ((Value × RegistrationNativePublicOwners.State source) × RegistrationServerReferenceCompiler.Environment) × Private n KemSK) :
    Value × State n KemSK source :=
  (result.1.1.1, ({ before with beacons := result.1.1.2, environment := result.1.2 }, fromPrivate result.2))

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

/-- Every adaptive owner operation in the actual mixed frontend has the literal source program and complete reached private state. -/
theorem beacon_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : State n KemSK source) :
    (execute setup wire route sign seed scalar (RegistrationNativePublicFrontend.beacon work)).run before =
      rebuild before.1 <$>
        (simulateQ (RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar)
          ((work.run before.1.beacons).run before.1.environment)).run (toPrivate before.2) := by
  have native := RegistrationNativePublicSourceCallbacks.program_source setup wire route sign seed scalar false
    ((work.run before.1.beacons).run before.1.environment) before.2
  have mapped := congrArg (fun distribution => rebuild before.1 <$> distribution) native
  simpa only [execute, RegistrationNativePublicFrontend.beacon, RegistrationNativePublicSourceEffects.close,
    StateT.run, state_map_apply, simulateQ_map, Functor.map_map, rebuild,
    RegistrationNativePublicSourceEffects.layout, Prod.map_def, id_eq] using mapped

/-- Owner operations leave all Server capability/control fields and parsed-attempt state intact. -/
theorem beacon_fields (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((execute setup wire route sign seed scalar
      (RegistrationNativePublicFrontend.beacon work)).run before)) :
    result.2.1.server = before.1.server ∧ result.2.1.parsedAccepts = before.1.parsedAccepts := by
  rw [beacon_run, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact ⟨rfl, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerLayout
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerLayout.beacon_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerLayout.beacon_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerLayout.beacon_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerLayout.beacon_fields
