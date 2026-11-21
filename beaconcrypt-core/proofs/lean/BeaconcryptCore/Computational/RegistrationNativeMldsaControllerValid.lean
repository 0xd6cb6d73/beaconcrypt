-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign
import BeaconcryptCore.Computational.RegistrationNativeMldsaServer
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership

/-! The actual reified controllers issue only ordinary queries and complete signing requests on their reached owned credential. This is a structural property of the free programs for every optional reply and private draw count; no dummy opaque signer is evaluated. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaPoolMap (CredentialLive)
open RegistrationNativeMldsaProgram (Spec liftState)
open RegistrationNativeMldsaTableSign (Valid)
variable {n : Nat} {ι KemSK State Value Next : Type} {base : OracleSpec ι}
variable (source : Source) (pool : Pool source)

private theorem map_all {Query : Type} {queries : OracleSpec Query} {Answer Result : Type}
    (predicate : Query → Prop) (observe : Answer → Result) (work : OracleComp queries Answer)
    (allowed : work.AllQueriesSatisfy predicate) : (observe <$> work).AllQueriesSatisfy predicate := by
  rw [← bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

private theorem ordinary_all (work : ProbComp Value) :
    (RegistrationNativeMldsaProgram.lift (source := handleSource source) work).AllQueriesSatisfy (Valid source pool) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      simp only [RegistrationNativeMldsaProgram.lift, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeMldsaProgram.ordinary]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private def Good (work : StateT State (OracleComp (Spec (handleSource source))) Value) : Prop :=
  ∀ before, (work.run before).AllQueriesSatisfy (Valid source pool)

private theorem pure_good (value : Value) : Good source pool (pure value : StateT State _ Value) :=
  fun _ => allQueriesSatisfy_pure _ _
private theorem bind_good (work : StateT State (OracleComp (Spec (handleSource source))) Value)
    (next : Value → StateT State (OracleComp (Spec (handleSource source))) Next)
    (first : Good source pool work) (rest : ∀ value, Good source pool (next value)) :
    Good source pool (work >>= next) := by
  intro before
  simp only [StateT.run_bind]
  exact allQueriesSatisfy_bind (first before) (fun result => rest result.1 result.2)
private theorem simulate_good {Query : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (StateT State (OracleComp (Spec (handleSource source)))))
    (law : ∀ query, Good source pool (implementation query)) (work : OracleComp queries Value) :
    Good source pool (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_good source pool value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_good source pool _ _ (law query) ih
private theorem lift_good (work : StateT State ProbComp Value) :
    Good source pool (liftState (source := handleSource source) work) :=
  fun before => ordinary_all source pool (work.run before)

private theorem call_all (credential : Credential (handleSource source)) (live : CredentialLive source pool credential)
    (accounting : RegistrationNativeMldsaCapability.Accounting) (request : registration.MldsaSigningRequest)
    (before : PqxdhRecordLiftWorld.State n) :
    ((RegistrationNativeMldsaProgram.call accounting (.sign credential request)).run before).AllQueriesSatisfy (Valid source pool) := by
  simp only [RegistrationNativeMldsaProgram.call, StateT.run]
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨live, fun _ => allQueriesSatisfy_pure _ _⟩

namespace Server
open RegistrationNativeMldsaServer
variable (credential : Credential (handleSource source)) (live : CredentialLive source pool credential)
include live

/-- Every Server publication callback signs with the reached owned server credential. -/
theorem outgoing (query : RegistrationSigningShared.Spec.Domain) :
    Good source pool (RegistrationNativeMldsaServer.outgoing (n := n) (handleSource source) credential query) := by
  cases query with
  | hash request => exact lift_good source pool _
  | sign request payload digest =>
      intro before
      apply map_all _ _ _
      exact call_all source pool credential live .native request before.1

private theorem signing {Auxiliary Encoded : Type}
    (encode : registration.SignedResponseView → core.option.Option Encoded) (pending : registration.ServerResponseHash) :
    Good source pool (RegistrationNativeMldsaServer.signing (n := n) (Auxiliary := Auxiliary) (handleSource source) credential encode pending) := by
  intro before
  apply map_all _ _ _
  exact simulate_good source pool _ (outgoing source pool credential live) _ before.world

private theorem publish {Auxiliary Encoded : Type}
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerResponseHash) :
    Good source pool (RegistrationNativeMldsaServer.publish (n := n) (Auxiliary := Auxiliary) (handleSource source) credential encode control pending) := by
  unfold RegistrationNativeMldsaServer.publish
  apply bind_good source pool _ _ (signing source pool credential live encode pending)
  intro result
  cases result with
  | fail error | div => exact pure_good source pool _
  | ok answer => cases answer with
    | Err previous => exact pure_good source pool _
    | Ok published => exact lift_good source pool _

private theorem completionFromInitial {Auxiliary Encoded Reader Response : Type}
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) :
    Good source pool (RegistrationNativeMldsaServer.completionFromInitial (n := n) (Auxiliary := Auxiliary)
      (handleSource source) credential setup codec encode control pending) := by
  unfold RegistrationNativeMldsaServer.completionFromInitial
  apply bind_good source pool _ _ (lift_good source pool _)
  intro result
  cases result with
  | fail error | div => exact pure_good source pool _
  | ok answer => cases answer with
    | Err previous => exact pure_good source pool _
    | Ok pending => exact publish source pool credential live encode control pending

omit live in
private theorem world (work : StateT (RegistrationServerRootCompiler.Local n)
    (OracleComp (Spec (handleSource source))) Value) (law : Good source pool work) :
    Good source pool (RegistrationNativeMldsaServer.world (handleSource source) work) :=
  fun before => map_all _ _ _ (law before.world)

private theorem fromInitial {Reader Response : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) :
    Good source pool (RegistrationNativeMldsaServer.fromInitial (n := n) (handleSource source) credential setup codec encode control pending) := by
  unfold RegistrationNativeMldsaServer.fromInitial
  exact bind_good source pool _ _
    (world source pool _ (completionFromInitial source pool credential live setup codec encode control pending))
    (fun _ => lift_good source pool _)

private theorem afterOccupancy {Reader Response : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (control : pqxdh.ServerState)
    (lookup : peer.CompletionLookup) (occupied : Bool) :
    Good source pool (RegistrationNativeMldsaServer.afterOccupancy (n := n) (handleSource source) credential setup codec checks encode control lookup occupied) := by
  unfold RegistrationNativeMldsaServer.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_good source pool _
  | ok result => cases result with
    | Err previous => exact pure_good source pool _
    | Ok pending =>
        apply bind_good source pool _ _ (lift_good source pool _)
        intro hashed
        cases hashed with
        | fail error | div => exact pure_good source pool _
        | ok result => cases result with
          | Err previous => exact pure_good source pool _
          | Ok initial =>
              simp only
              split
              · exact fromInitial source pool credential live setup codec encode control initial
              · exact pure_good source pool _

/-- All queries of the complete actual Server build use ordinary effects or its live owned signer. -/
theorem build {Reader Response : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (handle : Nat) (application : Option (Slice U8)) :
    Good source pool (RegistrationNativeMldsaServer.build (n := n) (handleSource source) credential setup codec checks encode handle application) := by
  intro before
  simp only [RegistrationNativeMldsaServer.build, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk found current => cases found with
    | none => exact allQueriesSatisfy_pure _ _
    | some token => cases application with
      | none => exact allQueriesSatisfy_pure _ _
      | some application =>
          simp only [RegistrationNativeMldsaServer.complete, StateT.run]
          cases peer.begin_completion_lookup current.control current.pin token application with
          | fail error | div => exact allQueriesSatisfy_pure _ _
          | ok result => cases result with
            | Err previous => exact allQueriesSatisfy_pure _ _
            | Ok lookup =>
                simp only
                cases lookup.request with
                | fail error | div => exact allQueriesSatisfy_pure _ _
                | ok keyId =>
                    simp only
                    split
                    · apply allQueriesSatisfy_bind
                        (world source pool _ (lift_good source pool _) current)
                      intro occupied
                      exact afterOccupancy source pool credential live setup codec checks encode current.control lookup occupied.1 occupied.2
                    · exact allQueriesSatisfy_pure _ _
end Server
namespace Bundle
open RegistrationNativeMldsaShared (Local)
open RegistrationNativeBeaconFrontend (Owner)
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

private theorem native (work : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source)
    RegistrationServerRoleBackend.State Value) :
    Good source pool (RegistrationNativeMldsaBundle.native setup checks representation created work) :=
  lift_good source pool _

/-- Every current Init callback is ordinary work and contains no ML capability request. -/
theorem outgoing (index : Nat) (owner : Owner (handleSource source))
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Good source pool (RegistrationNativeMldsaBundle.outgoing (n := n) setup checks representation created index owner query) :=
  native source pool setup checks representation created _

private theorem afterPublished (index : Nat) (owner : Owner (handleSource source))
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Good source pool (RegistrationNativeMldsaBundle.afterPublished (n := n) setup checks representation created index owner oneTime published) := by
  cases published with
  | fail error | div => exact pure_good source pool _
  | ok answer => cases answer with
    | Err previous => exact pure_good source pool _
    | Ok completed =>
        exact bind_good source pool _ _ (native source pool setup checks representation created _)
          (fun _ => bind_good source pool _ _ (native source pool setup checks representation created _)
            (fun _ => pure_good source pool _))

private theorem native_get (before : Local n KemSK (handleSource source)) :
    (RegistrationNativeMldsaBundle.native setup checks representation created get).run before = pure (before.1, before) := by
  rfl

/-- Actual bundle lookup derives the live signer from the reached owner list; no valid-signing assumption is supplied by a caller. -/
theorem bundle (wire : RegistrationNativeWire.Wire) (index : Nat) (before : Local n KemSK (handleSource source))
    :
    ((RegistrationNativeMldsaBundle.bundle setup checks wire representation created index).run before).AllQueriesSatisfy (Valid source pool) := by
  simp only [RegistrationNativeMldsaBundle.bundle, StateT.run_bind, native_get source setup checks representation created,
    pure_bind]
  cases found : before.1[index]? with
  | none => exact allQueriesSatisfy_pure _ _
  | some owner =>
      have continuation (oneTime : PqxdhJointGapDh.ScalarBytes) (current : Local n KemSK (handleSource source)) :
          ((do
            let published ← simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner)
              (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
                (RegistrationNativeBeaconFrontend.inputs setup owner)
                ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
            RegistrationNativeMldsaBundle.afterPublished setup checks representation created index owner oneTime published).run current).AllQueriesSatisfy (Valid source pool) :=
        bind_good source pool _ _
          (simulate_good source pool _ (outgoing source pool setup checks representation created index owner) _)
          (afterPublished source pool setup checks representation created index owner oneTime) current
      cases phase : owner.phase <;> simp only [phase]
      all_goals first
        | exact allQueriesSatisfy_pure _ _
        | exact continuation _ before
        | exact allQueriesSatisfy_bind
            (native source pool setup checks representation created _ before)
            (fun result => continuation result.1 result.2)

/-- The complete source Init wrapper inherits the live-credential query law from its actual lookup and local continuation. -/
theorem sourceBundle (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    :
    ((RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index).run before).AllQueriesSatisfy (Valid source pool) :=
  map_all _ _ _ (bundle source pool setup checks representation created wire index _)
end Bundle
end BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid.Server.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid.Server.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid.Server.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid.Server.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid.Bundle.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid.Bundle.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid.Bundle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid.Bundle.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid.Bundle.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaControllerValid.Bundle.sourceBundle
