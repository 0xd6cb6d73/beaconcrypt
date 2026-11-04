-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaServer
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership

/-! Actual reified bundle and build controllers issue no ML generation request on any source path. This syntactic theorem needs no live-key or signer-success premise and counts every optional failure branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaProgram (Spec liftState)
variable {n : Nat} {ι KemSK State Value Next : Type} {base : OracleSpec ι}
variable (source : Source)

def Allowed : (Spec source).Domain → Prop
  | .inl _ | .inr (.sign _ _) => True
  | .inr .generate => False

private theorem map_all {Query : Type} {queries : OracleSpec Query} {Answer Result : Type}
    (predicate : Query → Prop) (observe : Answer → Result) (work : OracleComp queries Answer)
    (allowed : work.AllQueriesSatisfy predicate) : (observe <$> work).AllQueriesSatisfy predicate := by
  rw [← bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

private theorem ordinary_all (work : ProbComp Value) :
    (RegistrationNativeMldsaProgram.lift (source := source) work).AllQueriesSatisfy (Allowed source) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      simp only [RegistrationNativeMldsaProgram.lift, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeMldsaProgram.ordinary]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private def Good (work : StateT State (OracleComp (Spec source)) Value) : Prop :=
  ∀ before, (work.run before).AllQueriesSatisfy (Allowed source)

private theorem pure_good (value : Value) : Good source (pure value : StateT State _ Value) :=
  fun _ => allQueriesSatisfy_pure _ _
private theorem bind_good (work : StateT State (OracleComp (Spec source)) Value)
    (next : Value → StateT State (OracleComp (Spec source)) Next)
    (first : Good source work) (rest : ∀ value, Good source (next value)) :
    Good source (work >>= next) := by
  intro before
  simp only [StateT.run_bind]
  exact allQueriesSatisfy_bind (first before) (fun result => rest result.1 result.2)
private theorem simulate_good {Query : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (StateT State (OracleComp (Spec source))))
    (law : ∀ query, Good source (implementation query)) (work : OracleComp queries Value) :
    Good source (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_good source value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_good source _ _ (law query) ih
private theorem lift_good (work : StateT State ProbComp Value) :
    Good source (liftState (source := source) work) :=
  fun before => ordinary_all source (work.run before)

private theorem call_all (credential : Credential source)
    (accounting : RegistrationNativeMldsaCapability.Accounting) (request : registration.MldsaSigningRequest)
    (before : PqxdhRecordLiftWorld.State n) :
    ((RegistrationNativeMldsaProgram.call accounting (.sign credential request)).run before).AllQueriesSatisfy (Allowed source) := by
  simp only [RegistrationNativeMldsaProgram.call, StateT.run]
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, fun _ => allQueriesSatisfy_pure _ _⟩

namespace Server
open RegistrationNativeMldsaServer
variable (credential : Credential source)

/-- Server publication has no named generation request. -/
theorem outgoing (query : RegistrationSigningShared.Spec.Domain) :
    Good source (RegistrationNativeMldsaServer.outgoing (n := n) source credential query) := by
  cases query with
  | hash request => exact lift_good source _
  | sign request payload digest =>
      intro before
      apply map_all _ _ _
      exact call_all source credential .native request before.1

private theorem signing {Auxiliary Encoded : Type}
    (encode : registration.SignedResponseView → core.option.Option Encoded) (pending : registration.ServerResponseHash) :
    Good source (RegistrationNativeMldsaServer.signing (n := n) (Auxiliary := Auxiliary) source credential encode pending) := by
  intro before
  apply map_all _ _ _
  exact simulate_good source _ (outgoing source credential) _ before.world

private theorem publish {Auxiliary Encoded : Type}
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerResponseHash) :
    Good source (RegistrationNativeMldsaServer.publish (n := n) (Auxiliary := Auxiliary) source credential encode control pending) := by
  unfold RegistrationNativeMldsaServer.publish
  apply bind_good source _ _ (signing source credential encode pending)
  intro result
  cases result with
  | fail error | div => exact pure_good source _
  | ok answer => cases answer with
    | Err previous => exact pure_good source _
    | Ok published => exact lift_good source _

private theorem completionFromInitial {Auxiliary Encoded Reader Response : Type}
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) :
    Good source (RegistrationNativeMldsaServer.completionFromInitial (n := n) (Auxiliary := Auxiliary)
      source credential setup codec encode control pending) := by
  unfold RegistrationNativeMldsaServer.completionFromInitial
  apply bind_good source _ _ (lift_good source _)
  intro result
  cases result with
  | fail error | div => exact pure_good source _
  | ok answer => cases answer with
    | Err previous => exact pure_good source _
    | Ok pending => exact publish source credential encode control pending

private theorem world (work : StateT (RegistrationServerRootCompiler.Local n)
    (OracleComp (Spec source)) Value) (law : Good source work) :
    Good source (RegistrationNativeMldsaServer.world source work) :=
  fun before => map_all _ _ _ (law before.world)

private theorem fromInitial {Reader Response : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) :
    Good source (RegistrationNativeMldsaServer.fromInitial (n := n) source credential setup codec encode control pending) := by
  unfold RegistrationNativeMldsaServer.fromInitial
  exact bind_good source _ _
    (world source _ (completionFromInitial source credential setup codec encode control pending))
    (fun _ => lift_good source _)

private theorem afterOccupancy {Reader Response : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (control : pqxdh.ServerState)
    (lookup : peer.CompletionLookup) (occupied : Bool) :
    Good source (RegistrationNativeMldsaServer.afterOccupancy (n := n) source credential setup codec checks encode control lookup occupied) := by
  unfold RegistrationNativeMldsaServer.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_good source _
  | ok result => cases result with
    | Err previous => exact pure_good source _
    | Ok pending =>
        simp only
        split
        · exact fromInitial source credential setup codec encode control pending
        · exact pure_good source _

/-- Complete native build has no named generation request, including all failed prefixes. -/
theorem build {Reader Response : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (handle : Nat) (application : Option (Slice U8)) :
    Good source (RegistrationNativeMldsaServer.build (n := n) source credential setup codec checks encode handle application) := by
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
                        (world source _ (lift_good source _) current)
                      intro occupied
                      exact afterOccupancy source credential setup codec checks encode current.control lookup occupied.1 occupied.2
                    · exact allQueriesSatisfy_pure _ _
end Server
namespace Bundle
open RegistrationNativeMldsaShared (Local)
open RegistrationNativeBeaconFrontend (Owner)
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit)

private theorem native (work : RegistrationNativeBeaconFrontend.M n KemSK source
    RegistrationServerRoleBackend.State Value) :
    Good source (RegistrationNativeMldsaBundle.native setup checks representation created work) :=
  lift_good source _

/-- Init publication has no named generation request. -/
theorem outgoing (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Good source (RegistrationNativeMldsaBundle.outgoing (n := n) setup checks representation created index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact native source setup checks representation created _
    | sign request payload digest =>
        intro before
        simp only [RegistrationNativeMldsaBundle.outgoing, StateT.run]
        exact allQueriesSatisfy_bind (call_all source owner.mldsa .environment request before.2.2.server.world.world.1)
          (fun _ => allQueriesSatisfy_pure _ _)
  | inr request => exact native source setup checks representation created _

private theorem afterPublished (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (published : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Good source (RegistrationNativeMldsaBundle.afterPublished (n := n) setup checks representation created index owner oneTime published) := by
  cases published with
  | fail error | div => exact pure_good source _
  | ok answer => cases answer with
    | Err previous => exact pure_good source _
    | Ok completed =>
        exact bind_good source _ _ (native source setup checks representation created _)
          (fun _ => bind_good source _ _ (native source setup checks representation created _)
            (fun _ => pure_good source _))

private theorem native_get (before : Local n KemSK source) :
    (RegistrationNativeMldsaBundle.native setup checks representation created get).run before = pure (before.1, before) := by
  rfl

/-- Bundle lookup and its full actual publication continuation have no named generation request. -/
theorem bundle (wire : RegistrationNativeWire.Wire) (index : Nat) (before : Local n KemSK source)
    :
    ((RegistrationNativeMldsaBundle.bundle setup checks wire representation created index).run before).AllQueriesSatisfy (Allowed source) := by
  simp only [RegistrationNativeMldsaBundle.bundle, StateT.run_bind, native_get source setup checks representation created,
    pure_bind]
  cases found : before.1[index]? with
  | none => exact allQueriesSatisfy_pure _ _
  | some owner =>
      have continuation (oneTime : PqxdhJointGapDh.ScalarBytes) (current : Local n KemSK source) :
          ((do
            let published ← simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner)
              (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
                (RegistrationNativeBeaconFrontend.inputs setup owner)
                ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
            RegistrationNativeMldsaBundle.afterPublished setup checks representation created index owner oneTime published).run current).AllQueriesSatisfy (Allowed source) :=
        bind_good source _ _
          (simulate_good source _ (outgoing source setup checks representation created index owner) _)
          (afterPublished source setup checks representation created index owner oneTime) current
      cases phase : owner.phase <;> simp only [phase]
      all_goals first
        | exact allQueriesSatisfy_pure _ _
        | exact continuation _ before
        | exact allQueriesSatisfy_bind
            (native source setup checks representation created _ before)
            (fun result => continuation result.1 result.2)

/-- The complete source bundle has no named generation request. -/
theorem sourceBundle (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source)
    :
    ((RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index).run before).AllQueriesSatisfy (Allowed source) :=
  map_all _ _ _ (bundle source setup checks representation created wire index _)
end Bundle
end BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate.Server.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate.Server.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate.Bundle.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate.Bundle.sourceBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate.Server.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate.Server.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate.Bundle.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate.Bundle.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate.Bundle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoGenerate.Bundle.bundle
