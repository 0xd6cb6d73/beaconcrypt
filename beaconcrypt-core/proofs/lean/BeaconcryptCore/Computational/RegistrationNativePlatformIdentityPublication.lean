-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter

/-! The actual full source Init hash/sign/serializer program is interpreted with opaque generated Ed credentials and an arbitrary common stateful writer. Original and indexed execution retain the same complete native and external poststates through every signature, allocation and serialization failure. The proof derives correspondence from the existing actual outgoing leaves; no pure writer or whole-controller security law is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativePlatformIdentityProgram (M Original Related Keeps native original external externalOriginal)
variable {n : Nat} {ι KemSK Auxiliary Platform E Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def callback (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (RegistrationNativePlatformWriter.Spec E) (M n KemSK Auxiliary Platform source)
  | .inl query => native (RegistrationNativeIdentityFrontend.outgoing setup source index owner query)
  | .inr query => external (writer query)

noncomputable def originalCallback (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (RegistrationNativePlatformWriter.Spec E) (Original n KemSK Auxiliary Platform source)
  | .inl query => original (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)
  | .inr query => externalOriginal (writer query)

/-- Actual outgoing signature/hash leaves and the exact same P writer interpret every source request. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (seed : IdentitySeed)
    (found : seeds[owner.identity.handle]? = some seed) (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformWriter.Spec E).Domain) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds (callback setup index owner writer query)
      (originalCallback setup index (RegistrationNativeIdentityFrontend.restore seed owner) writer query) := by
  cases query with
  | inl query =>
    exact RegistrationNativePlatformIdentityProgram.native_related setup checks representation created seeds _ _
      (RegistrationNativeIdentityOutgoingSource.query_source setup checks representation created seeds index owner seed found publicKey query)
  | inr query => exact RegistrationNativePlatformIdentityProgram.external_related setup checks representation created seeds (writer query)

/-- Actual failed signing and source writer calls preserve the same generated private identity roster. -/
theorem query_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformWriter.Spec E).Domain) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (callback setup index owner writer query) := by
  cases query with
  | inl query =>
    exact RegistrationNativePlatformIdentityProgram.native_keeps setup checks representation created _
      (RegistrationNativeIdentityOutgoingSource.query_keeps setup checks representation created index owner query)
  | inr query => exact RegistrationNativePlatformIdentityProgram.external_keeps setup checks representation created (writer query)

/-- Arbitrary adaptive source publication trees preserve complete same-run state, including failed-prefix history and mutable writer results. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (seed : IdentitySeed)
    (found : seeds[owner.identity.handle]? = some seed) (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) Value) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds (simulateQ (callback setup index owner writer) work)
      (simulateQ (originalCallback setup index (RegistrationNativeIdentityFrontend.restore seed owner) writer) work) :=
  RegistrationNativePlatformIdentityProgram.related_program setup checks representation created seeds _ _
    (query_source setup checks representation created seeds index owner seed found publicKey writer)
    (query_keeps setup checks representation created index owner writer) work

theorem program_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) Value) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (simulateQ (callback setup index owner writer) work) :=
  RegistrationNativePlatformIdentityProgram.keeps_program setup checks representation created _
    (query_keeps setup checks representation created index owner writer) work

/-- The literal actual source Init controller, including all six-field serialization and shared-state allocation, has the opaque-credential source interpretation. -/
theorem begin_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (seeds : List IdentitySeed) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (seed : IdentitySeed)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : seeds[owner.identity.handle]? = some seed) (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (simulateQ (callback setup index owner writer) (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩
        (RegistrationNativeIdentityFrontend.inputs owner) ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin))
      (simulateQ (originalCallback setup index (RegistrationNativeIdentityFrontend.restore seed owner) writer)
        (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩
          (RegistrationNativeBeaconFrontend.inputs setup (RegistrationNativeIdentityFrontend.restore seed owner))
            ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)) := by
  rw [← RegistrationNativeIdentityRoles.inputs_source setup owner seed publicKey]
  exact program_source setup checks representation created seeds index owner seed found publicKey writer _

theorem begin_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (simulateQ (callback setup index owner writer) (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩
        (RegistrationNativeIdentityFrontend.inputs owner) ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)) :=
  program_keeps setup checks representation created index owner writer _

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.query_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.query_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.program_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.begin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.begin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.begin_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication.begin_keeps
