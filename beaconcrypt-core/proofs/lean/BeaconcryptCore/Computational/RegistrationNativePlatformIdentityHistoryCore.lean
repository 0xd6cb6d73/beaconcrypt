-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle
/-! Shared source allocator and writer work preserve the actual generated signing-history invariant. Native leaves use their genuine local history proof and keep the complete platform poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityProgram (M native external runNew)
open RegistrationNativeIdentityHistoryInvariant (Good Holds)
open RegistrationNativeIdentitySourceSimulation (NewState)
variable {n : Nat} {I KemSK Auxiliary Platform Value Next : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)

def Preserves (index handle : Nat) (work : M n KemSK Auxiliary Platform source Value) : Prop :=
  ∀ before result, Good setup.joint index handle before.1 →
    result ∈ support (runNew setup checks representation created work before) → Good setup.joint index handle result.2.1

/-- Genuine native per-leaf synchronization lifts through the same persistent platform state. -/
theorem native_preserves (index handle : Nat)
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (law : RegistrationNativeIdentityHistoryInvariant.Preserves setup checks representation created index handle work) :
    Preserves setup checks representation created index handle (native (Platform := Platform) work) := by
  intro before result prior supported
  rw [RegistrationNativePlatformIdentityProgram.native_run,support_map] at supported
  obtain ⟨actual,reached,rfl⟩ := supported
  exact law before.1 actual prior reached

/-- Every actual shared-state platform effect leaves the full native signing history untouched. -/
theorem external_preserves (index handle : Nat) (work : StateT Platform ProbComp Value) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) setup checks representation created index handle (external work) := by
  intro before result prior supported
  rw [RegistrationNativePlatformIdentityProgram.external_run,support_map] at supported
  obtain ⟨actual,_reached,rfl⟩ := supported
  exact prior

/-- A pure return retains the whole synchronized state. -/
theorem pure_preserves (index handle : Nat) (value : Value) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) setup checks representation created index handle (pure value) := by
  intro before result prior supported
  simp only [runNew,StateT.run_pure,simulateQ_pure,map_pure,mem_support_pure_iff] at supported
  cases supported
  exact prior

/-- Actual sequencing retains the reached indexed history through every earlier platform outcome. -/
theorem bind_preserves (index handle : Nat) (work : M n KemSK Auxiliary Platform source Value)
    (next : Value → M n KemSK Auxiliary Platform source Next)
    (first : Preserves setup checks representation created index handle work)
    (later : ∀ value,Preserves setup checks representation created index handle (next value)) :
    Preserves setup checks representation created index handle (work >>= next) := by
  intro before result prior supported
  rw [RegistrationNativePlatformIdentityProgram.runNew_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,reached,continued⟩ := supported
  exact later middle.1 middle.2 result (first before middle prior reached) continued

/-- Adaptive source subtrees compose the actual individual query receipts. -/
theorem program_preserves {Index : Type} {spec : OracleSpec Index} (index handle : Nat)
    (implementation : QueryImpl spec (M n KemSK Auxiliary Platform source))
    (leaf : ∀ query,Preserves setup checks representation created index handle (implementation query))
    (work : OracleComp spec Value) :
    Preserves setup checks representation created index handle (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_preserves setup checks representation created index handle value
  | query_bind query next ih =>
    rw [simulateQ_bind,simulateQ_spec_query]
    exact bind_preserves setup checks representation created index handle _ _ (leaf query) ih

/-- The literal native hash/sign branch and the common-P source writer preserve the same captured generated handle. -/
theorem query_preserves {E : Type} (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformWriter.Spec E).Domain) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativePlatformIdentityPublication.callback setup index owner writer query) := by
  cases query with
  | inl query =>
    exact native_preserves setup checks representation created index owner.identity.handle _
      (RegistrationNativeIdentityHistoryOutgoing.query_preserves setup checks representation created index owner query)
  | inr query => exact external_preserves setup checks representation created index owner.identity.handle (writer query)

/-- Every actual stateful Init publication tree retains its chronological indexed signing history. -/
theorem publication_preserves {E : Type} (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) Value) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (simulateQ (RegistrationNativePlatformIdentityPublication.callback setup index owner writer) work) :=
  program_preserves setup checks representation created index owner.identity.handle _
    (query_preserves setup checks representation created index owner writer) work

/-- Actual successful source publication updates only lifecycle phase after recording every reached signature. -/
theorem next_preserves (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (reply : RegistrationNativePlatformIdentityBundle.Reply) :
    Preserves (n := n) (Auxiliary := Auxiliary) (Platform := Platform) setup checks representation created index owner.identity.handle
      (RegistrationNativePlatformIdentityBundle.next index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact pure_preserves setup checks representation created index owner.identity.handle _
  | ok result => cases result with
    | Err error => exact pure_preserves setup checks representation created index owner.identity.handle _
    | Ok published =>
      exact bind_preserves setup checks representation created index owner.identity.handle _ _
        (native_preserves setup checks representation created index owner.identity.handle _
          (RegistrationNativeIdentityHistoryInvariant.phase_preserves setup checks representation created index owner.identity.handle index _))
        (fun _ => bind_preserves setup checks representation created index owner.identity.handle _ _
          (native_preserves setup checks representation created index owner.identity.handle _
            (RegistrationNativeIdentityHistoryOutgoing.effect_preserves setup checks representation created index owner.identity.handle _))
          (fun _ => pure_preserves setup checks representation created index owner.identity.handle _))

/-- The literal outgoing source bundle retains failed signature and writer prefixes in the same synchronized history. -/
theorem bundled_preserves {E : Type} (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativePlatformIdentityBundle.bundled setup index owner oneTime writer) :=
  bind_preserves setup checks representation created index owner.identity.handle _ _
    (publication_preserves setup checks representation created index owner writer _)
    (next_preserves setup checks representation created index owner oneTime)

/-- Supplied and sampled one-time branches retain the exact generated signing history. -/
theorem start_preserves {E : Type} (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativePlatformIdentityBundleRun.start setup index owner writer) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start,phase]
    exact bind_preserves setup checks representation created index owner.identity.handle _ _
      (native_preserves setup checks representation created index owner.identity.handle _
        (RegistrationNativeIdentityHistoryOutgoing.sample_preserves setup checks representation created index owner.identity.handle _))
      (fun scalar => bundled_preserves setup checks representation created index owner scalar writer)
  | freshWithCoins scalar =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start,phase,pure_bind] using
      bundled_preserves setup checks representation created index owner scalar writer
  | initSent pending scalar | established completed | aborted aborted =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start,phase] using
      (pure_preserves (n := n) (Auxiliary := Auxiliary) (source := source) (Platform := Platform) setup checks representation created index owner.identity.handle
        (.ok none : RustM (Option (alloc.vec.Vec U8))))

/-- The complete actual stateful bundle retains generated ownership, distinct handles and chronological signed-message synchronization. -/
theorem bundle_holds {E : Type} (index : Nat)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : NewState n KemSK Auxiliary source × Platform)
    (result : RustM (Option (alloc.vec.Vec U8)) × (NewState n KemSK Auxiliary source × Platform))
    (prior : Holds setup.joint before.1.2.identities before.1.1.1)
    (supported : result ∈ support (runNew setup checks representation created
      (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer) before)) :
    Holds setup.joint result.2.1.2.identities result.2.1.1.1 := by
  cases found : before.1.1.1[index]? with
  | none =>
    simp only [runNew,RegistrationNativePlatformIdentityBundleRun.bundle,StateT.run_bind,StateT.run_get,
      pure_bind,found,StateT.run_pure,simulateQ_pure,map_pure,mem_support_pure_iff] at supported
    cases supported
    exact prior
  | some owner =>
    have same : runNew setup checks representation created (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer) before =
        runNew setup checks representation created (RegistrationNativePlatformIdentityBundleRun.start setup index owner writer) before := by
      simp only [runNew,RegistrationNativePlatformIdentityBundleRun.bundle,StateT.run_bind,StateT.run_get,pure_bind,found]
    rw [same] at supported
    apply (start_preserves setup checks representation created index owner writer before result ⟨prior,?_⟩ supported).1
    simp only [RegistrationNativeIdentityHistoryInvariant.At,RegistrationNativeIdentityHistorySync.handles,List.getElem?_map,found,Option.map_some]

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.native_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.native_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.external_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.external_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.pure_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.pure_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.bind_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.bind_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.program_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.program_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.query_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.query_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.publication_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.publication_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.next_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.next_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.bundled_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.bundled_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.start_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.start_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.bundle_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore.bundle_holds
