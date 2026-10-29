-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallAdmitted
import BeaconcryptCore.Computational.RegistrationNativeInstallCompile
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete

/-! The actual one-use Server controller records its same retained descriptor once exactly when its public build succeeds. Lookup, preflight, occupancy, reservation and every native failure branch are kept in the original chronological support. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerComplete
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeSecretWordInstallInsert (success)
open RegistrationNativeInstallBeaconComplete (present)
open RegistrationNativePairedMaterialSource (wordLift)
open RegistrationNativeSecretWordMessage (ServerReady)
abbrev Ready := ServerReady
variable {n : Nat} {KemSK Value Next : Type}

noncomputable def run (work : OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Value)
    (before : RegistrationNativeSecretWordFrontendTrace.State) :=
  (simulateQ RegistrationNativeSecretWordFrontendTrace.handler (simulateQ (wordLift (KemSK := KemSK)) work)).run before

private theorem pure_source (value : Value) (before : RegistrationNativeSecretWordFrontendTrace.State) :
    run (n := n) (KemSK := KemSK) (pure value) before = pure (value, before) := by
  simp only [run, simulateQ_pure, StateT.run_pure]

private theorem bind_source (work : OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Value)
    (next : Value → OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Next)
    (before : RegistrationNativeSecretWordFrontendTrace.State) :
    run (KemSK := KemSK) (work >>= next) before = (run work before >>= fun result => run (next result.1) result.2) := by
  simp only [run, simulateQ_bind, StateT.run_bind]

private theorem finish (published : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes))
    (server : RegistrationNativeSecretWordServerMaterial.State) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RegistrationNativeSecretWordServerMaterial.Result × RegistrationNativeSecretWordServerMaterial.State) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support (run (n := n) (KemSK := KemSK)
      ((RegistrationNativeSecretWordServerMaterial.finish published).run server) before)) :
    result.2 = before ∧ present result.1.1 = success published := by
  cases published with
  | fail error | div =>
      simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, pure_source, mem_support_pure_iff] at supported
      subst result
      exact ⟨rfl, rfl⟩
  | ok published =>
      cases published
      all_goals
        simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, pure_source, mem_support_pure_iff] at supported
        subst result
        exact ⟨rfl, rfl⟩

attribute [local irreducible] peer.begin_completion_lookup RegistrationServerSdkSource.preflight

/-- Every original complete result has exactly its own successful Server descriptor suffix, across all failure branches. -/
theorem complete (role : Role) (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (ready : Ready)
    (application : Slice U8) (server : RegistrationNativeSecretWordServerMaterial.State) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RegistrationNativeSecretWordServerMaterial.Result × RegistrationNativeSecretWordServerMaterial.State) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support (run (n := n) (KemSK := KemSK)
      ((RegistrationNativeSecretWordServerMaterial.complete wire reservePeer ready application).run server) before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ present result.1.1 = true then [ready.reference] else [] := by
  unfold RegistrationNativeSecretWordServerMaterial.complete at supported
  simp only [StateT.run] at supported
  split at supported <;> try {
    rw [pure_source, mem_support_pure_iff] at supported
    subst result
    simp [present] }
  split at supported <;> try {
    rw [pure_source, mem_support_pure_iff] at supported
    subst result
    simp [present] }
  split at supported <;> try {
    rw [pure_source, mem_support_pure_iff] at supported
    subst result
    simp [present] }
  rw [bind_source, mem_support_bind_iff] at supported
  obtain ⟨occupied, asked, continued⟩ := supported
  have same : occupied.2 = before := by
    simp only [run, RegistrationNativeSecretWordServerMaterial.effect, wordLift, QueryImpl.compose, RegistrationNativeSecretWordInterface.paired, RegistrationNativeSecretWordInterface.liftLocal, simulateQ_spec_query,
      RegistrationNativeSecretWordFrontendTrace.handler, RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
      StateT.run, support_map] at asked
    obtain ⟨reply, _called, returned⟩ := asked
    exact (congrArg Prod.snd returned).symm
  rw [same] at continued
  split at continued <;> try {
    rw [pure_source, mem_support_pure_iff] at continued
    subst result
    simp [present] }
  split at continued <;> try {
    rw [pure_source, mem_support_pure_iff] at continued
    subst result
    simp [present] }
  rw [bind_source, mem_support_bind_iff] at continued
  obtain ⟨published, admitted, completed⟩ := continued
  have settled := finish (KemSK := KemSK) published.1 server published.2 result completed
  have bill := RegistrationNativeSecretWordInstallAdmitted.server role wire.encodeResponse server.control _ ready.reference before published admitted
  rw [settled.1, bill, ← settled.2]

/-- The same live one-use session supplies exactly the descriptor counted by a successful original build. -/
theorem build_live (role : Role) (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (handle : Nat) (application : Option (Slice U8)) (server : RegistrationNativeSecretWordServerMaterial.State) (ready : Ready)
    (stored : server.sessions[handle]? = some (some ready)) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RegistrationNativeSecretWordServerMaterial.Result × RegistrationNativeSecretWordServerMaterial.State) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support (run (n := n) (KemSK := KemSK)
      ((RegistrationNativeSecretWordServerMaterial.build wire reservePeer handle application).run server) before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ present result.1.1 = true then [ready.reference] else [] := by
  simp only [RegistrationNativeSecretWordServerMaterial.build, RegistrationNativeSecretWordServerMaterial.take, stored, StateT.run] at supported
  cases application with
  | none =>
      rw [pure_source, mem_support_pure_iff] at supported
      subst result
      simp [present]
  | some application =>
      exact complete (KemSK := KemSK) role wire reservePeer ready application
        { server with sessions := server.sessions.set handle none } before result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerComplete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerComplete.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerComplete.complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerComplete.build_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerComplete.build_live
