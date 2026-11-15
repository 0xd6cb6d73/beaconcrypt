-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRequests

/-! Actual native owner creation and outgoing publication preserve the record-request analysis field. The Server-only ML request refuses purely, while the real Ed signing and shared hash paths remain; no environment projection is used to infer preservation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private def Keeps (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) →
    result.2.recordRequests = env.recordRequests

private theorem pure_keeps (value : Value) : Keeps (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem bind_keeps (work : M n KemSK source Auxiliary Value) (next : Value → M n KemSK source Auxiliary Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle reached)

private theorem lift_keeps (work : OracleComp (Trusted n KemSK) Value) :
    Keeps (StateT.lift (StateT.lift work) : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨returned, reached, equal⟩ := supported
  cases equal
  obtain ⟨reply, _member, same⟩ := reached
  cases same
  rfl

private theorem program_keeps {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (step : ∀ query, Keeps (implementation query)) (work : OracleComp spec Value) :
    Keeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps _ _ (step query) ih

private theorem sample_keeps (work : ProbComp Value) :
    Keeps (sample work : M n KemSK source Auxiliary Value) :=
  program_keeps _ (fun _ => lift_keeps _) work

private theorem get_keeps : Keeps (get : M n KemSK source Auxiliary (State source)) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem modify_keeps (update : State source → State source) :
    Keeps (modify update : M n KemSK source Auxiliary Unit) := by
  intro owners env result supported
  simp only [StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem set_keeps (owners : State source) : Keeps (set owners : M n KemSK source Auxiliary Unit) := by
  intro before env result supported
  simp only [StateT.run_set, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem receipts_keeps (receipts : List RegistrationSigningShared.Receipt) :
    Keeps (updateEnv (fun env => { env with receipts := env.receipts ++ receipts }) : M n KemSK source Auxiliary Unit) := by
  intro owners env result supported
  simp only [updateEnv, StateT.run_lift, bind_pure_comp] at supported
  cases supported
  rfl

private theorem prepare_keeps (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Keeps (prepare source edPin mlPin keyId : M n KemSK source Auxiliary (RustM (Option (Prepared source)))) := by
  unfold prepare
  exact bind_keeps _ _ (sample_keeps _) (fun _ =>
    bind_keeps _ _ (sample_keeps _) (fun _ => pure_keeps _))

private theorem append_keeps (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (pin : session.ServerAuthenticationPin)
    (identity : PqxdhJointIdentity.IdentitySeed) (prekey : PqxdhJointGapDh.ScalarBytes) :
    Keeps (appendBorn setup source edPin keyId pin identity prekey : M n KemSK source Auxiliary (RustM (Option Nat))) :=
  bind_keeps _ _ (lift_keeps _) (fun _ => bind_keeps _ _ (lift_keeps _) (fun _ =>
    bind_keeps _ _ get_keeps (fun _ => bind_keeps _ _ (set_keeps _) (fun _ => pure_keeps _))))

private theorem outgoing_keeps (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact lift_keeps _
    | sign request payload digest =>
        exact pure_keeps _
  | inr request =>
      classical
      unfold outgoing
      dsimp only
      split
      · exact bind_keeps _ _ (modify_keeps _) (fun _ => pure_keeps _)
      · exact pure_keeps _

private theorem bundled_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Keeps (do
      let published ← simulateQ (outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
      match published with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok finished) => do
          updatePhase index (.initSent finished.pending oneTime)
          let _ ← effect (.inr (.advanceOwner owner.worldOwner .initSent))
          pure (.ok (some finished.encoded)) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes))) := by
  apply bind_keeps _ _ (program_keeps _ (outgoing_keeps setup index owner) _)
  intro published
  cases published with
  | fail error | div => exact pure_keeps _
  | ok result => cases result with
    | Err error => exact pure_keeps _
    | Ok finished => exact bind_keeps _ _ (modify_keeps _) (fun _ =>
        bind_keeps _ _ (lift_keeps _) (fun _ => pure_keeps _))

/-- Native constructor effects retain exactly the original record-request field through every constructor preflight and failure. -/
theorem create_keeps (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Nat) × State source) × EnvState Auxiliary)
    (supported : result ∈ support (((create (n := n) setup source edPin mlPin keyId).run owners).run env)) :
    result.2.recordRequests = env.recordRequests := by
  have valid : Keeps (create (n := n) (Auxiliary := Auxiliary) setup source edPin mlPin keyId) := by
    apply bind_keeps _ _ (prepare_keeps edPin mlPin keyId)
    intro result
    cases result with
    | fail error | div => exact pure_keeps _
    | ok prepared => cases prepared with
      | none => exact pure_keeps _
      | some prepared => exact append_keeps setup edPin keyId prepared.pin prepared.identity prepared.prekey
  exact valid owners env result supported

/-- Actual outgoing publication preserves the independent record-request field through its real Ed/hash paths and the pure Server-only ML refusal. -/
theorem bundle_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (supported : result ∈ support (((bundle (n := n) setup source wire index).run owners).run env)) :
    result.2.recordRequests = env.recordRequests := by
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none => simp only [found, StateT.run_pure, mem_support_pure_iff] at supported; cases supported; rfl
  | some owner =>
      rw [found] at supported
      cases phase : owner.phase <;> simp only [phase] at supported
      all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; rfl }
      case fresh => exact (bind_keeps _ _ (sample_keeps _) (fun oneTime => bundled_keeps setup wire index owner oneTime)) owners env result supported
      case freshWithCoins oneTime => exact (bundled_keeps setup wire index owner oneTime) owners env result supported

/-- Public scalar/prekey packing retains the actual constructor's exact environment analysis field. -/
theorem public_create_keeps (setup : Setup base KemSK) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Nat) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationNativePublicOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId).run owners).run env)) :
    result.2.recordRequests = env.recordRequests := by
  simp only [RegistrationNativePublicOwners.create, RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at supported
  obtain ⟨reached, member, equal⟩ := supported
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member
  have kept := create_keeps setup edPin mlPin keyId (owners.map RegistrationNativePublicOwners.restore) env reached native
  cases equal
  exact kept

/-- Public outgoing packing preserves the current environment field through the actual native signing and writer branches. -/
theorem public_bundle_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationNativePublicOwners.bundle (n := n) setup source wire selected publicPrekey index).run owners).run env)) :
    result.2.recordRequests = env.recordRequests := by
  simp only [RegistrationNativePublicOwners.bundle, RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at supported
  obtain ⟨reached, member, equal⟩ := supported
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member
  have kept := bundle_keeps setup wire index (owners.map RegistrationNativePublicOwners.restore) env reached native
  cases equal
  exact kept

end BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests.create_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests.create_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests.bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests.bundle_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests.public_create_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests.public_create_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests.public_bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests.public_bundle_keeps
