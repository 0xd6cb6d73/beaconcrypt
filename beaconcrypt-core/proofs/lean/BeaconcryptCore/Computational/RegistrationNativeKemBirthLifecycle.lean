-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners

/-! Actual Beacon bundle/finish transitions change lifecycle phases while retaining every owner's exact opaque KEM handle and public key. The proof follows the actual callbacks, including all primitive errors, abort paths and failed record publication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBirthLifecycle
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeKemBirthInvariant (metadata)
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}
private abbrev Keys := List (Nat × PqxdhKemIndCca.MlKem768PublicKey)

private def Keeps (expected : Keys) (work : M n KemSK mlSource Auxiliary Value) : Prop :=
  ∀ owners env result, owners.map metadata = expected →
    result ∈ support ((work.run owners).run env) → result.1.2.map metadata = expected

private theorem pure_keeps (expected : Keys) (value : Value) :
    Keeps expected (pure value : M n KemSK mlSource Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

private theorem bind_keeps {Next : Type} (expected : Keys) (work : M n KemSK mlSource Auxiliary Value)
    (next : Value → M n KemSK mlSource Auxiliary Next) (first : Keeps expected work)
    (rest : ∀ value, Keeps expected (next value)) : Keeps expected (work >>= next) := by
  intro owners env result prior supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owners env middle prior reached) continued

private theorem lift_keeps (expected : Keys)
    (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Keeps expected (StateT.lift work : M n KemSK mlSource Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _, returned⟩ := supported
  cases returned
  exact prior

private theorem simulate_keeps {Query : Type} {spec : OracleSpec Query} (expected : Keys)
    (implementation : QueryImpl spec (M n KemSK mlSource Auxiliary))
    (law : ∀ query, Keeps expected (implementation query)) (work : OracleComp spec Value) :
    Keeps expected (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps expected value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps expected _ _ (law query) ih

private theorem sample_keeps (expected : Keys) (work : ProbComp Value) :
    Keeps expected (sample (n := n) (KemSK := KemSK) (mldsaSource := mlSource) (Auxiliary := Auxiliary) work) :=
  simulate_keeps expected (fun (query : unifSpec.Domain) => effect (.inl query))
    (fun _ => lift_keeps expected _) work

private theorem set_same (expected : Keys) (index : Nat) (key : Nat × PqxdhKemIndCca.MlKem768PublicKey)
    (found : expected[index]? = some key) : expected.set index key = expected := by
  obtain ⟨below, selected⟩ := List.getElem?_eq_some_iff.mp found
  rw [← selected]
  exact List.set_getElem_self below

private theorem current_keeps (expected : Keys) (index : Nat) (change : Owner mlSource → Owner mlSource)
    (same : ∀ owner, metadata (change owner) = metadata owner) :
    Keeps expected ((modify fun owners => match owners[index]? with
      | none => owners
      | some current => owners.set index (change current)) : M n KemSK mlSource Auxiliary Unit) := by
  intro owners env result prior supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => simpa only [found] using prior
  | some owner =>
      simp only [List.map_set, same, prior]
      apply set_same expected index (metadata owner)
      rw [← prior]
      simp [found]

private theorem phase_keeps (expected : Keys) (index : Nat) (phase : Phase) :
    Keeps expected (updatePhase (n := n) (KemSK := KemSK) (mldsaSource := mlSource) (Auxiliary := Auxiliary) index phase) :=
  current_keeps expected index (fun owner => { owner with phase }) (fun _ => rfl)

private theorem log_keeps (expected : Keys) (index : Nat) (message : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Keeps expected (logEd (n := n) (KemSK := KemSK) (mldsaSource := mlSource) (Auxiliary := Auxiliary) index message signature) :=
  current_keeps expected index
    (fun owner => { owner with edHistory := owner.edHistory ++ [.signed message signature] }) (fun _ => rfl)

private theorem outgoing_keeps (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) (expected : Keys) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps expected (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  classical
  rcases query with (hashRequest | signRequest) | edRequest
  · exact lift_keeps expected _
  · exact bind_keeps expected _ _ (sample_keeps expected _) (fun _ =>
      bind_keeps expected _ _ (lift_keeps expected _) (fun _ => pure_keeps expected _))
  · simp only [outgoing]
    split
    · exact bind_keeps expected _ _ (log_keeps expected index _ _) (fun _ => pure_keeps expected _)
    · exact pure_keeps expected _

private theorem authentication_keeps (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (expected : Keys) (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    Keeps expected (authentication (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) setup source query) := by
  cases query with
  | hash request => exact bind_keeps expected _ _ (lift_keeps expected _) (fun _ => pure_keeps expected _)
  | mldsa request | ed25519 request => exact pure_keeps expected _

private theorem primitive_keeps (setup : Setup base KemSK) (owner : Owner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (expected : Keys)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Keeps expected (primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  unfold primitive
  apply simulate_keeps expected
  intro lower
  cases lower with
  | inl other => exact sample_keeps expected _
  | inr other => exact lift_keeps expected _

private theorem agreement_keeps (setup : Setup base KemSK) (owner : Owner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (expected : Keys)
    (query : RegistrationAgreementExecutor.Spec.Domain) :
    Keeps expected (agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  unfold agreement
  apply bind_keeps expected _ _ (lift_keeps expected _)
  intro _
  cases query
  all_goals first | exact primitive_keeps setup owner oneTime expected _ | exact pure_keeps expected _

private theorem record_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (expected : Keys) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Keeps expected (record (n := n) (KemSK := KemSK) (mldsaSource := mlSource) (Auxiliary := Auxiliary) setup wire query) := by
  unfold record
  apply bind_keeps expected _ _ (lift_keeps expected _)
  intro _
  cases query
  all_goals first
    | exact sample_keeps expected _
    | exact bind_keeps expected _ _ (lift_keeps expected _) (fun _ => pure_keeps expected _)

private theorem abort_keeps (owner : Owner mlSource) (expected : Keys) :
    Keeps expected (abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner) :=
  bind_keeps expected _ _ (lift_keeps expected _) (fun _ => pure_keeps expected _)

private noncomputable def bundled (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let published ← simulateQ (outgoing setup source index owner)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
      updatePhase index (.initSent finished.pending oneTime)
      let _ ← effect (.inr (.advanceOwner owner.worldOwner .initSent))
      pure (.ok (some finished.encoded))

private theorem bundled_keeps (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (expected : Keys) :
    Keeps expected (bundled (n := n) (Auxiliary := Auxiliary) setup source wire index owner oneTime) := by
  unfold bundled
  apply bind_keeps expected _ _ (simulate_keeps expected _ (outgoing_keeps setup source index owner expected) _)
  intro published
  cases published with
  | fail error | div => exact pure_keeps expected _
  | ok result => cases result with
    | Err previous => exact pure_keeps expected _
    | Ok finished => exact bind_keeps expected _ _ (phase_keeps expected index _) (fun _ =>
        bind_keeps expected _ _ (lift_keeps expected _) (fun _ => pure_keeps expected _))

/-- Successful and failed bundles retain all old opaque KEM handles and public keys. -/
theorem bundle_metadata (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (supported : result ∈ support (((bundle (n := n) setup source wire index).run owners).run env)) :
    result.1.2.map metadata = owners.map metadata := by
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none => simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; rfl
  | some owner =>
      rw [found] at supported
      cases phase : owner.phase <;> simp only [phase] at supported
      all_goals try { simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; rfl }
      case fresh =>
        exact (bind_keeps _ _ _ (sample_keeps _ _) (fun oneTime =>
          bundled_keeps setup source wire index owner oneTime _)) owners env result rfl supported
      case freshWithCoins oneTime =>
        exact (bundled_keeps setup source wire index owner oneTime _) owners env result rfl supported

private theorem abort_pure_keeps (owner : Owner mlSource) (expected : Keys) (value : Value) :
    Keeps expected ((abort owner *> pure value) : M n KemSK mlSource Auxiliary Value) := by
  rw [seqRight_eq_bind]
  exact bind_keeps expected _ _ (abort_keeps owner expected) (fun _ => pure_keeps expected value)

private noncomputable def finished (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) :=
  match pending.aborted_state with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok aborted => do
      updatePhase index (.aborted aborted)
      let authenticated ← simulateQ (authentication setup source)
        (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))
      match authenticated with
      | .fail error => abort owner *> pure (.fail error)
      | .div => abort owner *> pure .div
      | .ok (.Err _) => abort owner *> pure (.ok none)
      | .ok (.Ok accepted) => do
          let agreed ← simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon accepted)
          match agreed with
          | .fail error => abort owner *> pure (.fail error)
          | .div => abort owner *> pure .div
          | .ok (.BeaconComplete completed) => do
              let opened ← simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin completed)
              match opened with
              | .fail error => abort owner *> pure (.fail error)
              | .div => abort owner *> pure .div
              | .ok (.Err _) => abort owner *> pure (.ok none)
              | .ok (.Ok established) => do
                  let shell : PqxdhRecordLiftInterface.BeaconShell :=
                    ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩
                  let installed : Bool ← effect (.inr (.installBeacon owner.worldOwner shell (.known established.kernel)))
                  if installed then
                    updatePhase index (.established ⟨established.control, established.binding, established.application⟩)
                    pure (.ok (some (TranscriptAuthParts.absSlice established.application)))
                  else abort owner *> pure (.ok none)
          | .ok _ => abort owner *> pure (.ok none)

private theorem finished_keeps (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) (expected : Keys) :
    Keeps expected (finished (n := n) (Auxiliary := Auxiliary) setup source wire index owner pending oneTime packet) := by
  unfold finished
  cases pending.aborted_state with
  | fail error | div => exact pure_keeps expected _
  | ok aborted =>
      dsimp only
      apply bind_keeps expected _ _ (phase_keeps expected index (.aborted aborted))
      intro _
      apply bind_keeps expected _ _ (simulate_keeps expected _ (authentication_keeps setup source expected) _)
      intro authenticated
      cases authenticated with
      | fail error | div => exact abort_pure_keeps owner expected _
      | ok answer => cases answer with
        | Err previous => exact abort_pure_keeps owner expected _
        | Ok accepted =>
            apply bind_keeps expected _ _ (simulate_keeps expected _ (agreement_keeps setup owner oneTime expected) _)
            intro agreed
            cases agreed with
            | fail error | div => exact abort_pure_keeps owner expected _
            | ok effect =>
                cases effect
                all_goals first
                  | exact abort_pure_keeps owner expected _
                  | apply bind_keeps expected _ _ (simulate_keeps expected _ (record_keeps setup wire expected) _)
                    intro opened
                    cases opened with
                    | fail error | div => exact abort_pure_keeps owner expected _
                    | ok reply => cases reply with
                      | Err previous => exact abort_pure_keeps owner expected _
                      | Ok established =>
                          apply bind_keeps expected _ _ (lift_keeps expected _)
                          intro installed
                          cases installed with
                          | false => exact abort_pure_keeps owner expected _
                          | true => exact bind_keeps expected _ _ (phase_keeps expected index _) (fun _ => pure_keeps expected _)

/-- Actual response authentication, KEM agreement, first-record opening and every terminal abort retain the entire owner's indexed KEM metadata. -/
theorem finish_metadata (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (supported : result ∈ support (((finish (n := n) setup source wire index packet).run owners).run env)) :
    result.1.2.map metadata = owners.map metadata := by
  simp only [finish, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none => simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; rfl
  | some owner =>
      rw [found] at supported
      cases phase : owner.phase <;> simp only [phase] at supported
      all_goals try { simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; rfl }
      case initSent pending oneTime =>
        exact (finished_keeps setup source wire index owner pending oneTime packet _)
          owners env result rfl supported

end BeaconcryptCore.Computational.RegistrationNativeKemBirthLifecycle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthLifecycle.bundle_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthLifecycle.bundle_metadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthLifecycle.finish_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthLifecycle.finish_metadata
