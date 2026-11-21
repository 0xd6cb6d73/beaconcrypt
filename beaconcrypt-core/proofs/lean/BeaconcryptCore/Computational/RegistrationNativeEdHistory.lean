-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEdSigningBounds
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
import BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint

/-! The actual indexed native signing callback extends its current owner's history before returning to the source controller. The history invariant is maintained for rejected callbacks and failed final publication. It is attached to generated owner indices, independently of public-key aliases. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEdHistory
open RegistrationNativeBeaconFrontend
open RegistrationNativeEdOrigin (Allowed FixedPrekey)
open PqxdhEd25519EufCma (X25519PublicKey Ed25519Signature)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def Fixed (owners : State mlSource) : Prop :=
  ∀ owner ∈ owners, FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory

def At (index : Nat) (prekey : X25519PublicKey) (owners : State mlSource) : Prop :=
  ∀ current, owners[index]? = some current → PqxdhPhase2InputBytes.word current.prekeyPublic = prekey

def Inv (index : Nat) (prekey : X25519PublicKey) (owners : State mlSource) : Prop := At index prekey owners ∧ Fixed owners

def Preserves (invariant : State mlSource → Prop) (work : M n KemSK mlSource Auxiliary Value) : Prop :=
  ∀ owners env result, invariant owners → result ∈ support ((work.run owners).run env) → invariant result.1.2

private theorem pure_preserves (invariant : State mlSource → Prop) (value : Value) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) invariant (pure value) := by
  intro owners env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

private theorem bind_preserves {Next : Type} (invariant : State mlSource → Prop)
    (work : M n KemSK mlSource Auxiliary Value) (next : Value → M n KemSK mlSource Auxiliary Next)
    (first : Preserves invariant work) (later : ∀ value, Preserves invariant (next value)) :
    Preserves invariant (work >>= next) := by
  intro owners env result prior supported
  rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨value, currentOwners⟩, currentEnv⟩, reached, continued⟩ := supported
  exact later value currentOwners currentEnv result (first owners env _ prior reached) continued

private theorem lift_preserves (invariant : State mlSource → Prop)
    (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Preserves invariant (StateT.lift work) := by
  intro owners env result prior supported
  simp only [StateT.run_lift, bind_pure_comp] at supported
  rw [StateT.run_map, support_map] at supported
  obtain ⟨_, _, rfl⟩ := supported
  exact prior

private theorem simulate_preserves {Query : Type} {spec : OracleSpec Query} (invariant : State mlSource → Prop)
    (implementation : QueryImpl spec (M n KemSK mlSource Auxiliary))
    (allowed : Query → Prop) (step : ∀ query, allowed query → Preserves invariant (implementation query))
    (work : OracleComp spec Value) (bounded : AllQueriesSatisfy work allowed) :
    Preserves invariant (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_preserves invariant value
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_preserves invariant _ _ (step query bounded.1) (fun value => ih value (bounded.2 value))

private theorem sample_preserves (invariant : State mlSource → Prop) (work : ProbComp Value) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) invariant (sample work) := by
  unfold sample
  apply simulate_preserves invariant (fun (query : unifSpec.Domain) => effect (.inl query)) (fun _ => True)
    (fun _ _ => lift_preserves invariant _)
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩

private theorem current_inv (index : Nat) (prekey : X25519PublicKey) (owners : State mlSource)
    (change : Owner mlSource → Owner mlSource)
    (same : ∀ current, (change current).prekeyPublic = current.prekeyPublic)
    (fixedChange : ∀ current, PqxdhPhase2InputBytes.word current.prekeyPublic = prekey →
      FixedPrekey (PqxdhPhase2InputBytes.word current.prekeyPublic) current.edHistory →
      FixedPrekey (PqxdhPhase2InputBytes.word (change current).prekeyPublic) (change current).edHistory)
    (prior : Inv index prekey owners) :
    Inv index prekey (match owners[index]? with | none => owners | some current => owners.set index (change current)) := by
  cases found : owners[index]? with
  | none => exact prior
  | some current =>
      obtain ⟨below, _⟩ := List.getElem?_eq_some_iff.mp found
      refine ⟨?_, ?_⟩
      · intro selected selectedAt
        rw [List.getElem?_set_self below] at selectedAt
        cases selectedAt
        simpa only [same] using prior.1 current found
      · intro selected member
        rcases List.mem_or_eq_of_mem_set member with original | rfl
        · exact prior.2 selected original
        · exact fixedChange current (prior.1 current found) (prior.2 current (List.mem_of_getElem? found))

theorem phase_preserves (index : Nat) (prekey : X25519PublicKey) (phase : Phase) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource)
      (Inv index prekey) (updatePhase index phase) := by
  intro owners env result prior supported
  simp only [updatePhase, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact current_inv index prekey owners (fun current => { current with phase }) (fun _ => rfl)
    (fun _ _ fixed => fixed) prior

theorem log_preserves (index : Nat) (prekey : X25519PublicKey)
    (message : Pqxdh.Bytes) (signature : Ed25519Signature) (allowed : Allowed prekey message) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource)
      (Inv index prekey) (logEd index message signature) := by
  intro owners env result prior supported
  simp only [logEd, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  apply current_inv index prekey owners (fun current => { current with edHistory := current.edHistory ++ [.signed message signature] })
    (fun _ => rfl) _ prior
  intro current same fixed
  exact RegistrationNativeEdOrigin.fixed_signed _ _ fixed message signature (same.symm ▸ allowed)

theorem outgoing_preserves (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) (query : RegistrationBeaconInitExecutor.Spec.Domain)
    (allowed : RegistrationNativeEdSigningBounds.AllowedQuery (PqxdhPhase2InputBytes.word owner.prekeyPublic) query) :
    Preserves (n := n) (Auxiliary := Auxiliary) (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic))
      (outgoing setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact lift_preserves _ _
    | sign request payload digest => exact pure_preserves _ _
  | inr request =>
      classical
      by_cases matching : request.public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519
      · simp only [outgoing, matching, ite_true]
        exact bind_preserves _ _ _ (log_preserves index _ _ _ allowed) (fun _ => pure_preserves _ _)
      · simp only [outgoing, ite_eq_right matching]
        exact pure_preserves _ _

/-- The full actual three-Ed/request-hash/publication controller preserves every owner's fixed-prekey signing history on all return paths. -/
theorem init_preserves (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Preserves (n := n) (Auxiliary := Auxiliary) (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic))
      (simulateQ (outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)) := by
  apply simulate_preserves _ _ (RegistrationNativeEdSigningBounds.AllowedQuery _)
    (fun query allowed => outgoing_preserves setup source index owner query allowed)
  apply RegistrationNativeEdSigningBounds.begin_all wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin
    (PqxdhPhase2InputBytes.word owner.prekeyPublic) (setup.dh.publicKey oneTime) owner.kemPublic
  · rfl
  · exact PqxdhRootTableInitialization.rootArray_bytes _
  · simp [inputs, pqArray, PqxdhRefinement.absBytes, List.map_map, Function.comp_def]

theorem signed_attempt (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) (request : registration.Ed25519SigningRequest)
    (matching : request.public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519) :
    outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner (.inr request) = (do
      let message := TranscriptAuthParts.absSlice request.message
      let signature := setup.joint.sign owner.identitySeed message
      logEd index message signature
      pure (RegistrationAuthenticationShared.openedBytes (some (signature.toList ++ message)))) := by
  classical
  simp only [outgoing, matching, ite_true]

theorem mismatched_key (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) (request : registration.Ed25519SigningRequest)
    (different : request.public_key ≠ PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519) :
    outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner (.inr request) = pure .None := by
  classical
  simp only [outgoing, ite_eq_right different]

private noncomputable def bundled (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
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
      pure (.ok (some finished.encoded))

private theorem bundled_preserves (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Preserves (n := n) (Auxiliary := Auxiliary) (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic))
      (bundled setup source wire index owner oneTime) := by
  unfold bundled
  apply bind_preserves _ _ _ (init_preserves setup source wire index owner oneTime)
  intro published
  cases published with
  | fail error => exact pure_preserves _ _
  | div => exact pure_preserves _ _
  | ok selected => cases selected with
    | Err previous => exact pure_preserves _ _
    | Ok finished =>
        exact bind_preserves _ _ _ (phase_preserves index _ _) (fun _ =>
          bind_preserves _ _ _ (lift_preserves _ _) (fun _ => pure_preserves _ _))

/-- Every actual bundle outcome retains the fixed-prekey history invariant, including failed ML signing or dynamic encoding after the Ed attempts. -/
theorem bundle_fixed (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) :
    Preserves (n := n) (Auxiliary := Auxiliary) Fixed (bundle setup source wire index) := by
  intro owners env result prior supported
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none =>
      simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact prior
  | some owner =>
      rw [found] at supported
      have initial : Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic) owners := by
        refine ⟨?_, prior⟩
        intro current atIndex
        have equal : current = owner := Option.some.inj (atIndex.symm.trans found)
        cases equal
        rfl
      cases phase : owner.phase with
      | fresh =>
          simp only [phase] at supported
          change result ∈ support (((do
            let oneTime ← sample PqxdhJointGapDh.sampleScalar
            bundled setup source wire index owner oneTime).run owners).run env) at supported
          exact (bind_preserves _ _ _ (sample_preserves _ _) (fun oneTime =>
            bundled_preserves setup source wire index owner oneTime) owners env result initial supported).2
      | freshWithCoins oneTime =>
          simp only [phase, StateT.run_bind] at supported
          exact (bundled_preserves setup source wire index owner oneTime owners env result initial supported).2
      | _ =>
          simp only [phase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact prior

private theorem readonly_preserves (invariant : State mlSource → Prop) (work : M n KemSK mlSource Auxiliary Value)
    (readonly : RegistrationNativeBeaconFootprint.ReadOnly work) : Preserves invariant work := by
  intro owners env result prior supported
  exact (readonly owners env result supported).symm ▸ prior

theorem phase_fixed (index : Nat) (phase : Phase) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource) Fixed (updatePhase index phase) := by
  intro owners env result prior supported
  simp only [updatePhase, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => exact prior
  | some current =>
      intro selected member
      rcases List.mem_or_eq_of_mem_set member with original | rfl
      · exact prior selected original
      · exact prior current (List.mem_of_getElem? found)

private noncomputable def finished (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket) :
    M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) :=
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

private theorem abort_preserves (owner : Owner mlSource) (value : Value) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) Fixed (abort owner *> pure value) :=
  bind_preserves _ _ _ (readonly_preserves _ _ (RegistrationNativeBeaconFootprint.abort_readonly owner))
    (fun _ => pure_preserves _ _)

private theorem finished_fixed (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket) :
    Preserves (n := n) (Auxiliary := Auxiliary) Fixed (finished setup source wire index owner pending oneTime packet) := by
  unfold finished
  cases pending.aborted_state with
  | fail error => exact pure_preserves _ _
  | div => exact pure_preserves _ _
  | ok aborted =>
      apply bind_preserves _ _ _ (phase_fixed index _)
      intro _
      apply bind_preserves Fixed (simulateQ (authentication setup source)
        (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))) _
        (readonly_preserves _ _ (RegistrationNativeBeaconFootprint.program_readonly _
          (RegistrationNativeBeaconFootprint.authentication_readonly (source := source) setup) _))
      intro authenticated
      cases authenticated with
      | fail error => exact abort_preserves _ _
      | div => exact abort_preserves _ _
      | ok answer => cases answer with
        | Err previous => exact abort_preserves _ _
        | Ok accepted =>
            apply bind_preserves Fixed
              (simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon accepted)) _ (readonly_preserves _ _
              (RegistrationNativeBeaconFootprint.program_readonly _ (RegistrationNativeBeaconFootprint.agreement_readonly setup owner oneTime) _))
            intro agreed
            cases agreed with
            | fail error => exact abort_preserves _ _
            | div => exact abort_preserves _ _
            | ok effect => cases effect with
              | BeaconComplete completed =>
                  apply bind_preserves Fixed
                    (simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin completed)) _ (readonly_preserves _ _
                    (RegistrationNativeBeaconFootprint.program_readonly _ (RegistrationNativeBeaconFootprint.record_readonly setup wire) _))
                  intro opened
                  cases opened with
                  | fail error => exact abort_preserves _ _
                  | div => exact abort_preserves _ _
                  | ok answer => cases answer with
                    | Err previous => exact abort_preserves _ _
                    | Ok established =>
                        apply bind_preserves Fixed (effect (.inr (.installBeacon owner.worldOwner
                          ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩
                          (.known established.kernel)))) _ (lift_preserves _ _)
                        intro installed
                        cases installed with
                        | false => exact abort_preserves _ _
                        | true => exact bind_preserves _ _ _ (phase_fixed index _) (fun _ => pure_preserves _ _)
              | _ => exact abort_preserves _ _

/-- Terminal malformed-response consumption and every later verification, root and opening failure retain the complete chronological Ed histories. -/
theorem finish_fixed (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    Preserves (n := n) (Auxiliary := Auxiliary) Fixed (finish setup source wire index packet) := by
  intro owners env result prior supported
  simp only [finish, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none =>
      simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact prior
  | some owner =>
      rw [found] at supported
      cases phase : owner.phase with
      | initSent pending oneTime =>
          simp only [phase] at supported
          exact finished_fixed setup source wire index owner pending oneTime packet owners env result prior supported
      | _ =>
          simp only [phase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact prior

end BeaconcryptCore.Computational.RegistrationNativeEdHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistory.phase_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistory.phase_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistory.log_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistory.log_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistory.outgoing_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistory.outgoing_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistory.init_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistory.init_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistory.signed_attempt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistory.signed_attempt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistory.mismatched_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistory.mismatched_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistory.bundle_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistory.bundle_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistory.phase_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistory.phase_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdHistory.finish_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdHistory.finish_fixed
