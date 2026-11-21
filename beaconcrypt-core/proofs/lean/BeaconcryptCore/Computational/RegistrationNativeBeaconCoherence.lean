-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape

/-! Every retained native InitSent capability has its actual control and server-pin binding aligned. The property follows from the generated outgoing controller and is preserved through failed signing, publication, authentication, record opening and installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def PhaseCoherent : Phase → Prop
  | .initSent pending _ => pending.control.expected_server_binding = pending.binding.server_pin.binding
  | _ => True

def Holds (owners : State source) : Prop := ∀ owner ∈ owners, PhaseCoherent owner.phase

private def Keeps (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env result, Holds owners → result ∈ support ((work.run owners).run env) → Holds result.1.2

private theorem pure_keeps (value : Value) : Keeps (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

private theorem bind_keeps {Next : Type} (work : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Next) (first : Keeps work)
    (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro owners env result prior supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owners env middle prior reached) continued

private theorem lift_keeps (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Keeps (StateT.lift work : M n KemSK source Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _reached, returned⟩ := supported
  cases returned
  exact prior

private theorem readonly_keeps (work : M n KemSK source Auxiliary Value)
    (readonly : RegistrationNativeBeaconFootprint.ReadOnly work) : Keeps work := by
  intro owners env result prior supported
  rw [readonly owners env result supported]
  exact prior

private theorem simulate_keeps {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (law : ∀ query, Keeps (implementation query)) (work : OracleComp spec Value) :
    Keeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps _ _ (law query) ih

private theorem sample_keeps (work : ProbComp Value) :
    Keeps (sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work) :=
  simulate_keeps (fun (query : unifSpec.Domain) => effect (.inl query)) (fun _ => lift_keeps _) work

private theorem current_keeps (index : Nat) (change : Owner source → Owner source)
    (valid : ∀ owner, PhaseCoherent owner.phase → PhaseCoherent (change owner).phase) :
    Keeps ((modify fun owners => match owners[index]? with
      | none => owners
      | some current => owners.set index (change current)) : M n KemSK source Auxiliary Unit) := by
  intro owners env result prior supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => exact prior
  | some owner =>
      intro selected member
      rcases List.mem_or_eq_of_mem_set member with original | rfl
      · exact prior selected original
      · exact valid owner (prior owner (List.mem_of_getElem? found))

private theorem phase_keeps (index : Nat) (phase : Phase) (valid : PhaseCoherent phase) :
    Keeps (updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) index phase) :=
  current_keeps index (fun owner => { owner with phase }) (fun _ _ => valid)

private theorem log_keeps (index : Nat) (message : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Keeps (logEd (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) index message signature) :=
  current_keeps index (fun owner => { owner with edHistory := owner.edHistory ++ [.signed message signature] })
    (fun _ valid => valid)

private theorem outgoing_keeps (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  classical
  rcases query with (hashRequest | signRequest) | edRequest
  · exact lift_keeps _
  · exact pure_keeps _
  · simp only [outgoing]
    split
    · exact bind_keeps _ _ (log_keeps index _ _) (fun _ => pure_keeps _)
    · exact pure_keeps _

private noncomputable def bundled (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
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

private theorem bundled_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Keeps (bundled (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime) := by
  intro owners env result prior supported
  simp only [bundled, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  have retained := (simulate_keeps (outgoing setup source index owner)
    (outgoing_keeps setup index owner) _) owners env middle prior reached
  cases actual : middle.1.1 with
  | fail error | div =>
      simp only [actual, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact retained
  | ok published => cases published with
    | Err previous =>
        simp only [actual, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        exact retained
    | Ok published =>
        have native := RegistrationNativeBeaconPublication.nested_support source (outgoing setup source index owner)
          (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
            ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
          owners middle.1.2 env middle.2 (.ok (.Ok published)) (by simpa only [← actual] using reached)
        have valid := RegistrationBeaconInitExecutor.begin_coherent wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin published native
        simp only [actual] at continued
        exact (bind_keeps _ _ (phase_keeps index (.initSent published.pending oneTime) valid)
          (fun _ => bind_keeps _ _ (lift_keeps _) (fun _ => pure_keeps _)))
          middle.1.2 middle.2 result retained continued

/-- Every actual outgoing bundle preserves coherence of every retained pending capability, on success and failure. -/
theorem bundle_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary) (prior : Holds owners)
    (supported : result ∈ support (((bundle (n := n) setup source wire index).run owners).run env)) :
    Holds result.1.2 := by
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none => simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; exact prior
  | some owner =>
      rw [found] at supported
      cases phase : owner.phase <;> simp only [phase] at supported
      all_goals try { simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; exact prior }
      case fresh =>
        exact (bind_keeps _ _ (sample_keeps _) (fun oneTime => bundled_keeps setup wire index owner oneTime))
          owners env result prior supported
      case freshWithCoins oneTime => exact (bundled_keeps setup wire index owner oneTime) owners env result prior supported

/-- Successful native creation adds a fresh owner; all constructor failures retain every prior coherent capability. -/
theorem create_keeps (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Nat) × State source) × EnvState Auxiliary) (prior : Holds owners)
    (supported : result ∈ support (((create (n := n) setup source edPin mlPin keyId).run owners).run env)) :
    Holds result.1.2 := by
  rw [RegistrationNativeBeaconBirth.create_program] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨earlier, reached, continued⟩ := supported
  have retained := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env earlier reached
  cases actual : earlier.1.1 with
  | fail error | div =>
      simp only [actual, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      simpa only [retained] using prior
  | ok prepared => cases prepared with
    | none =>
        simp only [actual, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        simpa only [retained] using prior
    | some prepared =>
        simp only [actual] at continued
        rw [RegistrationNativeBeaconBirth.append_program] at continued
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at continued
        obtain ⟨born, _generated, worldOwner, _allocated, returned⟩ := continued
        cases returned
        rw [retained]
        intro selected member
        rcases List.mem_append.mp member with previous | fresh
        · exact prior selected previous
        · simp only [List.mem_singleton] at fresh
          subst selected
          trivial

private theorem authentication_keeps (setup : Setup base KemSK)
    (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    Keeps (authentication (n := n) (Auxiliary := Auxiliary) setup source query) :=
  readonly_keeps _ (RegistrationNativeBeaconFootprint.authentication_readonly setup query)

private theorem agreement_keeps (setup : Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Spec.Domain) :
    Keeps (agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) :=
  readonly_keeps _ (RegistrationNativeBeaconFootprint.agreement_readonly setup owner oneTime query)

private theorem record_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Spec.Domain) :
    Keeps (record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire query) :=
  readonly_keeps _ (RegistrationNativeBeaconFootprint.record_readonly setup wire query)

private theorem abort_pure_keeps (owner : Owner source) (value : Value) :
    Keeps ((abort owner *> pure value) : M n KemSK source Auxiliary Value) := by
  rw [seqRight_eq_bind]
  exact bind_keeps _ _ (readonly_keeps _ (RegistrationNativeBeaconFootprint.abort_readonly owner))
    (fun _ => pure_keeps value)

attribute [local irreducible] RegistrationResponseExecutor.begin RegistrationAgreementExecutor.beacon
  RegistrationBeaconRecordExecutor.begin

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
    (packet : Option registration.ResponsePacket) :
    Keeps (finished (n := n) (Auxiliary := Auxiliary) setup source wire index owner pending oneTime packet) := by
  unfold finished
  cases pending.aborted_state with
  | fail error | div => exact pure_keeps _
  | ok aborted =>
      dsimp only
      apply bind_keeps _ _ (phase_keeps index (.aborted aborted) (by trivial))
      intro _
      apply bind_keeps _ _ (simulate_keeps _ (authentication_keeps setup) _)
      intro authenticated
      cases authenticated with
      | fail error | div => exact abort_pure_keeps owner _
      | ok answer => cases answer with
        | Err previous => exact abort_pure_keeps owner _
        | Ok accepted =>
            apply bind_keeps _ _ (simulate_keeps _ (agreement_keeps setup owner oneTime) _)
            intro agreed
            cases agreed with
            | fail error | div => exact abort_pure_keeps owner _
            | ok effect =>
                cases effect
                all_goals first
                  | exact abort_pure_keeps owner _
                  | apply bind_keeps _ _ (simulate_keeps _ (record_keeps setup wire) _)
                    intro opened
                    cases opened with
                    | fail error | div => exact abort_pure_keeps owner _
                    | ok reply => cases reply with
                      | Err previous => exact abort_pure_keeps owner _
                      | Ok established =>
                          apply bind_keeps _ _ (lift_keeps _)
                          intro installed
                          cases installed with
                          | false => exact abort_pure_keeps owner _
                          | true => exact bind_keeps _ _ (phase_keeps index _ (by trivial)) (fun _ => pure_keeps _)

/-- Finishing consumes the pending phase before authentication and preserves coherence of all surviving pending capabilities, on every failure and installation branch. -/
theorem finish_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary) (prior : Holds owners)
    (supported : result ∈ support (((finish (n := n) setup source wire index packet).run owners).run env)) :
    Holds result.1.2 := by
  simp only [finish, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none =>
      simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact prior
  | some owner =>
      rw [found] at supported
      cases phase : owner.phase <;> simp only [phase] at supported
      all_goals first
        | (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; exact prior)
        | exact (finished_keeps setup source wire index owner _ _ packet) owners env result prior supported

/-- Lookup of any retained InitSent owner recovers actual pending control/server-pin coherence. -/
theorem pending (owners : State source) (valid : Holds owners) (index : Nat) (owner : Owner source)
    (found : owners[index]? = some owner) (selected : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (phase : owner.phase = .initSent selected oneTime) :
    selected.control.expected_server_binding = selected.binding.server_pin.binding := by
  have aligned := valid owner (List.mem_of_getElem? found)
  simpa only [phase, PhaseCoherent] using aligned

end BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence.bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence.bundle_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence.create_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence.create_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence.finish_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence.finish_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence.pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence.pending
