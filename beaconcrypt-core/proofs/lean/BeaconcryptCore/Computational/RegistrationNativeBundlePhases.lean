-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBundleInitReceipt
import BeaconcryptCore.Computational.RegistrationNativePendingFrames

/-! Outgoing callbacks change Ed histories but retain every lifecycle phase. An actual bundle changes at most its selected phase, and such a change returns the actual successful encoded Init. These source facts include all primitive and encoder failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBundlePhases
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def phases (owners : State source) : List Phase := owners.map Owner.phase

def masked (index : Nat) (owners : State source) : List Phase := (phases owners).set index .fresh

private def Stable (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → phases result.1.2 = phases owners

private theorem pure_stable (value : Value) : Stable (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem bind_stable (work : M n KemSK source Auxiliary Value) (next : Value → M n KemSK source Auxiliary Next)
    (first : Stable work) (later : ∀ value, Stable (next value)) : Stable (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (later middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle called)

private theorem lift_stable (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Stable (StateT.lift work : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  rfl

private theorem simulated_stable {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary)) (steps : ∀ query, Stable (implementation query))
    (work : OracleComp spec Value) : Stable (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_stable value
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact bind_stable _ _ (steps query) ih

private theorem sample_stable (draw : ProbComp Value) :
    Stable (sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) draw) :=
  simulated_stable _ (fun _ => lift_stable _) draw

private theorem log_stable (index : Nat) (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Stable (logEd (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) index message signature) := by
  intro owners env result supported
  simp only [logEd, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
    simp only [phases, List.map_set]
    have mapped : (owners.map Owner.phase)[index]? = some owner.phase := by simp only [List.getElem?_map, found, Option.map_some]
    obtain ⟨below, selected⟩ := List.getElem?_eq_some_iff.mp mapped
    rw [← selected]
    exact List.set_getElem_self below

private theorem outgoing_stable (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Stable (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  classical
  rcases query with (hashRequest | signRequest) | edRequest
  · exact lift_stable _
  · exact pure_stable _
  · simp only [outgoing]
    split
    · exact bind_stable _ _ (log_stable index _ _) (fun _ => pure_stable _)
    · exact pure_stable _

/-- Every actual outgoing source execution retains the complete phase roster under all Ed, ML and shared hash replies. -/
theorem outgoing_phases (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (Value × State source) × EnvState Auxiliary)
    (supported : result ∈ support (((simulateQ (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner) work).run owners).run env)) :
    phases result.1.2 = phases owners := simulated_stable _ (outgoing_stable setup index owner) work owners env result supported


def Shape (target : Nat) (before : State source) (reply : RustM (Option Pqxdh.Bytes)) (after : State source) : Prop :=
  phases after = phases before ∨ ∃ bytes, reply = .ok (some bytes) ∧ masked target after = masked target before

private def setPhase (index : Nat) (phase : Phase) (owners : State source) : State source :=
  match owners[index]? with
  | none => owners
  | some owner => owners.set index { owner with phase }

private theorem masked_set (index : Nat) (phase : Phase) (owners : State source) :
    masked index (setPhase index phase owners) = masked index owners := by
  cases found : owners[index]? with
  | none => simp only [setPhase, found]
  | some owner => simp only [setPhase, found, masked, phases, List.map_set, List.set_set]

private theorem prefix_shape (target : Nat) (first middle last : State source)
    (reply : RustM (Option Pqxdh.Bytes)) (unchanged : phases middle = phases first)
    (later : Shape target middle reply last) : Shape target first reply last := by
  rcases later with same | ⟨bytes, returned, same⟩
  · exact Or.inl (same.trans unchanged)
  · exact Or.inr ⟨bytes, returned, same.trans (congrArg (fun current => current.set target .fresh) unchanged)⟩

private noncomputable def next (target : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) :=
  match reply with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok published) => do
    updatePhase target (.initSent published.pending oneTime)
    let _ ← effect (.inr (.advanceOwner owner.worldOwner .initSent))
    pure (.ok (some published.encoded))

private theorem next_shape (target : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (supported : result ∈ support (((next (n := n) (KemSK := KemSK) target owner oneTime reply).run owners).run env)) :
    Shape target owners result.1.1 result.1.2 := by
  cases reply with
  | fail error | div =>
    simp only [next, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact Or.inl rfl
  | ok answer => cases answer with
    | Err previous =>
      simp only [next, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl rfl
    | Ok published =>
      simp only [next, updatePhase, StateT.run_bind, StateT.run_modify, pure_bind, mem_support_bind_iff] at supported
      obtain ⟨advanced, called, returned⟩ := supported
      have retained : phases advanced.1.2 = phases (setPhase target (.initSent published.pending oneTime) owners) :=
        (lift_stable _) _ _ advanced called
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at returned
      cases returned
      exact Or.inr ⟨published.encoded, rfl,
        (congrArg (fun current => current.set target .fresh) retained).trans (masked_set target _ owners)⟩

private noncomputable def bundled (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (target : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let published ← simulateQ (outgoing setup source target owner)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
  next target owner oneTime published

private theorem bundled_shape (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (target : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (supported : result ∈ support (((bundled (n := n) setup wire target owner oneTime).run owners).run env)) :
    Shape target owners result.1.1 result.1.2 := by
  simp only [bundled, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact prefix_shape target owners middle.1.2 result.1.2 result.1.1
    (outgoing_phases setup target owner _ owners env middle called)
    (next_shape target owner oneTime middle.1.1 middle.1.2 middle.2 result continued)

/-- Every actual bundle changes no phase, or returns its successful Init bytes while changing only its selected phase. -/
theorem source_shape (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (target : Nat)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (supported : result ∈ support (((bundle (n := n) setup source wire target).run owners).run env)) :
    Shape target owners result.1.1 result.1.2 := by
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[target]? with
  | none =>
    simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact Or.inl rfl
  | some owner =>
    rw [found] at supported
    cases phase : owner.phase with
    | fresh =>
      simp only [phase] at supported
      change result ∈ support (((sample PqxdhJointGapDh.sampleScalar >>= bundled setup wire target owner).run owners).run env) at supported
      simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨sampled, called, continued⟩ := supported
      exact prefix_shape target owners sampled.1.2 result.1.2 result.1.1
        (sample_stable _ owners env sampled called)
        (bundled_shape setup wire target owner sampled.1.1 sampled.1.2 sampled.2 result continued)
    | freshWithCoins oneTime =>
      simp only [phase] at supported
      exact bundled_shape setup wire target owner oneTime owners env result supported
    | initSent pending oneTime | established completed | aborted control =>
      simp only [phase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl rfl


/-- Original native closure retains the same source phase-change alternative for every failed or successful bundle. -/
theorem typed_shape (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (target : Nat) (before after : RegistrationNativeExperiment.State n KemSK source)
    (reply : RustM (Option Pqxdh.Bytes))
    (supported : (reply, after) ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation
      created source credential (.inr (.bundle target))).run before)) : Shape target before.beacons reply after.beacons := by
  change (reply, after) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
    (bundle setup source wire target)).run before) at supported
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  have original : inner.1 ∈ support (((bundle (n := n) setup source wire target).run before.beacons).run
      (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst possible
  have shape := source_shape setup wire target before.beacons _ inner.1 original
  cases same
  exact shape

private theorem pending_lookup (before after : State source) (index : Nat)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (same : (phases after)[index]? = (phases before)[index]?)
    (present : RegistrationNativePendingFrames.PendingAt after index pending oneTime) :
    RegistrationNativePendingFrames.PendingAt before index pending oneTime := by
  obtain ⟨owner, found, phase⟩ := present
  have actual : (phases after)[index]? = some (.initSent pending oneTime) := by
    simp only [phases, List.getElem?_map, found, Option.map_some, phase]
  rw [same] at actual
  simp only [phases, List.getElem?_map] at actual
  obtain ⟨earlier, earlierFound, earlierPhase⟩ := Option.map_eq_some_iff.mp actual
  exact ⟨earlier, earlierFound, earlierPhase⟩

/-- An exact pending capability after an original bundle is inherited from its prior state, or was created by this same successful bundle at its own slot. -/
theorem typed_pending (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (target : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (reply : RustM (Option Pqxdh.Bytes))
    (supported : (reply, after) ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation
      created source credential (.inr (.bundle target))).run before))
    (index : Nat) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (present : RegistrationNativePendingFrames.PendingAt after.beacons index pending oneTime) :
    RegistrationNativePendingFrames.PendingAt before.beacons index pending oneTime ∨
      ∃ bytes, index = target ∧ reply = .ok (some bytes) ∧
        RegistrationNativeBundleInitReceipt.Receipt setup wire target before after bytes := by
  rcases typed_shape setup checks wire route representation created credential target before after reply supported with unchanged | ⟨bytes, returned, same⟩
  · exact Or.inl (pending_lookup before.beacons after.beacons index pending oneTime
      (congrArg (fun current => current[index]?) unchanged) present)
  · by_cases selected : index = target
    · exact Or.inr ⟨bytes, selected, returned,
        RegistrationNativeBundleInitReceipt.typed_receipt setup checks wire route representation created credential target before after bytes
          (by simpa only [returned] using supported)⟩
    · have atIndex := congrArg (fun current => current[index]?) same
      simp only [masked, List.getElem?_set_ne (Ne.symm selected)] at atIndex
      exact Or.inl (pending_lookup before.beacons after.beacons index pending oneTime atIndex present)

end BeaconcryptCore.Computational.RegistrationNativeBundlePhases
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundlePhases.outgoing_phases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundlePhases.outgoing_phases

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundlePhases.source_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundlePhases.source_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundlePhases.typed_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundlePhases.typed_shape
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundlePhases.typed_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundlePhases.typed_pending
