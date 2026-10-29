-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape
import BeaconcryptCore.Computational.RegistrationNativeOwnerFields
import BeaconcryptCore.Computational.RegistrationBeaconInitPinSource

/-! Every retained native InitSent capability has its actual control and server-pin binding aligned. The property follows from the generated outgoing controller and is preserved through failed signing, publication, authentication, record opening and installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinNative
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def Coherent (owner : Owner source) : Prop :=
  match owner.phase with
  | .initSent pending _ => pending.control.expected_server_binding = owner.pin.binding
  | _ => True

def Holds (owners : State source) : Prop := ∀ owner ∈ owners, Coherent owner

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

private theorem lift_readonly (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    RegistrationNativeBeaconFootprint.ReadOnly (StateT.lift work : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _reached, returned⟩ := supported
  cases returned
  rfl

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

private theorem sample_readonly (work : ProbComp Value) :
    RegistrationNativeBeaconFootprint.ReadOnly
      (sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work) := by
  unfold sample
  apply RegistrationNativeBeaconFootprint.program_readonly
  intro query
  exact lift_readonly _

private theorem current_keeps (index : Nat) (change : Owner source → Owner source)
    (valid : ∀ owner, Coherent owner → Coherent (change owner)) :
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
  · exact bind_keeps _ _ (sample_keeps _) (fun _ =>
      bind_keeps _ _ (lift_keeps _) (fun _ => pure_keeps _))
  · simp only [outgoing]
    split
    · exact bind_keeps _ _ (log_keeps index _ _) (fun _ => pure_keeps _)
    · exact pure_keeps _

private noncomputable def bundled (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
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

private theorem bundled_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (prior : Holds owners) (found : owners[index]? = some owner)
    (supported : result ∈ support (((bundled (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime).run owners).run env)) :
    Holds result.1.2 := by
  simp only [bundled, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  have retained := (simulate_keeps (outgoing setup source index owner)
    (outgoing_keeps setup index owner) _) owners env middle prior reached
  cases actual : middle.1.1 with
  | fail error | div =>
      simp only [actual, StateT.run_pure, mem_support_pure_iff] at continued
      cases continued
      exact retained
  | ok published => cases published with
    | Err previous =>
        simp only [actual, StateT.run_pure, mem_support_pure_iff] at continued
        cases continued
        exact retained
    | Ok published =>
        have fields := RegistrationNativeOwnerFields.outgoing_metadata setup source index owner _ owners env middle reached
        have same := congrArg (fun roster => roster[index]?) fields
        simp only [List.getElem?_map, found, Option.map_some] at same
        obtain ⟨current, currentFound, currentMetadata⟩ := Option.map_eq_some_iff.mp same
        have pin : current.pin.binding = owner.pin.binding := congrArg (fun owner => owner.pin.binding) currentMetadata
        have native := RegistrationNativeBeaconPublication.nested_support source (outgoing setup source index owner)
          (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
            ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
          owners middle.1.2 env middle.2 (.ok (.Ok published)) (by simpa only [← actual] using reached)
        have expected := RegistrationBeaconInitPinSource.begin_coherent wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey published native
        have installed : Holds (middle.1.2.set index { current with phase := .initSent published.pending oneTime }) := by
          intro selected member
          rcases List.mem_or_eq_of_mem_set member with original | rfl
          · exact retained selected original
          · change published.pending.control.expected_server_binding = current.pin.binding
            exact expected.trans pin.symm
        simp only [actual, updatePhase, StateT.run_bind, StateT.run_modify, pure_bind, currentFound] at continued
        let suffix : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
          let _ ← effect (.inr (.advanceOwner owner.worldOwner .initSent))
          pure (.ok (some published.encoded))
        have kept : Keeps suffix := bind_keeps _ _ (lift_keeps _) (fun _ => pure_keeps _)
        apply kept (middle.1.2.set index { current with phase := .initSent published.pending oneTime }) middle.2 result installed
        simpa only [suffix, StateT.run_bind] using continued

/-- The actual outgoing bundle derives each installed pending control from that same indexed owner's stored pin. -/
theorem bundle_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary) (prior : Holds owners)
    (supported : result ∈ support (((bundle (n := n) setup source wire index).run owners).run env)) :
    Holds result.1.2 := by
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none =>
      simp only [found, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact prior
  | some owner =>
      rw [found] at supported
      cases phase : owner.phase <;> simp only [phase] at supported
      all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; exact prior }
      case fresh =>
        simp only [StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨sampled, draw, continued⟩ := supported
        have unchanged := sample_readonly _ owners env sampled draw
        have kept : Holds sampled.1.2 := by rw [unchanged]; exact prior
        apply bundled_keeps (n := n) setup wire index owner sampled.1.1 sampled.1.2 sampled.2 result kept
        · rw [unchanged]
          exact found
        · simp only [bundled, StateT.run_bind, mem_support_bind_iff]
          obtain ⟨published, called, tail⟩ := continued
          refine ⟨published, called, ?_⟩
          cases actual : published.1.1 with
          | fail error | div => simpa only [actual] using tail
          | ok reply => cases reply <;> simpa only [actual] using tail
      case freshWithCoins oneTime =>
        exact bundled_keeps setup wire index owner oneTime owners env result prior found supported

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

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinNative
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinNative.bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinNative.bundle_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinNative.create_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinNative.create_keeps
