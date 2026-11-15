-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape
import BeaconcryptCore.Computational.RegistrationNativePublicOwners

/-! Terminal local owners cannot be recreated or bundled again. These actual source facts retain owner positions through constructor append and all failed outgoing callbacks. Scalar restoration and public packing keep phases unchanged; no KEM handle is identified with a local owner index. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerPhase
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (Phase Owner M Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Terminal : Phase → Prop
  | .established _ | .aborted _ => True
  | _ => False
instance : DecidablePred Terminal := fun phase => by
  cases phase with
  | fresh | freshWithCoins _ | initSent _ _ => exact isFalse id
  | established _ | aborted _ => exact isTrue trivial

def NativeDone (index : Nat) (owners : RegistrationNativeBeaconFrontend.State source) : Prop :=
  ∃ owner, owners[index]? = some owner ∧ Terminal owner.phase

def Done (index : Nat) (owners : RegistrationNativePublicOwners.State source) : Prop :=
  ∃ owner, owners[index]? = some owner ∧ Terminal owner.view.phase

private theorem set_foreign (index target : Nat) (different : index ≠ target)
    (owners : RegistrationNativeBeaconFrontend.State source) (owner : Owner source) (valid : NativeDone index owners) :
    NativeDone index (owners.set target owner) := by
  obtain ⟨earlier, found, terminal⟩ := valid
  exact ⟨earlier, by simpa only [List.getElem?_set_ne (Ne.symm different)] using found, terminal⟩

/-- Appending an actual new owner cannot retarget any earlier terminal owner. -/
theorem append_done (index : Nat) (owners : RegistrationNativeBeaconFrontend.State source)
    (owner : Owner source) (valid : NativeDone index owners) : NativeDone index (owners ++ [owner]) := by
  obtain ⟨earlier, found, terminal⟩ := valid
  exact ⟨earlier, by simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found, terminal⟩

/-- Native constructor failure preserves the old roster and success appends; both retain earlier terminal positions. -/
theorem create_done (setup : Setup base KemSK) (index : Nat) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : EnvState Auxiliary) (result : (RustM (Option Nat) × RegistrationNativeBeaconFrontend.State source) × EnvState Auxiliary)
    (valid : NativeDone index owners) (supported : result ∈ support
      (((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run owners).run env)) :
    NativeDone index result.1.2 := by
  rcases result with ⟨⟨reply, afterOwners⟩, afterEnv⟩
  have shape := RegistrationNativeKemBirthCreateShape.create_shape setup source edPin mlPin keyId owners env
    reply afterOwners afterEnv supported
  cases reply with
  | fail error | div =>
      simp only [RegistrationNativeKemBirthCreateShape.Shape] at shape
      rw [shape]
      exact valid
  | ok reply => cases reply with
    | none =>
        simp only [RegistrationNativeKemBirthCreateShape.Shape] at shape
        rw [shape]
        exact valid
    | some assigned =>
        obtain ⟨_assigned, owner, changed⟩ := shape
        rw [changed]
        exact append_done index owners owner valid

private def Keeps (index : Nat) (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env result, NativeDone index owners → result ∈ support ((work.run owners).run env) → NativeDone index result.1.2

private theorem pure_keeps (index : Nat) (value : Value) : Keeps index (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env result valid supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact valid

private theorem bind_keeps (index : Nat) (work : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Next) (first : Keeps index work)
    (later : ∀ value, Keeps index (next value)) : Keeps index (work >>= next) := by
  intro owners env result valid supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, stepped, continued⟩ := supported
  exact later middle.1.1 middle.1.2 middle.2 result (first owners env middle valid stepped) continued

private theorem lift_keeps (index : Nat) (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Keeps index (StateT.lift work : M n KemSK source Auxiliary Value) := by
  intro owners env result valid supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _stepped, equal⟩ := supported
  cases equal
  exact valid

private theorem simulate_keeps {Query : Type} {spec : OracleSpec Query} (index : Nat)
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (law : ∀ query, Keeps index (implementation query)) (work : OracleComp spec Value) :
    Keeps index (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps index value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps index _ _ (law query) ih

private theorem sample_keeps (index : Nat) (work : ProbComp Value) :
    Keeps index (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work) :=
  simulate_keeps index _ (fun _ => lift_keeps index _) work

private theorem log_keeps (index target : Nat) (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Keeps index (RegistrationNativeBeaconFrontend.logEd (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) target message signature) := by
  intro owners env result valid supported
  simp only [RegistrationNativeBeaconFrontend.logEd, StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  cases found : owners[target]? with
  | none => simpa only [found] using valid
  | some current =>
      by_cases same : index = target
      · subst target
        obtain ⟨old, oldAt, terminal⟩ := valid
        have equal : old = current := Option.some.inj (oldAt.symm.trans found)
        subst old
        refine ⟨{ current with edHistory := current.edHistory ++ [.signed message signature] }, ?_, terminal⟩
        exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1
      · simpa only [found] using set_foreign index target same owners _ valid

private theorem phase_keeps (index target : Nat) (different : index ≠ target) (phase : Phase) :
    Keeps index (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) target phase) := by
  intro owners env result valid supported
  simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  cases found : owners[target]? with
  | none => simpa only [found] using valid
  | some current => simpa only [found] using set_foreign index target different owners _ valid

private theorem outgoing_keeps (setup : Setup base KemSK) (index target : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps index (RegistrationNativeBeaconFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source target owner query) := by
  classical
  rcases query with (hashRequest | signRequest) | edRequest
  · exact lift_keeps index _
  · exact pure_keeps index _
  · simp only [RegistrationNativeBeaconFrontend.outgoing]
    split
    · exact bind_keeps index _ _ (log_keeps index target _ _) (fun _ => pure_keeps index _)
    · exact pure_keeps index _

private noncomputable def bundled (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (target : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let published ← simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source target owner)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
      RegistrationNativeBeaconFrontend.updatePhase target (.initSent finished.pending oneTime)
      let _ ← RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))
      pure (.ok (some finished.encoded))

private theorem bundled_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index target : Nat) (different : index ≠ target) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Keeps index (bundled (n := n) (Auxiliary := Auxiliary) setup wire target owner oneTime) := by
  unfold bundled
  apply bind_keeps index _ _ (simulate_keeps index _ (outgoing_keeps setup index target owner) _)
  intro published
  cases published with
  | fail error | div => exact pure_keeps index _
  | ok result => cases result with
    | Err previous => exact pure_keeps index _
    | Ok finished => exact bind_keeps index _ _ (phase_keeps index target different _) (fun _ =>
        bind_keeps index _ _ (lift_keeps index _) (fun _ => pure_keeps index _))

/-- Every actual bundle preserves each earlier terminal owner, including all failed signatures, hashes and publication paths. -/
theorem bundle_done (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index target : Nat)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeBeaconFrontend.State source) × EnvState Auxiliary)
    (valid : NativeDone index owners) (supported : result ∈ support
      (((RegistrationNativeBeaconFrontend.bundle (n := n) setup source wire target).run owners).run env)) :
    NativeDone index result.1.2 := by
  simp only [RegistrationNativeBeaconFrontend.bundle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[target]? with
  | none =>
      simp only [found, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | some owner =>
      rw [found] at supported
      cases phase : owner.phase <;> simp only [phase] at supported
      all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; exact valid }
      all_goals
        have different : index ≠ target := by
          intro same
          subst target
          obtain ⟨old, oldAt, terminal⟩ := valid
          have equal : old = owner := Option.some.inj (oldAt.symm.trans found)
          subst old
          simp only [phase, Terminal] at terminal
      case fresh =>
        exact (bind_keeps index _ _ (sample_keeps index _) (fun oneTime =>
          bundled_keeps setup wire index target different owner oneTime)) owners env result valid supported
      case freshWithCoins oneTime =>
        exact (bundled_keeps setup wire index target different owner oneTime) owners env result valid supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerPhase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerPhase.append_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerPhase.append_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerPhase.create_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerPhase.create_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerPhase.bundle_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerPhase.bundle_done
