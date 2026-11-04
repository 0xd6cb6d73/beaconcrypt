-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint
import BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth
import BeaconcryptCore.Computational.RegistrationNativeStatePreservation

/-! Every original native callback except bundle can only retain or remove an existing InitSent capability. Actual creation appends a fresh owner, and actual finish writes only terminal phases. The backward source frame follows every optional failure and retains the exact pending value and one-time scalar, without an assumed phase or journal invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePendingFrames
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (M Owner Phase)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeBeaconFootprint (ReadOnly)
variable {n : Nat} {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def PendingAt (owners : RegistrationNativeBeaconFrontend.State source) (index : Nat)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) : Prop :=
  ∃ owner, owners[index]? = some owner ∧ owner.phase = .initSent pending oneTime

def Backwards (before after : RegistrationNativeBeaconFrontend.State source) : Prop :=
  ∀ index pending oneTime, PendingAt after index pending oneTime → PendingAt before index pending oneTime

namespace Backwards

theorem refl (owners : RegistrationNativeBeaconFrontend.State source) : Backwards owners owners :=
  fun _ _ _ found => found

theorem trans (before middle after : RegistrationNativeBeaconFrontend.State source)
    (first : Backwards before middle) (later : Backwards middle after) : Backwards before after :=
  fun index pending oneTime found => first index pending oneTime (later index pending oneTime found)
end Backwards

private theorem appended (owners : RegistrationNativeBeaconFrontend.State source) (added : Owner source)
    (terminal : ∀ pending oneTime, added.phase ≠ .initSent pending oneTime) : Backwards owners (owners ++ [added]) := by
  intro index pending oneTime entered
  obtain ⟨owner, found, phase⟩ := entered
  by_cases earlier : index < owners.length
  · rw [List.getElem?_append_left earlier] at found
    exact ⟨owner, found, phase⟩
  · simp only [List.getElem?_append, earlier, ite_false] at found
    cases difference : index - owners.length with
    | zero =>
      simp only [difference, List.getElem?_cons_zero, Option.some.injEq] at found
      subst owner
      exact (terminal pending oneTime phase).elim
    | succ rest => simp [difference] at found

private def Keeps (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → Backwards owners result.1.2

private theorem pure_keeps (value : Value) : Keeps (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact Backwards.refl owners

private theorem bind_keeps (work : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Next) (first : Keeps work) (later : ∀ value, Keeps (next value)) :
    Keeps (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact Backwards.trans owners middle.1.2 result.1.2
    (first owners env middle reached) (later middle.1.1 middle.1.2 middle.2 result continued)

private theorem readonly_keeps (work : M n KemSK source Auxiliary Value) (readonly : ReadOnly work) : Keeps work := by
  intro owners env result supported
  rw [readonly owners env result supported]
  exact Backwards.refl owners

private theorem lift_keeps (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value) :
    Keeps (StateT.lift work : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _reached, returned⟩ := supported
  cases returned
  exact Backwards.refl owners

private theorem get_keeps : Keeps (get : M n KemSK source Auxiliary (RegistrationNativeBeaconFrontend.State source)) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact Backwards.refl owners

private theorem current_keeps (index : Nat) (change : Owner source → Owner source)
    (backward : ∀ owner pending oneTime, (change owner).phase = .initSent pending oneTime →
      owner.phase = .initSent pending oneTime) :
    Keeps ((modify fun owners => match owners[index]? with
      | none => owners
      | some owner => owners.set index (change owner)) : M n KemSK source Auxiliary Unit) := by
  intro owners env result supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  intro target pending oneTime entered
  obtain ⟨selected, found, phase⟩ := entered
  cases original : owners[index]? with
  | none => exact ⟨selected, by simpa only [original] using found, phase⟩
  | some owner =>
    simp only [original] at found
    by_cases same : index = target
    · subst target
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp original).1] at found
      cases found
      exact ⟨owner, original, backward owner pending oneTime phase⟩
    · rw [List.getElem?_set_ne same] at found
      exact ⟨selected, found, phase⟩

private theorem phase_keeps (index : Nat) (phase : Phase)
    (terminal : ∀ pending oneTime, phase ≠ .initSent pending oneTime) :
    Keeps (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := Auxiliary) index phase) :=
  current_keeps index (fun owner => { owner with phase })
    (fun _ pending oneTime same => (terminal pending oneTime same).elim)

/-- The complete actual constructor appends only a fresh owner and therefore introduces no InitSent capability. -/
theorem create (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Nat) × RegistrationNativeBeaconFrontend.State source) × EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run owners).run env)) :
    Backwards owners result.1.2 := by
  rw [RegistrationNativeBeaconBirth.create_program] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨earlier, reached, continued⟩ := supported
  have retained := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners env earlier reached
  cases actual : earlier.1.1 with
  | fail error | div =>
    simp only [actual, support_pure, Set.mem_singleton_iff] at continued
    cases continued
    rw [retained]
    exact Backwards.refl owners
  | ok result => cases result with
    | none =>
      simp only [actual, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      rw [retained]
      exact Backwards.refl owners
    | some prepared =>
      simp only [actual] at continued
      rw [RegistrationNativeBeaconBirth.append_program] at continued
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at continued
      obtain ⟨born, _born, worldOwner, _allocated, returned⟩ := continued
      cases returned
      rw [retained]
      exact appended owners _ (fun _ _ impossible => Phase.noConfusion impossible)

private theorem abort_return (owner : Owner source) (value : Value) :
    Keeps (RegistrationNativeBeaconFrontend.abort owner *> pure value : M n KemSK source Auxiliary Value) := by
  rw [seqRight_eq_bind]
  exact bind_keeps _ _ (readonly_keeps _ (RegistrationNativeBeaconFootprint.abort_readonly owner))
    (fun _ => pure_keeps value)

/-- Every actual finish path consumes or preserves pending state and writes only terminal phases; none can synthesize a new InitSent capability. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeBeaconFrontend.State source) × EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationNativeBeaconFrontend.finish (n := n) setup source wire index packet).run owners).run env)) :
    Backwards owners result.1.2 := by
  have law : Keeps (RegistrationNativeBeaconFrontend.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
    unfold RegistrationNativeBeaconFrontend.finish
    apply bind_keeps _ _ get_keeps
    intro selectedOwners
    cases selectedOwners[index]? with
    | none => exact pure_keeps _
    | some owner =>
      simp only
      cases owner.phase with
      | fresh | freshWithCoins _ | established _ | aborted _ => exact pure_keeps _
      | initSent pending oneTime =>
        simp only
        cases pending.aborted_state with
        | fail error | div => exact pure_keeps _
        | ok aborted =>
          apply bind_keeps _ _ (phase_keeps index (.aborted aborted) (fun _ _ impossible => Phase.noConfusion impossible))
          intro _
          apply bind_keeps _ _ (readonly_keeps _ (RegistrationNativeBeaconFootprint.program_readonly _
            (RegistrationNativeBeaconFootprint.authentication_readonly setup) _))
          intro authenticated
          cases authenticated with
          | fail error | div => exact abort_return owner _
          | ok verdict => cases verdict with
            | Err rejected => exact abort_return owner _
            | Ok accepted =>
              apply bind_keeps _ _ (readonly_keeps _ (RegistrationNativeBeaconFootprint.program_readonly _
                (RegistrationNativeBeaconFootprint.agreement_readonly setup owner oneTime) _))
              intro agreed
              cases agreed with
              | fail error | div => exact abort_return owner _
              | ok effect => cases effect with
                | BeaconComplete completed =>
                  apply bind_keeps _ _ (readonly_keeps _ (RegistrationNativeBeaconFootprint.program_readonly _
                    (RegistrationNativeBeaconFootprint.record_readonly setup wire) _))
                  intro opened
                  cases opened with
                  | fail error | div => exact abort_return owner _
                  | ok result => cases result with
                    | Err rejected => exact abort_return owner _
                    | Ok established =>
                      apply bind_keeps _ _ (lift_keeps _)
                      intro installed
                      cases installed with
                      | false => exact abort_return owner _
                      | true =>
                        exact bind_keeps _ _
                          (phase_keeps index (.established ⟨established.control, established.binding, established.application⟩)
                            (fun _ _ impossible => Phase.noConfusion impossible))
                          (fun _ => pure_keeps _)
                | _ => exact abort_return owner _
  exact law owners env result supported

private theorem beacon (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (law : ∀ owners env result, result ∈ support ((work.run owners).run env) → Backwards owners result.1.2)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    Backwards before.beacons result.2.beacons := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  apply law before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) inner.1
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

def NonBundle : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.bundle _) => False
  | _ => True

/-- Every original typed callback except bundle preserves the exact backward pending frame, with no initial phase or journal condition. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonBundle query)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    Backwards before.beacons result.2.beacons := by
  have ordinary (good : RegistrationNativeStatePreservation.Ordinary query) : Backwards before.beacons result.2.beacons := by
    rw [(RegistrationNativeStatePreservation.handler_keeps setup checks wire route representation created credential query good before result supported).2]
    exact Backwards.refl before.beacons
  cases query with
  | inl coin => exact ordinary trivial
  | inr query => cases query with
    | create edPin mlPin keyId =>
      exact beacon setup checks representation created _ (create setup edPin mlPin keyId) before result supported
    | bundle index => exact False.elim allowed
    | finish index packet =>
      exact beacon setup checks representation created _ (finish setup wire index packet) before result supported
    | _ => exact ordinary trivial

end BeaconcryptCore.Computational.RegistrationNativePendingFrames

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePendingFrames.Backwards.refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePendingFrames.Backwards.refl

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePendingFrames.Backwards.trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePendingFrames.Backwards.trans

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePendingFrames.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePendingFrames.create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePendingFrames.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePendingFrames.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePendingFrames.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePendingFrames.handler
