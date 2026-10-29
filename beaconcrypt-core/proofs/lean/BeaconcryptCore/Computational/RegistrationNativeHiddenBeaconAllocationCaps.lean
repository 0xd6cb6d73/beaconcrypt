-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth

/-! The actual native Beacon pre-birth and outgoing-publication controllers allocate no physical owner slot. All replies, failed hashes, signing attempts and publication failures are retained. Allocation occurs only in the separate appendBorn suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconAllocationCaps
open RegistrationNativeBeaconFrontend
open RegistrationNativeHiddenAllocationCore (mapped simulation)
open RegistrationNativeHiddenAllocationProtocol (effectDelta)
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def Allowed : (Trusted n KemSK).Domain → Prop
  | .inl effect => effectDelta effect = 0
  | .inr _ => True

def Safe (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env, AllQueriesSatisfy ((work.run owners).run env) (Allowed (KemSK := KemSK))

private theorem pure_safe (value : Value) : Safe (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env
  simp only [StateT.run_pure]
  trivial

private theorem bind_safe (work : M n KemSK source Auxiliary Value) (next : Value → M n KemSK source Auxiliary Next)
    (first : Safe work) (later : ∀ value, Safe (next value)) : Safe (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun reply => later reply.1.1 reply.1.2 reply.2)

private theorem effect_safe (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (safe : effectDelta query = 0) :
    Safe (effect query : M n KemSK source Auxiliary _) := by
  intro owners env
  simp only [effect, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr safe)

private theorem sample_safe (work : ProbComp Value) : Safe (sample work : M n KemSK source Auxiliary Value) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe value
  | query_bind query next ih =>
      simp only [sample, simulateQ_bind, simulateQ_spec_query]
      exact bind_safe _ _ (effect_safe _ rfl) ih

private theorem modify_safe (change : State source → State source) :
    Safe (modify change : M n KemSK source Auxiliary Unit) := by
  intro owners env
  simp only [StateT.run_modify, StateT.run_pure]
  trivial

private theorem update_safe (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Safe (updateEnv change : M n KemSK source Auxiliary Unit) := by
  intro owners env
  simp only [updateEnv, StateT.run_lift]
  trivial

private theorem program_safe {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (step : ∀ query, Safe (implementation query)) (work : OracleComp spec Value) : Safe (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact bind_safe _ _ (step query) ih

/-- Actual preparation uses ordinary draws and the shared pin hash before any indexed birth or physical allocation. -/
theorem prepare_safe (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Safe (prepare (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source edPin mlPin keyId) := by
  unfold prepare
  apply bind_safe _ _ (sample_safe _)
  intro generated
  cases generated with
  | none => exact pure_safe _
  | some credentials =>
      dsimp only
      cases begun : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error | div => exact pure_safe _
      | ok pending =>
          simp only
          cases requested : pending.request with
          | fail error | div => exact pure_safe _
          | ok request =>
              simp only
              apply bind_safe _ _ (effect_safe _ rfl)
              intro digest
              cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
              | fail error | div => exact pure_safe _
              | ok result => cases result with
                | none => exact pure_safe _
                | some pin => exact bind_safe _ _ (sample_safe _) (fun _ => bind_safe _ _ (sample_safe _) (fun _ => pure_safe _))

private theorem outgoing_safe (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Safe (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact effect_safe _ rfl
    | sign request payload digest => exact bind_safe _ _ (sample_safe _) (fun _ => bind_safe _ _ (update_safe _) (fun _ => pure_safe _))
  | inr request =>
      simp only [outgoing]
      split
      · exact bind_safe _ _ (modify_safe _) (fun _ => pure_safe _)
      · exact pure_safe _

/-- Full native Ed3/fingerprint/ML publication and lifecycle update contain no physical owner allocation. -/
theorem bundle_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat) :
    Safe (bundle (n := n) (Auxiliary := Auxiliary) setup source wire index) := by
  intro owners env
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind]
  cases found : owners[index]? with
  | none => simp only [StateT.run_pure]; trivial
  | some owner =>
      simp only
      cases phase : owner.phase with
      | initSent pending oneTime | established completed | aborted control =>
          simp only [StateT.run_pure]
          trivial
      | fresh | freshWithCoins oneTime =>
          simp only []
          have later (oneTime : PqxdhJointGapDh.ScalarBytes) : Safe (do
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
                  pure (.ok (some finished.encoded)) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes))) := by
            apply bind_safe _ _ (program_safe _ (outgoing_safe setup index owner) _)
            intro published
            cases published with
            | fail error | div => exact pure_safe _
            | ok result => cases result with
              | Err error => exact pure_safe _
              | Ok finished => exact bind_safe _ _ (modify_safe _) (fun _ => bind_safe _ _ (effect_safe _ rfl) (fun _ => pure_safe _))
          all_goals first
            | exact bind_safe _ _ (sample_safe _) later owners env
            | exact later _ owners env

end BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconAllocationCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconAllocationCaps.prepare_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconAllocationCaps.prepare_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconAllocationCaps.bundle_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconAllocationCaps.bundle_safe
