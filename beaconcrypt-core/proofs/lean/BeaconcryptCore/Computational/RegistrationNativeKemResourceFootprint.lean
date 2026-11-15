-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame
import BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps

/-! Birth, encapsulation and decapsulation bills follow the actual private native controller leaves, including every failed prefix. Opposite-role KEM operations have zero cost. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint
open RegistrationNativeBeaconFrontend (M Trusted Owner)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value Result : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

inductive Kind where
  | birth
  | encapsulate
  | decapsulate
  deriving DecidableEq

def counted (kind : Kind) : (Trusted n KemSK).Domain → Prop
  | .inr (.inr (.inl .create)) => kind = .birth
  | .inr (.inr (.inl (.decapsulate _ _))) => kind = .decapsulate
  | .inr (.inr (.inr _)) => kind = .encapsulate
  | _ => False

instance (kind : Kind) : DecidablePred (counted (n := n) (KemSK := KemSK) kind) := fun query => by
  unfold counted
  split <;> infer_instance

def Bounded (kind : Kind) (cap : Nat) (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners environment, ((work.run owners).run environment).IsQueryBoundP (counted (n := n) (KemSK := KemSK) kind) cap

private theorem pure_bound (kind : Kind) (cap : Nat) (value : Value) :
    Bounded (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind cap (pure value) := by
  intro owners environment
  simp only [StateT.run_pure, isQueryBoundP_pure]

private theorem bind_bound (kind : Kind) (left right : Nat) (first : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Result)
    (initial : Bounded kind left first) (later : ∀ value, Bounded kind right (next value)) :
    Bounded kind (left + right) (first >>= next) := by
  intro owners environment
  change (((first.run owners).run environment) >>= fun middle =>
    (((next middle.1.1).run middle.1.2).run middle.2)).IsQueryBoundP (counted (n := n) (KemSK := KemSK) kind) (left + right)
  exact isQueryBoundP_bind (initial owners environment) (fun middle _supported => later middle.1.1 middle.1.2 middle.2)

private theorem bind_zero (kind : Kind) (first : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Result)
    (initial : Bounded kind 0 first) (later : ∀ value, Bounded kind 0 (next value)) :
    Bounded kind 0 (first >>= next) := bind_bound kind 0 0 first next initial later

/-- An arbitrary native continuation is quiet for the private KEM class when each actual callback is quiet. -/
theorem simulate_zero {Index : Type} (spec : OracleSpec Index) (kind : Kind)
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (quiet : ∀ query, Bounded kind 0 (implementation query)) (work : OracleComp spec Value) :
    Bounded kind 0 (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_bound kind 0 value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_zero kind _ _ (quiet query) ih

/-- Actual World effects cannot create an indexed KEM pair or reveal its secret. -/
theorem effect_zero (kind : Kind) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Bounded (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.effect query) := by
  intro owners environment
  simp [RegistrationNativeBeaconFrontend.effect, StateT.run_lift, StateT.run_map,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff, counted]

/-- Native randomness remains the original World effect and incurs no private KEM access. -/
theorem sample_zero (kind : Kind) (work : ProbComp Value) :
    Bounded (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.sample work) :=
  simulate_zero unifSpec kind _ (fun query => effect_zero kind (.inl query)) work

private theorem env_zero (kind : Kind) (change : EnvState Auxiliary → EnvState Auxiliary) :
    Bounded (n := n) (KemSK := KemSK) (source := source) kind 0
      (RegistrationNativeBeaconFrontend.updateEnv change) := by
  intro owners environment
  simp [RegistrationNativeBeaconFrontend.updateEnv, StateT.run_lift, StateT.run_map]

private theorem modify_zero (kind : Kind)
    (change : RegistrationNativeBeaconFrontend.State source → RegistrationNativeBeaconFrontend.State source) :
    Bounded (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) kind 0 (modify change) := by
  intro owners environment
  simp [StateT.run_modify, StateT.run_pure]

private theorem get_zero (kind : Kind) :
    Bounded (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind 0 get := by
  intro owners environment
  simp [StateT.run_get, StateT.run_pure]

private theorem hash_zero (kind : Kind) (request : registration.HashRequest) :
    Bounded (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.hash request) := effect_zero kind _

/-- All actual constructor preflights (the fixed-size Server pin) and classical identity and prekey draws occur before indexed KEM birth and have zero private KEM cost. -/
theorem prepare_zero (kind : Kind) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.prepare source edPin mlPin keyId) := by
  unfold RegistrationNativeBeaconFrontend.prepare
  repeat first
    | exact pure_bound kind 0 _
    | split
    | (apply bind_zero kind _ _ (sample_zero kind _); intro sampled)

/-- The real constructor suffix has exactly one possible private birth and no secret-reveal operation. -/
theorem append_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (edPin : Std.Array U8 32#usize) (keyId : U64) (pin : session.ServerAuthenticationPin)
    (identity : PqxdhJointIdentity.IdentitySeed) (prekey : PqxdhJointGapDh.ScalarBytes) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind (if kind = .birth then 1 else 0)
      (RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId pin identity prekey) := by
  intro owners environment
  cases kind <;>
    simp [RegistrationNativeBeaconFrontend.appendBorn, RegistrationNativeBeaconFrontend.kem,
      RegistrationNativeBeaconFrontend.effect, StateT.run_bind, StateT.run_lift, StateT.run_map,
      StateT.run_get, StateT.run_set, isQueryBoundP_query_bind_iff, counted]

/-- Every actual create call has at most one indexed private birth, including all constructor failures. -/
theorem create_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind (if kind = .birth then 1 else 0)
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId) := by
  unfold RegistrationNativeBeaconFrontend.create
  rw [← Nat.zero_add (if kind = .birth then 1 else 0)]
  apply bind_bound kind 0 _ _ _ (prepare_zero kind edPin mlPin keyId)
  intro prepared
  cases prepared with
  | fail error | div => exact pure_bound kind _ _
  | ok prepared => cases prepared with
    | none => exact pure_bound kind _ _
    | some prepared => exact append_bound setup kind edPin keyId prepared.pin prepared.identity prepared.prekey

private theorem map_zero (kind : Kind) (project : Value → Result) (work : M n KemSK source Auxiliary Value)
    (bounded : Bounded kind 0 work) : Bounded kind 0 (project <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact bind_zero kind work _ bounded (fun _ => pure_bound kind 0 _)

/-- Actual native Init hashing and Ed25519 signing perform no private KEM access; the shared ML-DSA sign request is unreachable for the Beacon and returns `None`. -/
theorem outgoing_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (index : Nat) (owner : Owner source) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query) := by
  classical
  cases query with
  | inl query => cases query with
    | hash request => exact hash_zero kind request
    | sign request payload digest =>
        unfold RegistrationNativeBeaconFrontend.outgoing
        exact pure_bound kind 0 _
  | inr request =>
      simp only [RegistrationNativeBeaconFrontend.outgoing]
      split
      · exact bind_zero kind _ _ (modify_zero kind _) (fun _ => pure_bound kind 0 _)
      · exact pure_bound kind 0 _

attribute [local irreducible] RegistrationBeaconInitExecutor.begin RegistrationResponseExecutor.begin
  RegistrationAgreementExecutor.beacon RegistrationBeaconRecordExecutor.begin

private noncomputable def bundled (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let published ← simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
      (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
      RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime)
      let _ ← RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))
      pure (.ok (some finished.encoded))

private theorem bundled_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind 0 (bundled setup wire index owner oneTime) := by
  unfold bundled
  apply bind_zero kind _ _ (simulate_zero RegistrationBeaconInitExecutor.Spec kind _
    (fun query => outgoing_zero setup kind index owner query) _)
  intro published
  cases published with
  | fail error | div => exact pure_bound kind 0 _
  | ok result => cases result with
    | Err previous => exact pure_bound kind 0 _
    | Ok finished => exact bind_zero kind _ _ (modify_zero kind _) (fun _ =>
        bind_zero kind _ _ (effect_zero kind _) (fun _ => pure_bound kind 0 _))

/-- The actual bundle controller retains every success and failed publication while creating no private KEM pair or reveal. -/
theorem bundle_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (wire : RegistrationNativeWire.Wire) (index : Nat) :
    Bounded (n := n) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.bundle setup source wire index) := by
  unfold RegistrationNativeBeaconFrontend.bundle
  apply bind_zero kind _ _ (get_zero kind)
  intro owners
  cases owners[index]? with
  | none => exact pure_bound kind 0 _
  | some owner =>
      dsimp only
      cases owner.phase <;> dsimp only
      all_goals first
        | exact pure_bound kind 0 _
        | exact bind_zero kind _ _ (sample_zero kind _) (fun oneTime => bundled_zero setup kind wire index owner oneTime)
        | exact bundled_zero setup kind wire index owner _

private theorem authentication_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    Bounded (n := n) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.authentication setup source query) := by
  cases query with
  | hash request =>
      unfold RegistrationNativeBeaconFrontend.authentication
      exact bind_zero kind _ _ (hash_zero kind _) (fun _ => pure_bound kind 0 _)
  | mldsa request | ed25519 request => exact pure_bound kind 0 _

private theorem decapsulate_zero (kind : Kind) (quiet : kind ≠ .decapsulate) (handle : Nat) (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) :
    Bounded (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.kem (.inr (.inl (.decapsulate handle ciphertext)))) := by
  intro owners environment
  simp [RegistrationNativeBeaconFrontend.kem, StateT.run_lift, StateT.run_map,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff, counted, quiet]

private theorem primitive_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind) (quiet : kind ≠ .decapsulate)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.primitive setup owner oneTime query) := by
  cases query with
  | convertPublic key | convertSecret key | generate key | dh key =>
      simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
        RegistrationNativeKemInterface.other, simulateQ_spec_query]
      exact sample_zero kind _
  | encapsulate key =>
      simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure]
      exact pure_bound kind 0 _
  | decapsulate ciphertext =>
      cases ciphertext with
      | none =>
          simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure]
          exact pure_bound kind 0 _
      | some ciphertext =>
          simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
            simulateQ_map, simulateQ_spec_query]
          exact map_zero kind _ _ (decapsulate_zero kind quiet owner.kemHandle _)

private theorem agreement_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind) (quiet : kind ≠ .decapsulate)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query) := by
  unfold RegistrationNativeBeaconFrontend.agreement
  apply bind_zero kind _ _ (env_zero kind _)
  intro recorded
  cases query <;> first
    | exact primitive_zero setup kind quiet owner oneTime _
    | exact pure_bound kind 0 _

private theorem record_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Bounded (n := n) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.record setup wire query) := by
  unfold RegistrationNativeBeaconFrontend.record
  apply bind_zero kind _ _ (env_zero kind _)
  intro recorded
  cases query <;> first
    | exact bind_zero kind _ _ (hash_zero kind _) (fun _ => pure_bound kind 0 _)
    | exact sample_zero kind _

private theorem abort_zero (kind : Kind) (owner : Owner source) :
    Bounded (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.abort owner) :=
  bind_zero kind _ _ (effect_zero kind _) (fun _ => pure_bound kind 0 _)

/-- The corrected actual installation has zero KEM work on both installation outcomes. -/
theorem install_zero (kind : Kind) (index : Nat) (owner : Owner source) (completed : beaconcrypt_core.registration.CompletedBeacon) :
    Bounded (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativePlatformBeaconFinish.install index owner completed) := by
  rw [RegistrationNativePlatformBeaconFinish.install_exact]
  apply bind_zero kind _ _ (effect_zero kind _)
  intro installed
  split
  · exact bind_zero kind _ _ (modify_zero kind _) (fun _ => pure_bound kind 0 _)
  · exact bind_zero kind _ _ (abort_zero kind owner) (fun _ => pure_bound kind 0 _)

/-- Actual corrected finish has no private birth or encapsulation, including all failed prefixes. -/
theorem finish_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (quiet : kind ≠ .decapsulate)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option beaconcrypt_core.registration.ResponsePacket) :
    Bounded (n := n) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet) := by
  unfold RegistrationNativePlatformBeaconFinish.finish RegistrationNativePlatformBeaconFinish.finishWith
  apply bind_zero kind _ _ (get_zero kind)
  intro owners
  repeat first
    | exact pure_bound kind 0 _
    | (apply bind_zero kind _ _ (modify_zero kind _); intro changed)
    | (apply bind_zero kind _ _ (abort_zero kind _); intro aborted)
    | exact install_zero kind _ _ _
    | (unfold RegistrationNativePlatformBeaconFinish.afterAuthenticationWith)
    | (apply bind_zero kind _ _ (simulate_zero RegistrationAuthenticationExecutor.Spec kind _ (fun query => authentication_zero setup kind query) _); intro authenticated)
    | (apply bind_zero kind _ _ (simulate_zero RegistrationAgreementExecutor.Spec kind _ (fun query => agreement_zero setup kind quiet _ _ query) _); intro agreed)
    | (apply bind_zero kind _ _ (simulate_zero RegistrationRecordPrimitives.Spec kind _ (fun query => record_zero setup kind wire query) _); intro opened)
    | split

end BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.simulate_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.simulate_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.effect_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.effect_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.sample_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.sample_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.prepare_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.prepare_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.append_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.append_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.outgoing_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.outgoing_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.bundle_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.bundle_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.install_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.install_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.finish_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint.finish_zero
