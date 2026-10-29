-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler
import BeaconcryptCore.Computational.RegistrationNativeKemBudget

/-! Private indexed KEM creation and secret-reveal bills are derived from the actual Beacon controller AST. Ordinary World randomness, hashing, signatures and local control updates carry neither operation. The source state and every optional failure continuation remain explicit in the bounds. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint
open RegistrationNativeBeaconFrontend (M Trusted Owner)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value Result : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- The third marker audits that role callbacks are lowered locally before reaching the external native interface. -/
inductive Kind where
  | create
  | reveal
  | other
  deriving DecidableEq

def counted (kind : Kind) : (Trusted n KemSK).Domain → Prop
  | .inr (.inl _) => kind = .other
  | .inr (.inr (.inl .create)) => kind = .create
  | .inr (.inr (.inl (.reveal _))) => kind = .reveal
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

/-- All actual constructor preflights, ML generation, fingerprint and classical draws occur before indexed KEM birth and have zero private KEM cost. -/
theorem prepare_zero (kind : Kind) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.prepare source edPin mlPin keyId) := by
  unfold RegistrationNativeBeaconFrontend.prepare
  apply bind_zero kind _ _ (sample_zero kind _)
  intro generated
  cases generated with
  | none => exact pure_bound kind 0 _
  | some credentials =>
      repeat first
        | exact pure_bound kind 0 _
        | split
        | (apply bind_zero kind _ _ (hash_zero kind _); intro digest)
        | (apply bind_zero kind _ _ (sample_zero kind _); intro sampled)

/-- The real constructor suffix has exactly one possible private birth and no secret-reveal operation. -/
theorem append_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (edPin : Std.Array U8 32#usize) (keyId : U64) (pin : session.ServerAuthenticationPin)
    (credential : RegistrationNativeMldsa.Credential source)
    (identity : PqxdhJointIdentity.IdentitySeed) (prekey : PqxdhJointGapDh.ScalarBytes) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind (if kind = .create then 1 else 0)
      (RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId pin credential identity prekey) := by
  intro owners environment
  cases kind <;>
    simp [RegistrationNativeBeaconFrontend.appendBorn, RegistrationNativeBeaconFrontend.kem,
      RegistrationNativeBeaconFrontend.effect, StateT.run_bind, StateT.run_lift, StateT.run_map,
      StateT.run_get, StateT.run_set, isQueryBoundP_query_bind_iff, counted]

/-- Every actual create call has at most one indexed private birth, including all constructor failures. -/
theorem create_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind (if kind = .create then 1 else 0)
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId) := by
  unfold RegistrationNativeBeaconFrontend.create
  rw [← Nat.zero_add (if kind = .create then 1 else 0)]
  apply bind_bound kind 0 _ _ _ (prepare_zero kind edPin mlPin keyId)
  intro prepared
  cases prepared with
  | fail error | div => exact pure_bound kind _ _
  | ok prepared => cases prepared with
    | none => exact pure_bound kind _ _
    | some prepared => exact append_bound setup kind edPin keyId prepared.pin prepared.credentials prepared.identity prepared.prekey

private theorem map_zero (kind : Kind) (project : Value → Result) (work : M n KemSK source Auxiliary Value)
    (bounded : Bounded kind 0 work) : Bounded kind 0 (project <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact bind_zero kind work _ bounded (fun _ => pure_bound kind 0 _)

/-- Actual native Init signing, fingerprinting and stateful signing receipts perform no private KEM access. -/
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
        apply bind_zero kind _ _ (sample_zero kind _)
        intro reply
        exact bind_zero kind _ _ (env_zero kind _) (fun _ => pure_bound kind 0 _)
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
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
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

private theorem decapsulate_zero (kind : Kind) (handle : Nat) (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) :
    Bounded (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.kem (.inr (.inl (.decapsulate handle ciphertext)))) := by
  intro owners environment
  simp [RegistrationNativeBeaconFrontend.kem, StateT.run_lift, StateT.run_map,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff, counted]

private theorem primitive_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
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
          exact map_zero kind _ _ (decapsulate_zero kind owner.kemHandle _)

private theorem agreement_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) :
    Bounded (n := n) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query) := by
  unfold RegistrationNativeBeaconFrontend.agreement
  apply bind_zero kind _ _ (env_zero kind _)
  intro recorded
  cases query <;> first
    | exact primitive_zero setup kind owner oneTime _
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

/-- The full actual finish controller performs only indexed decapsulation, never creation or secret reveal, on all authentication, agreement, open and install failures. -/
theorem finish_zero (setup : PqxdhServerAuthExperiment.Setup base KemSK) (kind : Kind)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    Bounded (n := n) (source := source) (Auxiliary := Auxiliary) kind 0
      (RegistrationNativeBeaconFrontend.finish setup source wire index packet) := by
  unfold RegistrationNativeBeaconFrontend.finish
  apply bind_zero kind _ _ (get_zero kind)
  intro owners
  repeat first
    | exact pure_bound kind 0 _
    | (apply bind_zero kind _ _ (modify_zero kind _); intro changed)
    | (apply bind_zero kind _ _ (effect_zero kind _); intro effected)
    | (apply bind_zero kind _ _ (abort_zero kind _); intro aborted)
    | (apply bind_zero kind _ _ (simulate_zero RegistrationAuthenticationExecutor.Spec kind _ (fun query => authentication_zero setup kind query) _); intro authenticated)
    | (apply bind_zero kind _ _ (simulate_zero RegistrationAgreementExecutor.Spec kind _ (fun query => agreement_zero setup kind _ _ query) _); intro agreed)
    | (apply bind_zero kind _ _ (simulate_zero RegistrationRecordPrimitives.Spec kind _ (fun query => record_zero setup kind wire query) _); intro opened)
    | (split <;> try dsimp only)

end BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.simulate_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.simulate_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.effect_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.effect_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.sample_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.sample_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.prepare_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.prepare_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.append_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.append_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.create_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.outgoing_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.outgoing_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.bundle_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.bundle_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.finish_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint.finish_zero
