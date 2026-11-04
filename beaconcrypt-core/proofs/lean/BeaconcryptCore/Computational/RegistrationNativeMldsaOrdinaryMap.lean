-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaMap
import BeaconcryptCore.Computational.RegistrationNativeMldsaCreation

/-! Ordinary native owner programs are parametric in the private ML signing-key representation. The state map preserves all public fields and complete shared environment; generation and signing are excluded from these lemmas. No generation/sign equality for the dummy opaque source is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaMap (Map owners owner)
open RegistrationNativeBeaconFrontend (M)
variable {left right : Source} {n : Nat} {KemSK Auxiliary Value Next Other : Type}

abbrev Natural (mapping : Map left right) (value : Value → Other)
    (first : M n KemSK left Auxiliary Value) (second : M n KemSK right Auxiliary Other) : Prop :=
  ∀ before env, (fun result => ((value result.1.1, owners mapping result.1.2), result.2)) <$>
      ((first.run before).run env) = ((second.run (owners mapping before)).run env)

theorem pure_natural (mapping : Map left right) (value : Value → Other) (input : Value) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping value (pure input) (pure (value input)) := by
  intro before env
  simp only [StateT.run_pure, map_pure]

theorem bind_natural {OtherNext : Type} (mapping : Map left right) (value : Value → Other) (nextValue : Next → OtherNext)
    (first : M n KemSK left Auxiliary Value) (second : M n KemSK right Auxiliary Other)
    (nextFirst : Value → M n KemSK left Auxiliary Next) (nextSecond : Other → M n KemSK right Auxiliary OtherNext)
    (initial : Natural mapping value first second)
    (continued : ∀ input, Natural mapping nextValue (nextFirst input) (nextSecond (value input))) :
    Natural mapping nextValue (first >>= nextFirst) (second >>= nextSecond) := by
  intro before env
  simp only [StateT.run_bind, map_bind]
  rw [← initial before env, bind_map_left]
  apply bind_congr
  intro result
  exact continued result.1.1 result.1.2 result.2

theorem simulate_natural {Query : Type} {spec : OracleSpec Query} (mapping : Map left right)
    (first : QueryImpl spec (M n KemSK left Auxiliary)) (second : QueryImpl spec (M n KemSK right Auxiliary))
    (queries : ∀ query, Natural mapping id (first query) (second query)) (work : OracleComp spec Value) :
    Natural mapping id (simulateQ first work) (simulateQ second work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, id_eq] using pure_natural mapping id value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact bind_natural mapping id id _ _ _ _ (queries query) ih

theorem effect_natural (mapping : Map left right) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Natural (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.effect query) (RegistrationNativeBeaconFrontend.effect query) := by
  intro before env
  simp only [RegistrationNativeBeaconFrontend.effect, StateT.run_lift, bind_pure_comp]
  rfl

theorem kem_natural (mapping : Map left right)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Natural (n := n) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.kem query) (RegistrationNativeBeaconFrontend.kem query) := by
  intro before env
  simp only [RegistrationNativeBeaconFrontend.kem, StateT.run_lift, bind_pure_comp]
  rfl

theorem sample_natural (mapping : Map left right) (work : ProbComp Value) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.sample work) (RegistrationNativeBeaconFrontend.sample work) := by
  apply simulate_natural
  intro query
  exact effect_natural mapping (.inl query)

theorem hash_natural (mapping : Map left right) (request : registration.HashRequest) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.hash request) (RegistrationNativeBeaconFrontend.hash request) :=
  effect_natural mapping _

theorem get_natural (mapping : Map left right) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping (owners mapping)
      (get : M n KemSK left Auxiliary (RegistrationNativeBeaconFrontend.State left)) get := by
  intro before env
  simp only [StateT.run_get, StateT.run_pure, map_pure]

theorem set_natural (mapping : Map left right) (updated : RegistrationNativeBeaconFrontend.State left) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (set updated) (set (owners mapping updated)) := by
  intro before env
  simp only [StateT.run_set, StateT.run_pure, map_pure]

theorem updateEnv_natural (mapping : Map left right)
    (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Natural (n := n) (KemSK := KemSK) mapping id
      (RegistrationNativeBeaconFrontend.updateEnv change) (RegistrationNativeBeaconFrontend.updateEnv change) := by
  intro before env
  simp only [RegistrationNativeBeaconFrontend.updateEnv, StateT.run_lift, StateT.run_map, StateT.run_modify, bind_pure_comp, map_pure]

theorem put_natural (mapping : Map left right) (index : Nat) (updated : RegistrationNativeBeaconFrontend.Owner left) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.put index updated) (RegistrationNativeBeaconFrontend.put index (owner mapping updated)) := by
  intro before env
  simp only [RegistrationNativeBeaconFrontend.put, StateT.run_modify, StateT.run_pure, map_pure,
    RegistrationNativeMldsaMap.owners_set]

theorem phase_natural (mapping : Map left right) (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.updatePhase index phase) (RegistrationNativeBeaconFrontend.updatePhase index phase) := by
  intro before env
  simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, StateT.run_pure, map_pure,
    RegistrationNativeMldsaMap.owners_lookup]
  cases before[index]? with
  | none => rfl
  | some current => simp only [Option.map_some, RegistrationNativeMldsaMap.owners_set, RegistrationNativeMldsaMap.owner_phase]

theorem history_natural (mapping : Map left right) (index : Nat) (message : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.logEd index message signature) (RegistrationNativeBeaconFrontend.logEd index message signature) := by
  intro before env
  simp only [RegistrationNativeBeaconFrontend.logEd, StateT.run_modify, StateT.run_pure, map_pure,
    RegistrationNativeMldsaMap.owners_lookup]
  cases before[index]? with
  | none => rfl
  | some current =>
      simp only [Option.map_some, RegistrationNativeMldsaMap.owners_set, RegistrationNativeMldsaMap.owner_history]
      rfl

variable {ι : Type} {base : OracleSpec ι}

set_option backward.isDefEq.respectTransparency false in
theorem authentication_natural (mapping : Map left right) (sameVerify : left.verify = right.verify)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    Natural (n := n) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.authentication setup left query) (RegistrationNativeBeaconFrontend.authentication setup right query) := by
  cases query with
  | hash request =>
      apply bind_natural mapping id id _ _ _ _ (hash_natural mapping request)
      intro digest
      exact pure_natural mapping id _
  | mldsa request =>
      simp only [RegistrationNativeBeaconFrontend.authentication, sameVerify]
      exact pure_natural mapping id _
  | ed25519 request => exact pure_natural mapping id _

set_option backward.isDefEq.respectTransparency false in
theorem primitive_natural (mapping : Map left right) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (current : RegistrationNativeBeaconFrontend.Owner left) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Natural (n := n) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.primitive setup current oneTime query)
      (RegistrationNativeBeaconFrontend.primitive setup (owner mapping current) oneTime query) := by
  apply simulate_natural
  intro lower
  cases lower with
  | inl other => exact sample_natural mapping _
  | inr other => exact kem_natural mapping _

set_option backward.isDefEq.respectTransparency false in
theorem agreementCore_natural (mapping : Map left right) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (current : RegistrationNativeBeaconFrontend.Owner left) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    Natural (n := n) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.agreementCore setup current oneTime query)
      (RegistrationNativeBeaconFrontend.agreementCore setup (owner mapping current) oneTime query) := by
  cases query with
  | root request => exact pure_natural mapping id _
  | convertPublic key => exact primitive_natural mapping setup current oneTime (.convertPublic key)
  | convertSecret role => exact primitive_natural mapping setup current oneTime (.convertSecret role)
  | generate role => exact primitive_natural mapping setup current oneTime (.generate role)
  | encapsulate key => exact primitive_natural mapping setup current oneTime (.encapsulate key)
  | decapsulate ciphertext => exact primitive_natural mapping setup current oneTime (.decapsulate ciphertext)
  | dh request => exact primitive_natural mapping setup current oneTime (.dh request)

set_option backward.isDefEq.respectTransparency false in
theorem agreement_natural (mapping : Map left right) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (current : RegistrationNativeBeaconFrontend.Owner left) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    Natural (n := n) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.agreement setup current oneTime query)
      (RegistrationNativeBeaconFrontend.agreement setup (owner mapping current) oneTime query) := by
  apply bind_natural mapping id id _ _ _ _ (updateEnv_natural mapping _)
  intro _changed
  exact agreementCore_natural mapping setup current oneTime query

theorem abort_natural (mapping : Map left right) (current : RegistrationNativeBeaconFrontend.Owner left) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.abort current) (RegistrationNativeBeaconFrontend.abort (owner mapping current)) := by
  apply bind_natural mapping id id _ _ _ _ (effect_natural mapping _)
  intro result
  exact pure_natural mapping id _

set_option backward.isDefEq.respectTransparency false in
theorem appendBorn_natural (mapping : Map left right) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (edPin : Std.Array Std.U8 32#usize) (keyId : Std.U64) (pin : session.ServerAuthenticationPin)
    (credential : RegistrationNativeMldsa.Credential left) (identity : PqxdhJointIdentity.IdentitySeed)
    (prekey : PqxdhJointGapDh.ScalarBytes) :
    Natural (n := n) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.appendBorn setup left edPin keyId pin credential identity prekey)
      (RegistrationNativeBeaconFrontend.appendBorn setup right edPin keyId pin (RegistrationNativeMldsaMap.credential mapping credential) identity prekey) := by
  intro before env
  simp only [RegistrationNativeBeaconFrontend.appendBorn, RegistrationNativeBeaconFrontend.kem,
    RegistrationNativeBeaconFrontend.effect, StateT.run_bind, StateT.run_lift, StateT.run_get,
    StateT.run_pure, bind_pure_comp, map_bind, bind_map_left]
  apply bind_congr
  intro born
  apply bind_congr
  intro worldOwner
  simp only [pure_bind, StateT.run_map, StateT.run_set, StateT.run_pure, map_pure]
  simp only [RegistrationNativeMldsaMap.owners, List.map_append, List.map_cons, List.map_nil, List.length_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.pure_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.pure_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.bind_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.bind_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.simulate_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.simulate_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.effect_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.effect_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.kem_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.kem_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.sample_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.sample_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.hash_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.hash_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.get_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.get_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.set_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.set_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.updateEnv_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.updateEnv_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.put_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.put_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.phase_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.phase_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.history_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.history_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.authentication_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.authentication_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.primitive_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.primitive_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.agreementCore_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.agreementCore_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.agreement_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.agreement_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.abort_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.abort_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.appendBorn_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap.appendBorn_natural
