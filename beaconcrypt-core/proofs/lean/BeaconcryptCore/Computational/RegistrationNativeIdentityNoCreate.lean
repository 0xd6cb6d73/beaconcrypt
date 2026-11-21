-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch
import BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch

/-! Actual bundle and finish callbacks use only existing generated identities. Their complete trusted ASTs contain no identity-creation query on any source reply or failure branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate
open RegistrationNativeIdentityFrontend
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary Value Other : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def Allowed (n : Nat) (KemSK : Type) : (Trusted n KemSK).Domain → Prop
  | .inr .create => False
  | _ => True

instance : DecidablePred (Allowed n KemSK) := fun query => by
  cases query with
  | inl query => exact inferInstanceAs (Decidable True)
  | inr query => cases query <;> simp only [Allowed] <;> infer_instance

def Safe (work : M n KemSK Auxiliary source Value) : Prop :=
  ∀ owners env, AllQueriesSatisfy ((work.run owners).run env) (Allowed n KemSK)

private theorem mapped {Index : Type} {spec : OracleSpec Index} {A B : Type}
    (work : OracleComp spec A) (change : A → B) (predicate : Index → Prop)
    (allowed : AllQueriesSatisfy work predicate) : AllQueriesSatisfy (change <$> work) predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

private theorem pure_safe (value : Value) : Safe (pure value : M n KemSK Auxiliary source Value) := by
  intro owners env
  simp only [StateT.run_pure]
  trivial

private theorem bind_safe (work : M n KemSK Auxiliary source Value) (next : Value → M n KemSK Auxiliary source Other)
    (first : Safe work) (later : ∀ value, Safe (next value)) : Safe (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun result => later result.1.1 result.1.2 result.2)

private theorem program_safe {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (M n KemSK Auxiliary source))
    (step : ∀ query, Safe (implementation query)) (work : OracleComp spec Value) :
    Safe (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_safe value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_safe _ _ (step query) ih

private theorem lift_safe (work : OracleComp (Trusted n KemSK) Value)
    (allowed : AllQueriesSatisfy work (Allowed n KemSK)) :
    Safe (StateT.lift (StateT.lift work) : M n KemSK Auxiliary source Value) := by
  intro owners env
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  exact mapped work _ (Allowed n KemSK) allowed

private theorem ambient_allowed (work : OracleComp (Ambient n KemSK) Value) :
    AllQueriesSatisfy (simulateQ ambientLift work) (Allowed n KemSK) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, ambientLift]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem old_safe (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) : Safe (liftOld work) := by
  intro owners env
  simp only [liftOld, StateT.run_lift, bind_pure_comp, StateT.run_map]
  exact mapped _ _ (Allowed n KemSK) (ambient_allowed _)

private theorem effect_safe (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Safe (effect query : M n KemSK Auxiliary source _) :=
  lift_safe _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)

private theorem kem_safe (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Safe (kem query : M n KemSK Auxiliary source _) :=
  lift_safe _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)

private theorem sample_safe (work : ProbComp Value) : Safe (sample work : M n KemSK Auxiliary source Value) :=
  program_safe (fun (query : unifSpec.Domain) => effect (.inl query)) (fun _ => effect_safe _) work

private theorem modify_safe (change : State source → State source) : Safe (modify change : M n KemSK Auxiliary source Unit) := by
  intro owners env
  simp only [StateT.run_modify, StateT.run_pure]
  trivial

private theorem update_safe (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Safe (updateEnv change : M n KemSK Auxiliary source Unit) := by
  intro owners env
  simp only [updateEnv, StateT.run_lift]
  trivial

private theorem get_safe : Safe (get : M n KemSK Auxiliary source (State source)) := by
  intro owners env
  simp only [StateT.run_get, StateT.run_pure]
  trivial

private theorem set_safe (owners : State source) : Safe (set owners : M n KemSK Auxiliary source Unit) := by
  intro current env
  simp only [StateT.run_set, StateT.run_pure]
  trivial

private theorem outgoing_safe (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) : Safe (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact effect_safe _
    | sign request payload digest => exact pure_safe _
  | inr request =>
      simp only [outgoing]
      split
      · have allowedSign : AllQueriesSatisfy
            (RegistrationNativeIdentityInterface.sign (Ambient n KemSK) owner.identity (TranscriptAuthParts.absSlice request.message))
            (Allowed n KemSK) := by
          exact (allQueriesSatisfy_query_iff (spec := Trusted n KemSK)
            (.inr (.service owner.identity.handle (.sign (TranscriptAuthParts.absSlice request.message))))
            (Allowed n KemSK)).mpr trivial
        apply bind_safe _ _ (lift_safe (source := source) _ allowedSign)
        intro signature
        cases signature with
        | none => exact pure_safe _
        | some signature => exact bind_safe _ _ (modify_safe _) (fun _ => pure_safe _)
      · exact pure_safe _

private theorem authentication_safe (setup : Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    Safe (authentication (n := n) (Auxiliary := Auxiliary) setup source query) := by
  cases query with
  | hash request => exact bind_safe _ _ (effect_safe _) (fun _ => pure_safe _)
  | mldsa request | ed25519 request => exact pure_safe _

private theorem dh_allowed (owner : Owner source) (peer : PqxdhBeaconPhase2Preparation.Word32) :
    AllQueriesSatisfy (RegistrationNativeIdentityCallbacks.dh (Ambient n KemSK) owner.identity peer) (Allowed n KemSK) := by
  simp only [RegistrationNativeIdentityCallbacks.dh, bind_pure_comp]
  apply mapped _ _ (Allowed n KemSK)
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem agreement_safe (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) : Safe (agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  by_cases ordinary : RegistrationNativeIdentityAgreementShape.Other query
  · rw [RegistrationNativeIdentityAgreementShape.exposed_other setup owner oneTime query ordinary]
    exact old_safe _
  · cases query with
    | convertSecret role =>
        have localRole : role = .LocalIdentity := by simpa only [RegistrationNativeIdentityAgreementShape.Other, not_not] using ordinary
        subst role
        exact bind_safe _ _ (update_safe _) (fun _ => pure_safe true)
    | dh request =>
        rcases request with ⟨role, peer⟩
        have localRole : role = .LocalIdentity := by simpa only [RegistrationNativeIdentityAgreementShape.Other, not_not] using ordinary
        subst role
        exact bind_safe _ _ (update_safe _) (fun _ => lift_safe _ (dh_allowed owner peer))
    | convertPublic key | generate role | encapsulate key | decapsulate ciphertext | root request => exact False.elim (ordinary trivial)

private theorem bundle_next_safe (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Safe (RegistrationNativeIdentityBundleSource.next (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact pure_safe _
  | ok result => cases result with
    | Err error => exact pure_safe _
    | Ok published => exact bind_safe _ _ (modify_safe _) (fun _ => bind_safe _ _ (effect_safe _) (fun _ => pure_safe _))

private theorem bundled_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Safe (RegistrationNativeIdentityBundleSource.bundled (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime) :=
  bind_safe _ _ (program_safe _ (outgoing_safe setup index owner) _) (bundle_next_safe index owner oneTime)

private theorem bundle_start_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) :
    Safe (RegistrationNativeIdentityBundleDispatch.start (n := n) (Auxiliary := Auxiliary) setup wire index owner) := by
  cases phase : owner.phase with
  | fresh =>
      simp only [RegistrationNativeIdentityBundleDispatch.start, phase]
      exact bind_safe _ _ (sample_safe _) (bundled_safe setup wire index owner)
  | freshWithCoins scalar =>
      simpa only [RegistrationNativeIdentityBundleDispatch.start, phase, pure_bind] using bundled_safe setup wire index owner scalar
  | initSent pending scalar | established completed | aborted aborted =>
      simpa only [RegistrationNativeIdentityBundleDispatch.start, phase] using
        (pure_safe (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (.ok none : RustM (Option Pqxdh.Bytes)))

/-- Full three-Ed/hash/publication and every retry or failure path create no indexed identity. -/
theorem bundle_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat) :
    Safe (bundle (n := n) (Auxiliary := Auxiliary) setup source wire index) := by
  intro owners env
  cases found : owners[index]? with
  | none => simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind, found, StateT.run_pure]; trivial
  | some owner =>
      rw [RegistrationNativeIdentityBundleDispatch.new_run setup wire index owner owners found env]
      exact bundle_start_safe setup wire index owner owners env

private theorem abort_safe (owner : Owner source) (value : Value) :
    Safe (abort owner *> pure value : M n KemSK Auxiliary source Value) := by
  simp only [abort, seqRight_eq_bind, bind_assoc, pure_bind]
  exact bind_safe _ _ (effect_safe _) (fun _ => pure_safe _)

private theorem record_after_safe (index : Nat) (owner : Owner source) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Safe (RegistrationNativeIdentityFinishRecord.after (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner reply) := by
  cases reply with
  | fail error | div => exact abort_safe owner _
  | ok result => cases result with
    | Err error => exact abort_safe owner _
    | Ok established =>
        apply bind_safe _ _ (effect_safe _)
        intro installed
        cases installed with
        | false => exact abort_safe owner _
        | true => exact bind_safe _ _ (modify_safe _) (fun _ => pure_safe _)

private theorem agreement_after_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (reply : RustM agreement.AgreementEffect) :
    Safe (RegistrationNativeIdentityFinishSteps.afterAgreement (n := n) (Auxiliary := Auxiliary) setup wire index owner reply) := by
  cases reply with
  | fail error | div => exact abort_safe owner _
  | ok effect => cases effect with
    | Rejected previous | ConvertPublic pending | ConvertSecret pending | GenerateEphemeral pending | Encapsulate pending
      | Decapsulate pending | Dh pending | RootKdf pending | ServerComplete completed => exact abort_safe owner _
    | BeaconComplete completed =>
        exact bind_safe _ _ (program_safe _ (fun _ => old_safe _) _) (record_after_safe index owner)

private theorem authentication_after_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Safe (RegistrationNativeIdentityFinishSteps.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact abort_safe owner _
  | ok result => cases result with
    | Err previous => exact abort_safe owner _
    | Ok accepted =>
        exact bind_safe _ _ (program_safe _ (agreement_safe setup owner oneTime) _)
          (agreement_after_safe setup wire index owner)

private theorem finish_begin_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) :
    Safe (RegistrationNativeIdentityFinishSteps.begin (n := n) (Auxiliary := Auxiliary) setup wire index owner pending oneTime packet) := by
  cases moved : pending.aborted_state with
  | fail error | div =>
      simpa only [RegistrationNativeIdentityFinishSteps.begin, moved] using
        (pure_safe (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) _)
  | ok aborted =>
      simp only [RegistrationNativeIdentityFinishSteps.begin, moved]
      exact bind_safe _ _ (modify_safe _) (fun _ => bind_safe _ _
        (program_safe _ (authentication_safe setup) _) (authentication_after_safe setup wire index owner oneTime))

private theorem finish_start_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (packet : Option registration.ResponsePacket) :
    Safe (RegistrationNativeIdentityFinishDispatch.start (n := n) (Auxiliary := Auxiliary) setup wire index owner packet) := by
  cases phase : owner.phase with
  | initSent pending oneTime =>
      simpa only [RegistrationNativeIdentityFinishDispatch.start, phase] using finish_begin_safe setup wire index owner pending oneTime packet
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simpa only [RegistrationNativeIdentityFinishDispatch.start, phase] using
        (pure_safe (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (.ok none : RustM (Option Pqxdh.Bytes)))

/-- Actual terminal finish, native verification, local static DH and sequence-one opening create no indexed identity. -/
theorem finish_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) :
    Safe (finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  intro owners env
  cases found : owners[index]? with
  | none => simp only [finish, StateT.run_bind, StateT.run_get, pure_bind, found, StateT.run_pure]; trivial
  | some owner =>
      rw [RegistrationNativeIdentityFinishDispatch.new_run setup wire index owner owners found env packet]
      exact finish_start_safe setup wire index owner packet owners env

/-- Exact zero creation bill for the actual complete bundle AST. -/
theorem bundle_zero (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owners : State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((bundle (n := n) setup source wire index).run owners).run env).IsQueryBoundP
      (fun query => ¬ Allowed n KemSK query) 0 := by
  classical
  exact (isQueryBoundP_zero_iff _ (Allowed n KemSK)).mpr (bundle_safe setup wire index owners env)

/-- Exact zero creation bill for the actual complete finish AST. -/
theorem finish_zero (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option beaconcrypt_core.registration.ResponsePacket)
    (owners : State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((finish (n := n) setup source wire index packet).run owners).run env).IsQueryBoundP
      (fun query => ¬ Allowed n KemSK query) 0 := by
  classical
  exact (isQueryBoundP_zero_iff _ (Allowed n KemSK)).mpr (finish_safe setup wire index packet owners env)

end BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate.bundle_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate.bundle_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate.finish_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate.finish_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate.bundle_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate.bundle_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate.finish_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate.finish_zero
