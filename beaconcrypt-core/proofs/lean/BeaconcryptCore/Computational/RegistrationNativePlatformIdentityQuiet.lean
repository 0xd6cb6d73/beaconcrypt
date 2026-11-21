-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape

/-! The actual dynamic-writer bundle and corrected assigned-ID finish contain no indexed identity creation or reveal. This is a syntactic all-replies fact, including failed signing, writer failure and every rejected authentication/open/install continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityQuiet
open RegistrationNativeIdentityFrontend
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary Value Other Platform E : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def Allowed (n : Nat) (KemSK : Type) : (Trusted n KemSK).Domain → Prop
  | .inr (.service _ _) => True
  | .inl _ => True
  | _ => False

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
    | sign request payload digest => exact pure_safe (core.option.Option.None : RegistrationSigningShared.SignReply)
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

private theorem abort_safe (owner : Owner source) (value : Value) :
    Safe (abort owner *> pure value : M n KemSK Auxiliary source Value) := by
  simp only [abort, seqRight_eq_bind, bind_assoc, pure_bind]
  exact bind_safe _ _ (effect_safe _) (fun _ => pure_safe _)

private theorem install_safe (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) :
    Safe (RegistrationNativePlatformIdentityFinishRecord.install (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner completed) := by
  rw [RegistrationNativePlatformIdentityFinishRecord.install_exact]
  apply bind_safe _ _ (effect_safe _)
  intro installed
  cases installed with
  | false => exact abort_safe owner _
  | true => exact bind_safe _ _ (modify_safe _) (fun _ => pure_safe _)

private theorem record_after_safe (index : Nat) (owner : Owner source) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Safe (RegistrationNativePlatformIdentityFinishRecord.after (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner reply) := by
  cases reply with
  | fail error | div => exact abort_safe owner _
  | ok result => cases result with
    | Err error => exact abort_safe owner _
    | Ok established => exact install_safe index owner established

private theorem agreement_after_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (reply : RustM agreement.AgreementEffect) :
    Safe (RegistrationNativePlatformIdentityFinishSteps.afterAgreement (n := n) (Auxiliary := Auxiliary) setup wire index owner reply) := by
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
    Safe (RegistrationNativePlatformIdentityFinishSteps.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime reply) := by
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
    Safe (RegistrationNativePlatformIdentityFinishSteps.begin (n := n) (Auxiliary := Auxiliary) setup wire index owner pending oneTime packet) := by
  cases moved : pending.aborted_state with
  | fail error | div =>
      simpa only [RegistrationNativePlatformIdentityFinishSteps.begin, moved] using
        (pure_safe (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) _)
  | ok aborted =>
      simp only [RegistrationNativePlatformIdentityFinishSteps.begin, moved]
      exact bind_safe _ _ (modify_safe _) (fun _ => bind_safe _ _
        (program_safe _ (authentication_safe setup) _) (authentication_after_safe setup wire index owner oneTime))

private theorem finish_start_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (packet : Option registration.ResponsePacket) :
    Safe (RegistrationNativePlatformIdentityFinishRun.start (n := n) (Auxiliary := Auxiliary) setup wire index owner packet) := by
  cases phase : owner.phase with
  | initSent pending oneTime =>
      simpa only [RegistrationNativePlatformIdentityFinishRun.start, phase] using finish_begin_safe setup wire index owner pending oneTime packet
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simpa only [RegistrationNativePlatformIdentityFinishRun.start, phase] using
        (pure_safe (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (.ok none : RustM (Option Pqxdh.Bytes)))

/-- Every corrected assigned-ID finishing branch uses only ambient work, indexed signing and static DH: no identity creation or reveal occurs. -/
theorem finish_quiet (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) :
    Safe (RegistrationNativePlatformIdentityFinishRun.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  intro owners env
  cases found : owners[index]? with
  | none =>
    simp only [RegistrationNativePlatformIdentityFinishRun.finish, StateT.run_bind, StateT.run_get, pure_bind,
      found, StateT.run_pure]
    trivial
  | some owner =>
    simpa only [RegistrationNativePlatformIdentityFinishRun.finish, StateT.run_bind, StateT.run_get,
      pure_bind, found] using finish_start_safe setup wire index owner packet owners env

def PlatformAllowed (n : Nat) (KemSK : Type) : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain → Prop
  | .inl _ => True
  | .inr query => Allowed n KemSK query

def PlatformSafe (work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) : Prop :=
  ∀ owners env platform, AllQueriesSatisfy (((work.run owners).run env).run platform) (PlatformAllowed n KemSK)

private theorem simulate_allowed {I J A : Type} {left : OracleSpec I} {right : OracleSpec J}
    (implementation : QueryImpl left (OracleComp right)) (input : I → Prop) (output : J → Prop)
    (step : ∀ query, input query → AllQueriesSatisfy (implementation query) output)
    (work : OracleComp left A) (prior : AllQueriesSatisfy work input) :
    AllQueriesSatisfy (simulateQ implementation work) output := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp prior
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact allQueriesSatisfy_bind (step query first) (fun reply => ih reply (later reply))

theorem native_quiet (work : M n KemSK Auxiliary source Value) (prior : Safe work) :
    PlatformSafe (RegistrationNativePlatformIdentityProgram.native (Platform := Platform) work) := by
  intro owners env platform
  unfold RegistrationNativePlatformIdentityProgram.native
  apply mapped _ _ (PlatformAllowed n KemSK)
  exact simulate_allowed _ (Allowed n KemSK) (PlatformAllowed n KemSK) (fun _ permitted =>
    (allQueriesSatisfy_query_iff _ _).mpr permitted) _ (prior owners env)

private theorem all_true {I A : Type} {spec : OracleSpec I} (work : OracleComp spec A) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem platform_external (work : StateT Platform ProbComp Value) :
    PlatformSafe (RegistrationNativePlatformIdentityProgram.external (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) := by
  intro owners env platform
  unfold RegistrationNativePlatformIdentityProgram.external
  apply mapped _ _ (PlatformAllowed n KemSK)
  exact simulate_allowed _ (fun _ => True) (PlatformAllowed n KemSK) (fun query _ =>
    (allQueriesSatisfy_query_iff (spec := RegistrationNativePlatformIdentityProgram.Spec n KemSK)
      (.inl query) (PlatformAllowed n KemSK)).mpr trivial) _ (all_true _)

private theorem platform_pure (value : Value) :
    PlatformSafe (pure value : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) := by
  intro owners env platform
  simp only [StateT.run_pure]
  trivial

private theorem platform_bind (work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value)
    (next : Value → RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Other)
    (first : PlatformSafe work) (later : ∀ value, PlatformSafe (next value)) : PlatformSafe (work >>= next) := by
  intro owners env platform
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env platform)
    (fun result => later result.1.1.1 result.1.1.2 result.1.2 result.2)

private theorem platform_program {I : Type} {spec : OracleSpec I}
    (implementation : QueryImpl spec (RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source))
    (step : ∀ query, PlatformSafe (implementation query)) (work : OracleComp spec Value) :
    PlatformSafe (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using platform_pure value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact platform_bind _ _ (step query) ih

private theorem callback_quiet (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformWriter.Spec E).Domain) :
    PlatformSafe (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary) setup index owner writer query) := by
  cases query with
  | inl query => exact native_quiet _ (outgoing_safe setup index owner query)
  | inr query => exact platform_external _

private theorem next_quiet (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RegistrationNativePlatformIdentityBundle.Reply) :
    PlatformSafe (RegistrationNativePlatformIdentityBundle.next (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact platform_pure _
  | ok reply => cases reply with
    | Err error => exact platform_pure _
    | Ok published =>
      exact platform_bind _ _ (native_quiet _ (modify_safe _)) (fun _ =>
        platform_bind _ _ (native_quiet _ (effect_safe _)) (fun _ => platform_pure _))

private theorem bundled_quiet (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    PlatformSafe (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := Auxiliary) setup index owner oneTime writer) :=
  platform_bind _ _ (platform_program _ (callback_quiet setup index owner writer) _) (next_quiet index owner oneTime)

private theorem start_quiet (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    PlatformSafe (RegistrationNativePlatformIdentityBundleRun.start (n := n) (Auxiliary := Auxiliary) setup index owner writer) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
    exact platform_bind _ _ (native_quiet _ (sample_safe _)) (fun scalar => bundled_quiet setup index owner scalar writer)
  | freshWithCoins scalar =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind] using bundled_quiet setup index owner scalar writer
  | initSent pending scalar | established completed | aborted aborted =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase] using
      (platform_pure (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (Platform := Platform) (.ok none : RustM (Option (alloc.vec.Vec U8))))

/-- The whole effectful source bundle uses no identity create/reveal request on any writer or native reply, including repeated failed attempts. -/
theorem bundle_quiet (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    PlatformSafe (RegistrationNativePlatformIdentityBundleRun.bundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer) := by
  intro owners env platform
  cases found : owners[index]? with
  | none =>
    simp only [RegistrationNativePlatformIdentityBundleRun.bundle, StateT.run_bind, StateT.run_get,
      pure_bind, found, StateT.run_pure]
    trivial
  | some owner =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.bundle, StateT.run_bind, StateT.run_get,
      pure_bind, found] using start_quiet setup index owner writer owners env platform

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityQuiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityQuiet.finish_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityQuiet.finish_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityQuiet.native_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityQuiet.native_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityQuiet.bundle_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityQuiet.bundle_quiet
