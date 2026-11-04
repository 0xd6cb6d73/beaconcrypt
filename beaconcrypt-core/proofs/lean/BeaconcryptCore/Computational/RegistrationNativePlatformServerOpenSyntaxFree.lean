-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Every branch of the actual corrected OPEN accept syntax is independent of material-demand and publication callbacks. Reservation remains a real query and every prefix/prepare reply remains available. The zero-query result is structural over all replies. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformServerOpenSyntax (Spec protocol reserve)
open RegistrationNativePlatformServerReferenceAccept (PublicM)
variable {n : Nat} {ι KemSK A : Type} {base : OracleSpec ι}

def IsService : (Spec n KemSK).Domain → Prop
  | .inl query => RegistrationNativePlatformServerOpenServiceFree.IsService (n := n) (KemSK := KemSK) query
  | .inr _ => False

instance : DecidablePred (IsService (n := n) (KemSK := KemSK)) := fun query => by
  cases query with
  | inl query => exact inferInstanceAs (Decidable (RegistrationNativePlatformServerOpenServiceFree.IsService (n := n) (KemSK := KemSK) query))
  | inr _ => exact isFalse id

theorem transport_zero {I Source Target Value : Type} {queries : OracleSpec I}
    (excluded : I → Prop) [DecidablePred excluded]
    (left : QueryImpl queries (StateT Source ProbComp)) (right : QueryImpl queries (StateT Target ProbComp))
    (realize : Source → Target)
    (step : ∀ query before, ¬ excluded query → Prod.map id realize <$> (left query).run before = (right query).run (realize before))
    (work : OracleComp queries Value) (free : work.IsQueryBoundP excluded 0) (before : Source) :
    Prod.map id realize <$> (simulateQ left work).run before = (simulateQ right work).run (realize before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at free
    have allowed : ¬ excluded query := free.1.resolve_right (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← step query before allowed, bind_map_left]
    apply bind_congr
    rintro ⟨reply, after⟩
    apply ih reply _ after
    simpa only [allowed, ite_false] using free.2 reply

theorem effects_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) :
    (simulateQ (RegistrationNativePlatformServerOpenControl.effects (protocol (KemSK := KemSK))) work).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro query
  simp [RegistrationNativePlatformServerOpenControl.effects, QueryImpl.compose,
    RegistrationBeaconReferenceCompiler.effect, protocol, IsService,
    RegistrationNativePlatformServerOpenServiceFree.IsService, isQueryBoundP_query_iff]

theorem pin_free (current : session.ServerAuthenticationPin) :
    (RegistrationNativePlatformServerReferenceAccept.pin (RegistrationNativePlatformServerOpenControl.effects (protocol (n := n) (KemSK := KemSK))) current).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  unfold RegistrationNativePlatformServerReferenceAccept.pin
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simpa only [RegistrationNativePlatformServerReferenceAccept.hash, bind_pure_comp, isQueryBoundP_map_iff, simulateQ_spec_query, ite_false] using
    (effects_free (n := n) (KemSK := KemSK) (((PqxdhRecordLiftInterface.EnvEffects n).query
      (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes query)))) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _))

theorem agreement_free (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePlatformServerOpenKernel.agreement (protocol (n := n)) setup checks packet authenticated).run before).run env).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  change (simulateQ protocol (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run before).run env)).IsQueryBoundP (IsService (KemSK := KemSK)) 0
  apply RawCtxSourceOpen.simulate_bound _ (RegistrationNativePlatformServerOpenServiceFree.IsService (KemSK := KemSK)) _ _ 0
    (RegistrationNativePlatformServerOpenServiceFree.agreement_free setup checks packet authenticated before env)
  intro query
  simp only [protocol, isQueryBoundP_query_iff, IsService]
  split_ifs <;> simp_all

theorem lift_free (work : OracleComp (Spec n KemSK) A) (free : work.IsQueryBoundP (IsService (n := n) (KemSK := KemSK)) 0)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    (((StateT.lift (StateT.lift work) : PublicM (OracleComp (Spec n KemSK)) A).run before).run env).IsQueryBoundP (IsService (n := n) (KemSK := KemSK)) 0 := by
  simpa only [StateT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff] using free

theorem retain_free (ready : RegistrationServerReferenceRoot.Ready)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePlatformServerReferenceAccept.retain ready : PublicM (OracleComp (Spec n KemSK)) _).run before).run env).IsQueryBoundP (IsService (n := n) (KemSK := KemSK)) 0 := by
  dsimp only [RegistrationNativePlatformServerReferenceAccept.retain, StateT.run]
  cases current : RegistrationServerMaterialFrontend.retain ready before <;> trivial

theorem afterAuthentication_free (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePlatformServerOpenControl.afterAuthentication (protocol (n := n)) reserve setup checks packet authenticated).run before).run env).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformServerOpenControl.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · apply isQueryBoundP_bind (m := 0) (lift_free reserve (by simp [reserve, isQueryBoundP_query_iff, IsService]) before env)
    rintro ⟨⟨admitted, current⟩, currentEnv⟩ _
    cases admitted with
    | false => trivial
    | true =>
      simp only [ite_true]
      apply isQueryBoundP_bind (m := 0) (agreement_free setup checks packet authenticated current currentEnv)
      rintro ⟨⟨accepted, after⟩, afterEnv⟩ _
      cases accepted with
      | fail error | div => trivial
      | ok selected => cases selected with
        | none => trivial
        | some ready => exact retain_free ready after afterEnv

attribute [local irreducible] RegistrationAuthenticationCompiler.program

theorem afterPin_free (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (current : RegistrationNativeServerPinRecompute.PinReply)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePlatformServerOpenControl.afterPin (protocol (n := n)) reserve setup checks verify packet current).run before).run env).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  unfold RegistrationNativePlatformServerOpenControl.afterPin
  cases current with
  | fail error | div => trivial
  | ok selected => cases selected with
    | none => trivial
    | some pin =>
      simp only [StateT.run_bind]
      apply isQueryBoundP_bind (m := 0) (lift_free (n := n) (KemSK := KemSK) _
        (effects_free (n := n) (KemSK := KemSK) (RegistrationAuthenticationCompiler.program (n := n) setup.source.crypto verify pin packet)) before env)
      rintro ⟨⟨checked, after⟩, afterEnv⟩ _
      cases checked with
      | fail error | div => trivial
      | ok pair =>
        rcases pair with ⟨events, authentication⟩
        cases authentication
        all_goals first | exact afterAuthentication_free setup checks packet _ after afterEnv | trivial

theorem accept_free (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePlatformServerOpenSyntax.accept (n := n) setup checks verify packet).run before).run env).IsQueryBoundP (IsService (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformServerOpenSyntax.accept, RegistrationNativePlatformServerOpenControl.accept,
    StateT.run_bind, StateT.run_get, pure_bind]
  apply isQueryBoundP_bind (m := 0) (lift_free _ (pin_free before.pin) before env)
  rintro ⟨⟨current, after⟩, afterEnv⟩ _
  exact afterPin_free setup checks verify packet current after afterEnv

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.transport_zero' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.transport_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.effects_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.effects_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.pin_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.pin_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.agreement_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.agreement_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.lift_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.lift_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.retain_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.retain_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.afterAuthentication_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.afterAuthentication_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.afterPin_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.afterPin_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.accept_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree.accept_free
