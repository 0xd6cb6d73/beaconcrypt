-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateScope
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateFamily
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
/-! The identity-free late-key public program has an ordinary chosen-key interpretation. All auxiliary seeds are sampled by the executable adversary; the challenged seed remains solely in the genuine primitive interpreter. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateChosen
open PqxdhJointIdentity (Primitives IdentitySeed PublicIdentity Forgery wins)
open RegistrationNativeIdentityTemplateLateIdentity (Spec)
open RegistrationNativeIdentityTemplatePublicRegistry (Registry)
open RegistrationNativeIdentityTemplatePolicy (Public)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
variable {count : Nat}

noncomputable def work (joint : Primitives) (selected : Nat) (code : OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found))
    (registry : Registry) (before : Public) : OracleComp PublicSpec (Option Forgery) :=
  (fun result => result.1.map Prod.snd) <$> RegistrationNativeIdentityTemplateLateFamily.program joint selected code registry before

noncomputable def reduction (joint : Primitives) (target : Fin (count+1))
    (code : OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found))
    (registry : Registry) (before : Public) (fallback : Forgery) :=
  RegistrationNativeIdentityUnissuedChosenGame.reduction joint target (fun _keys => work joint target.val code registry before) fallback

private theorem source_dictionary (joint : Primitives) (seeds : Fin (count+1) → IdentitySeed) :
    (QueryImpl.Stateful.link
      (RegistrationNativeIdentityIndependentRouting.routeImpl (PqxdhJointIdentityFamily.familyPublic joint seeds))
      (PqxdhJointIdentityFreshness.sourceImpl joint seeds)) ∘ₛ RegistrationNativeIdentityTemplateProtocol.independent =
        RegistrationNativeIdentityTemplateChosenSource.reserved joint seeds := by
  funext query before
  rcases query with (dynamic | report) | coin
  · simp only [QueryImpl.apply_compose,RegistrationNativeIdentityTemplateProtocol.independent,simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose,RegistrationNativeIdentityTemplateProtocol.independent,simulateQ_pure]
    rfl
  · simp only [QueryImpl.apply_compose,RegistrationNativeIdentityTemplateProtocol.independent,simulateQ_spec_query]
    have expanded := QueryImpl.Stateful.link_impl_apply_run
      (RegistrationNativeIdentityIndependentRouting.routeImpl (PqxdhJointIdentityFamily.familyPublic joint seeds))
      (PqxdhJointIdentityFreshness.sourceImpl joint seeds) (.inr coin) before.1 before.2
    simp only [StateT.run] at expanded
    rw [expanded]
    simp only [RegistrationNativeIdentityIndependentRouting.routeImpl,
      RegistrationNativeIdentityTemplateChosenSource.reserved,QueryImpl.Stateful.Frame.prod]
    rfl

/-- The late-discovered-key family experiment has exactly one ordinary weak-EUF interpretation. E samples all independent other keys internally and accepts no challenged seed or hidden source state. -/
theorem probability_eq (joint : Primitives) (target : Fin (count+1))
    (code : OracleComp Spec (Option RegistrationNativeIdentityCensorPacketClient.Found))
    (allowed : code.AllQueriesSatisfy RegistrationNativeIdentityTemplateChosenSource.TemplateAllowed)
    (registry : Registry) (before : Public) (fallback : Forgery) :
    Pr{let result ← (RegistrationNativeIdentityTemplateLateFamily.run joint (count+1) target.val code registry before)}[
      wins joint (PqxdhJointIdentityFamily.familyPublic joint result.1 target)
        ((result.2.1.1.map Prod.snd).getD fallback) (result.2.2.2.histories target) = true] =
    PqxdhJointIdentity.advantage joint (reduction joint target code registry before fallback) := by
  have ordinary := RegistrationNativeIdentityUnissuedChosenGame.probability_eq joint target
    (fun _keys => work joint target.val code registry before)
    (fun _keys => RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _
      (RegistrationNativeIdentityTemplateLateScope.program joint target.val code registry allowed before)) fallback
  have family (seeds : Fin (count+1) → IdentitySeed) :
      (simulateQ (QueryImpl.Stateful.link
        (RegistrationNativeIdentityIndependentRouting.routeImpl (PqxdhJointIdentityFamily.familyPublic joint seeds))
        (PqxdhJointIdentityFreshness.sourceImpl joint seeds))
        (RegistrationNativeIdentityTemplateLateFamily.independent joint target.val code registry before)).run
          (PqxdhDynamicIdentityRouting.initialPublicState,PqxdhJointIdentityFreshness.initialState (count+1)) =
      (simulateQ (RegistrationNativeIdentityTemplateChosenSource.reserved joint seeds)
        (RegistrationNativeIdentityTemplateLateFamily.program joint target.val code registry before)).run
          (PqxdhDynamicIdentityRouting.initialPublicState,PqxdhJointIdentityFreshness.initialState (count+1)) := by
    rw [RegistrationNativeIdentityTemplateLateFamily.independent,←QueryImpl.simulateQ_compose,source_dictionary]
  have exactGame :
      (fun result => wins joint (PqxdhJointIdentityFamily.familyPublic joint result.1 target)
        ((result.2.1.1.map Prod.snd).getD fallback) (result.2.2.2.histories target)) <$>
          RegistrationNativeIdentityTemplateLateFamily.run joint (count+1) target.val code registry before =
      RegistrationNativeIdentityUnissuedChosenGame.familyGame joint target
        (fun _keys => work joint target.val code registry before) fallback := by
    unfold RegistrationNativeIdentityTemplateLateFamily.run RegistrationNativeIdentityUnissuedChosenGame.familyGame
    simp only [map_bind,map_pure,work,simulateQ_map,StateT.run_map,bind_map_left]
    apply bind_congr
    intro seeds
    rw [family]
  have probability := congrArg (fun distribution => Pr{let accepted ← distribution}[accepted = true]) exactGame
  simp only [prEvent_map] at probability
  exact probability.trans ordinary

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateChosen
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateChosen.probability_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateChosen.probability_eq
