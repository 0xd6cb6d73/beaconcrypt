-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting
import BeaconcryptCore.Computational.RegistrationNativeKemNoInput

/-! The actual compiled native encapsulation getter aborts at the selected cut before receiving its ciphertext/shared-secret reply. Its actual request-log prefix remains, and the normalized root collector cannot turn this abort into an accepted input. This instantiates the local optional-collector rule with the proved concrete callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemStoppedGetter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeKemNoInput (NoSome prefix_no_some)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def stop : QueryImpl (Spec n mlSource KemSK) (OptionT (OracleComp (Spec n mlSource KemSK))) :=
  RegistrationNativeKemCutStop.stop (fun query =>
    ((Spec n mlSource KemSK).query query : OracleComp (Spec n mlSource KemSK) _))

noncomputable def node (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl RegistrationAgreementExecutor.Spec (OptionT (OracleComp (Spec n mlSource KemSK))) := fun query =>
  simulateQ stop (simulateQ (RegistrationNativeKemRouting.route true)
    (simulateQ RegistrationNativeKemFrontendInterface.lift (RegistrationNativeKemServerInterface.agreement setup checks query)))

noncomputable def callbacks (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhBeaconPhase2Preparation.Word32)
      (OptionT (OracleComp (Spec n mlSource KemSK))) :=
  node setup checks ∘ₛ RegistrationAgreementRoot.callbacks

private theorem pure_none {Value : Type} : NoSome (pure none : OptionT (OracleComp (Spec n mlSource KemSK)) (Option Value)) := by
  intro value
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq, reduceCtorEq, not_false_eq_true]

/-- The actual typed root getter retains its request-log prefix and either aborts at the exposed query or returns the native checked refusal. -/
theorem encapsulation_no_some (setup : Setup base KemSK) (checks : Checks)
    (key : PqxdhKemIndCca.MlKem768PublicKey) :
    NoSome (callbacks (n := n) (mlSource := mlSource) setup checks (.encapsulate key)) := by
  simp only [callbacks, QueryImpl.compose, RegistrationAgreementRoot.callbacks, simulateQ_map, simulateQ_spec_query,
    node, RegistrationNativeKemServerInterface.agreement, simulateQ_bind, map_bind]
  apply prefix_no_some
  intro ignored
  simp only [RegistrationNativeKemServerInterface.agreementCore, RegistrationNativeKemServerInterface.primitive,
    QueryImpl.apply_compose, RegistrationNativeKemInterface.server]
  split
  · intro value supported
    simp only [RegistrationNativeKemInterface.encapsulate, simulateQ_map, simulateQ_spec_query,
      RegistrationNativeKemServerInterface.lift, RegistrationNativeKemFrontendInterface.lift,
      RegistrationNativeKemRouting.route, ite_true, stop, RegistrationNativeKemCutStop.stop,
      OptionT.run_map, OptionT.run_failure, map_pure, support_pure, Set.mem_singleton_iff,
      Option.map_none, reduceCtorEq] at supported
  · simpa only [simulateQ_pure, map_pure, RegistrationAgreementRoot.option] using
      (pure_none (n := n) (mlSource := mlSource) (KemSK := KemSK))

/-- The actual native root collector has no successful input after the selected literal KEM getter is stopped. No callback-failure or cut-reachability premise is supplied. -/
theorem collect_no_input (setup : Setup base KemSK) (checks : Checks)
    (verified : PqxdhServerRootPreparation.Verified registration.InitPacket) :
    NoSome (simulateQ (callbacks (n := n) (mlSource := mlSource) setup checks)
      (PqxdhServerRootPreparation.collectVerified verified)) :=
  RegistrationNativeKemNoInput.collect_no_some _ verified (encapsulation_no_some setup checks verified.keys.pqKey)

def serverResult : RustM agreement.AgreementEffect → Option agreement.ServerAgreement
  | .ok (.ServerComplete accepted) => some accepted
  | _ => none

/-- The literal native replay/controller continuation cannot complete a Server agreement after its actual selected encapsulation getter is stopped. -/
theorem agreement_no_completion (setup : Setup base KemSK) (checks : Checks)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (history : RegistrationReplaySchedule.State) :
    NoSome (serverResult <$> simulateQ (node (n := n) (mlSource := mlSource) setup checks)
      (RegistrationReplaySchedule.begin control authenticated history)) := by
  rw [RegistrationReplaySchedule.begin_eq]
  split
  · simpa only [simulateQ_pure, map_pure, serverResult] using
      (pure_none (n := n) (mlSource := mlSource) (KemSK := KemSK))
  · rw [RegistrationAgreementRoot.server_normalized control packet authenticated]
    simp only [RegistrationAgreementRoot.normalized, simulateQ_bind, map_bind]
    rw [← QueryImpl.simulateQ_compose]
    change NoSome (simulateQ (callbacks setup checks)
      (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)) >>= _)
    apply RegistrationNativeKemNoInput.optional_no_some _ (collect_no_input setup checks _)
    exact pure_none

end BeaconcryptCore.Computational.RegistrationNativeKemStoppedGetter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemStoppedGetter.encapsulation_no_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemStoppedGetter.encapsulation_no_some
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemStoppedGetter.collect_no_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemStoppedGetter.collect_no_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemStoppedGetter.agreement_no_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemStoppedGetter.agreement_no_completion
