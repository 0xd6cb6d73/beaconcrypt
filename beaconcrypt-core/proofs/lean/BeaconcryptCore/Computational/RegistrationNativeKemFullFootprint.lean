-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint

/-! Complete original raw native clients derive their private KEM creation cap and zero secret-reveal bill from the actual constructor, SDK, Beacon controllers, routing and unchanged secrecy wrapper. No supplied whole-program private-KEM resource condition is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemBeaconFootprint (Kind)
open RegistrationNativeKemCompilerFootprint (predicate beacon_bound frontend_lift_bound route_bound)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec kind)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

private theorem dispatcher_step (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (selected : Kind) (query : TypedSpec.Domain) :
    (RegistrationNativeKemDispatcherCompiler.handler (n := n) (mlSource := mlSource) setup wire checks query).IsQueryBoundP
      (predicate (RegistrationNativeKemFrontendInterface.Ambient n mlSource) KemSK selected)
      (if selected = .create ∧ kind query = 1 then 1 else 0) := by
  cases query with
  | inl coin =>
      simp [RegistrationNativeKemDispatcherCompiler.handler, RegistrationNativeKemBeaconCompiler.trusted,
        RegistrationNativeKemFrontendInterface.lift, predicate, isQueryBoundP_query_iff, kind]
  | inr command => cases command with
    | create edPin mlPin keyId =>
        simpa [RegistrationNativeKemDispatcherCompiler.handler, kind] using
          frontend_lift_bound (n := n) (mlSource := mlSource) selected _ _ (beacon_bound selected _ _
            (RegistrationNativeKemBeaconFootprint.create_bound setup selected edPin mlPin keyId))
    | bundle owner =>
        simpa [RegistrationNativeKemDispatcherCompiler.handler, kind] using frontend_lift_bound (n := n) (mlSource := mlSource) selected _ _ (beacon_bound selected _ 0
            (RegistrationNativeKemBeaconFootprint.bundle_zero setup selected wire owner))
    | finish owner packet =>
        simpa [RegistrationNativeKemDispatcherCompiler.handler, kind] using frontend_lift_bound (n := n) (mlSource := mlSource) selected _ _ (beacon_bound selected _ 0
            (RegistrationNativeKemBeaconFootprint.finish_zero setup selected wire owner packet))
    | accept packet =>
        simpa [RegistrationNativeKemDispatcherCompiler.handler, kind] using frontend_lift_bound (n := n) (mlSource := mlSource) selected _ 0
            (RegistrationNativeKemServerFootprint.typed_zero setup checks selected packet)
    | build session application | serverSend keyId plaintext | serverRaw raw | beaconSend owner plaintext | beaconRaw owner raw =>
        simp [RegistrationNativeKemDispatcherCompiler.handler, predicate, isQueryBoundP_query_iff, kind]
    | hmac key message => simp [RegistrationNativeKemDispatcherCompiler.handler, kind]
    | hash bytes =>
        simp [RegistrationNativeKemDispatcherCompiler.handler, RegistrationNativeKemBeaconCompiler.trusted,
          RegistrationNativeKemFrontendInterface.lift, predicate, isQueryBoundP_query_iff, kind]

/-- Actual selected-attempt routing preserves the concrete private KEM cost of every original typed command. -/
theorem parsed_step (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (parsed : Nat) (selected : Kind) (query : TypedSpec.Domain) :
    (RegistrationNativeKemParsedRouting.handler (n := n) (mlSource := mlSource) setup checks wire parsed query).IsQueryBoundP
      (predicate (RegistrationNativeKemParsedRouting.Ambient n mlSource) KemSK selected)
      (if selected = .create ∧ kind query = 1 then 1 else 0) := by
  cases query with
  | inl coin => exact route_bound (n := n) (mlSource := mlSource) selected false _ _ (dispatcher_step (n := n) (mlSource := mlSource) setup checks wire selected _)
  | inr command => cases command with
    | accept packet =>
        simp only [RegistrationNativeKemParsedRouting.handler]
        norm_num only [kind]
        apply isQueryBoundP_bind (m := 0) (by simp [RegistrationNativeKemParsedRouting.get, predicate, isQueryBoundP_query_iff])
        intro before _supported
        simpa [kind] using
          route_bound (n := n) (mlSource := mlSource) selected (decide (before.parsedAccepts = parsed)) _ _ (dispatcher_step (n := n) (mlSource := mlSource) setup checks wire selected (.inr (.accept packet)))
    | _ => exact route_bound (n := n) (mlSource := mlSource) selected false _ _ (dispatcher_step (n := n) (mlSource := mlSource) setup checks wire selected _)

/-- Original hidden test/fresh controllers never add native create calls. -/
theorem compile_creates (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) :
    (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work).IsQueryBoundP
      (fun query => kind query = 1) budget.create := by
  have compiled := RegistrationNativeFullCompiler.compile_bound crypto wire serverKeyId bounds mode work budget bounded 1
  have bill : (∑ full : Fin 14, PqxdhDeploymentCompileSecrecy.wrapCost bounds 1 full * budget.cap full) = budget.create := by
    simp [Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost, PqxdhDeploymentInterface.Budget.cap]
  simpa only [bill] using compiled

/-- The actual full raw compiler creates at most the original adversary's create allowance. -/
theorem full_creates (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (parsed : Nat) :
    (simulateQ (RegistrationNativeKemParsedRouting.handler (n := n) (mlSource := mlSource) setup checks wire parsed)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).IsQueryBoundP
      (predicate (RegistrationNativeKemParsedRouting.Ambient n mlSource) KemSK .create) budget.create := by
  apply RawCtxSourceOpen.simulate_bound _ (fun query => kind query = 1) _ _ budget.create
    (compile_creates setup.source.crypto wire serverKeyId bounds mode work budget bounded)
  intro query
  simpa only [true_and] using parsed_step (n := n) (mlSource := mlSource) setup checks wire parsed .create query

/-- Every actual complete raw native client has zero private KEM secret-reveal calls, with no disclosure premise. -/
theorem full_no_reveal (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (parsed : Nat) :
    (simulateQ (RegistrationNativeKemParsedRouting.handler (n := n) (mlSource := mlSource) setup checks wire parsed)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).IsQueryBoundP
      (predicate (RegistrationNativeKemParsedRouting.Ambient n mlSource) KemSK .reveal) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (OracleComp.isQueryBoundP_false _ 0)
  intro query
  simpa only [reduceCtorEq, false_and, ite_false] using parsed_step (n := n) (mlSource := mlSource) setup checks wire parsed .reveal query

end BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint.parsed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint.parsed_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint.compile_creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint.compile_creates
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint.full_creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint.full_creates
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint.full_no_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint.full_no_reveal
