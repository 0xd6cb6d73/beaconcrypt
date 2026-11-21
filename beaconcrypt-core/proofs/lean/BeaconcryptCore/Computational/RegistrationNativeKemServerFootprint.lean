-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint

/-! The actual selected Server SDK exposes encapsulation but never creates an owner key or reveals a private KEM secret. These zero bills include all native authentication, replay, reservation, root-controller, request-log and one-use retention branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemBeaconFootprint (Kind)
open RegistrationNativeKemCompilerFootprint (predicate)
open RegistrationNativeKemServerInterface (Spec Ambient)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}

private theorem ambient_zero (kind : Kind) (query : (Ambient n mlSource).Domain) :
    OracleComp.IsQueryBoundP
      ((Spec n mlSource KemSK).query (.inl query) : OracleComp (Spec n mlSource KemSK) ((Ambient n mlSource).Range query))
      (predicate (Ambient n mlSource) KemSK kind) 0 := by
  simp [predicate, isQueryBoundP_query_iff]

private theorem modify_zero (kind : Kind)
    (change : RegistrationNativeKemServerState.State n mlSource → RegistrationNativeKemServerState.State n mlSource) :
    (RegistrationNativeKemServerInterface.modify (KemSK := KemSK) change).IsQueryBoundP
      (predicate (Ambient n mlSource) KemSK kind) 0 := by
  unfold RegistrationNativeKemServerInterface.modify
  exact isQueryBoundP_bind (ambient_zero kind .get) (fun before _ => ambient_zero kind (.put (change before)))

/-- Every actual native Server primitive has zero private birth/reveal cost, including exposed encapsulation and native refusal. -/
theorem primitive_zero (checks : Checks) (kind : Kind) (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    (RegistrationNativeKemServerInterface.primitive (n := n) (mlSource := mlSource) (KemSK := KemSK) checks query).IsQueryBoundP
      (predicate (Ambient n mlSource) KemSK kind) 0 := by
  cases query with
  | convertPublic key | convertSecret role | generate role | dh request =>
      simp [RegistrationNativeKemServerInterface.primitive, QueryImpl.apply_compose,
        RegistrationNativeKemInterface.server, RegistrationNativeKemInterface.other,
        RegistrationNativeKemServerInterface.lift, predicate, isQueryBoundP_query_iff]
  | decapsulate ciphertext =>
      simp [RegistrationNativeKemServerInterface.primitive, QueryImpl.apply_compose,
        RegistrationNativeKemInterface.server]
  | encapsulate key =>
      cases key with
      | none => simp [RegistrationNativeKemServerInterface.primitive, QueryImpl.apply_compose,
          RegistrationNativeKemInterface.server]
      | some key =>
          simp only [RegistrationNativeKemServerInterface.primitive, QueryImpl.apply_compose,
            RegistrationNativeKemInterface.server]
          split
          · simp [RegistrationNativeKemInterface.encapsulate, RegistrationNativeKemServerInterface.lift,
              predicate, isQueryBoundP_query_iff]
          · simp

private theorem agreement_step (setup : Setup base KemSK) (checks : Checks) (kind : Kind)
    (query : RegistrationAgreementExecutor.Spec.Domain) :
    (RegistrationNativeKemServerInterface.agreement (n := n) (mlSource := mlSource) setup checks query).IsQueryBoundP
      (predicate (Ambient n mlSource) KemSK kind) 0 := by
  unfold RegistrationNativeKemServerInterface.agreement
  apply isQueryBoundP_bind (m := 0) (modify_zero kind _)
  intro returned _supported
  cases query <;> first | exact primitive_zero checks kind _ | simp [RegistrationNativeKemServerInterface.agreementCore]

/-- The literal root/agreement continuation is quiet for both private KEM classes, independently of its optional outcomes. -/
theorem agreement_zero (setup : Setup base KemSK) (checks : Checks) (kind : Kind)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    (simulateQ (RegistrationNativeKemServerInterface.agreement (n := n) (mlSource := mlSource) setup checks) work).IsQueryBoundP
      (predicate (Ambient n mlSource) KemSK kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (OracleComp.isQueryBoundP_false work 0)
  intro query
  exact agreement_step setup checks kind query

attribute [local irreducible] RegistrationReplaySchedule.begin

/-- Actual SDK acceptance adds neither private creation nor secret reveal before or after any authentication/replay branch. -/
theorem accept_zero (setup : Setup base KemSK) (checks : Checks) (kind : Kind)
    (packet : registration.InitPacket) :
    (RegistrationNativeKemServerInterface.accept (n := n) (mlSource := mlSource) setup checks packet).IsQueryBoundP
      (predicate (Ambient n mlSource) KemSK kind) 0 := by
  unfold RegistrationNativeKemServerInterface.accept
  apply isQueryBoundP_bind (m := 0) (ambient_zero kind (.authenticate packet))
  intro checked _supported
  repeat first
    | simp only [isQueryBoundP_pure]
    | exact ambient_zero kind _
    | (apply isQueryBoundP_bind (m := 0) (ambient_zero kind .get); intro before _reached)
    | (apply isQueryBoundP_bind (m := 0) (agreement_zero setup checks kind _); intro completed _reached)
    | split

/-- The actual typed-attempt increment preserves the zero private creation/reveal bill. -/
theorem typed_zero (setup : Setup base KemSK) (checks : Checks) (kind : Kind)
    (packet : registration.InitPacket) :
    (RegistrationNativeKemServerInterface.typedAccept (n := n) (mlSource := mlSource) setup checks packet).IsQueryBoundP
      (predicate (Ambient n mlSource) KemSK kind) 0 := by
  unfold RegistrationNativeKemServerInterface.typedAccept
  exact isQueryBoundP_bind (modify_zero kind _) (fun _ _ => accept_zero setup checks kind packet)

end BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint.primitive_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint.primitive_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint.agreement_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint.agreement_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint.accept_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint.accept_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint.typed_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerFootprint.typed_zero
