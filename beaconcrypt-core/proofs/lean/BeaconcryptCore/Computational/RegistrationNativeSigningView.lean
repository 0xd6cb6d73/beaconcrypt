-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLocalView

/-! Actual response signing keeps the full chronological signing-attempt ledger under private accounting projection, including failures before dynamic packing. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSigningView
open RegistrationWorldSigning (State)
variable {n : Nat} {Value Encoded : Type}

def project (before : State n) : State n := (RegistrationNativeWorldView.project before.1, before.2)

/-- Signing receipts remain literal under repeated projection. -/
theorem project_idempotent (before : State n) : project (project before) = project before := by
  simp only [project, RegistrationNativeWorldView.project_idempotent]

/-- Both actual outgoing callbacks retain their real reply, cache and attempted-signature receipt. -/
theorem outgoing_input
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : State n) :
    Prod.map id project <$> (RegistrationWorldSigning.outgoing sign query).run before =
      Prod.map id project <$> (RegistrationWorldSigning.outgoing sign query).run (project before) := by
  cases query with
  | hash request =>
      have law := congrArg (fun distribution => (fun result => (result.1, (result.2, before.2))) <$> distribution)
        (RegistrationNativeWorldViewEffects.effects_input
          (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))) before.1)
      simpa only [RegistrationWorldSigning.outgoing, StateT.run, Functor.map_map, Prod.map,
        id_eq, project, Function.comp_def] using law
  | sign request payload digest =>
      have first := RegistrationNativeWorldView.sampled (sign request) before.1
      have second := RegistrationNativeWorldView.sampled (sign request) (RegistrationNativeWorldView.project before.1)
      rw [RegistrationNativeWorldView.project_idempotent] at second
      have law := congrArg (fun distribution => (fun result => (result.1,
        (result.2, before.2 ++ [RegistrationSigningShared.Receipt.mk
          ⟨request.public_key, payload, BeaconcryptCore.Refinement.RegistrationSigningTrace.replyBytes result.1⟩ digest]))) <$>
        distribution) (first.trans second.symm)
      simpa only [RegistrationWorldSigning.outgoing, StateT.run, Functor.map_map, Prod.map,
        id_eq, project, Function.comp_def] using law

/-- Adaptive actual signing continuations keep all reached state and optional failure branches. -/
theorem outgoing_program
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Value) (before : State n) :
    Prod.map id project <$> (simulateQ (RegistrationWorldSigning.outgoing sign) work).run before =
      Prod.map id project <$> (simulateQ (RegistrationWorldSigning.outgoing sign) work).run (project before) :=
  RegistrationStateView.program_stable project project_idempotent _ (outgoing_input sign) work before

/-- The native publication wrapper retains full local auxiliary state and every actual signing receipt. -/
theorem signing_input {Auxiliary : Type}
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id RegistrationServerRecordWorldSource.project <$>
        (RegistrationWorldServerCompletion.signing sign encode pending).run before =
      Prod.map id RegistrationServerRecordWorldSource.project <$>
        (RegistrationWorldServerCompletion.signing sign encode pending).run (RegistrationServerRecordWorldSource.project before) := by
  have law := congrArg (fun distribution => (fun result => (result.1,
    { RegistrationServerRecordWorldSource.project before with world := result.2 })) <$> distribution)
    (outgoing_program sign (RegistrationWorldServerPublication.program encode pending) before.world)
  simpa only [RegistrationWorldServerCompletion.signing, StateT.run, Functor.map_map, Prod.map,
    id_eq, project, RegistrationServerRecordWorldSource.project, Function.comp_def] using law

end BeaconcryptCore.Computational.RegistrationNativeSigningView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSigningView.project_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSigningView.project_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSigningView.outgoing_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSigningView.outgoing_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSigningView.outgoing_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSigningView.outgoing_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSigningView.signing_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSigningView.signing_input
