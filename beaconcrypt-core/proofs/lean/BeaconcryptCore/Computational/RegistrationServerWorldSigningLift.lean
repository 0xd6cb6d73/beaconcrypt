-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerSigningWorldSource
import BeaconcryptCore.Computational.RegistrationWorldServerCompletion

/-! Actual outgoing hash/sign programs update only the current World and chronological signing log. This exact local lift connects the concrete Server publication controller to its per-query source laws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationServerWorldSigningLift
variable {n : Nat} {Auxiliary Value Encoded : Type}

private theorem query_run
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Request) (before : RegistrationWorldAgreement.State n Auxiliary) :
    (RegistrationServerSigningWorldSource.source sign query).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (RegistrationWorldSigning.outgoing sign query).run before.world := rfl

/-- Every adaptive source signing program preserves all non-signing local state. -/
theorem program
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Value) (before : RegistrationWorldAgreement.State n Auxiliary) :
    (simulateQ (RegistrationServerSigningWorldSource.source sign) work).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ (RegistrationWorldSigning.outgoing sign) work).run before.world := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, query_run,
        bind_map_left, ih, map_bind]

/-- The literal source Server signing/publication stage is precisely this same local lift. -/
theorem completion
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    RegistrationWorldServerCompletion.signing (n := n) (Auxiliary := Auxiliary) sign encode pending =
      simulateQ (RegistrationServerSigningWorldSource.source sign)
        (RegistrationWorldServerPublication.program encode pending) := by
  funext before
  change (RegistrationWorldServerCompletion.signing sign encode pending).run before =
    (simulateQ (RegistrationServerSigningWorldSource.source sign) (RegistrationWorldServerPublication.program encode pending)).run before
  rw [program]
  rfl

end BeaconcryptCore.Computational.RegistrationServerWorldSigningLift

/-- info: 'BeaconcryptCore.Computational.RegistrationServerWorldSigningLift.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerWorldSigningLift.program
/-- info: 'BeaconcryptCore.Computational.RegistrationServerWorldSigningLift.completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerWorldSigningLift.completion
