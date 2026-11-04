-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Reassociation of the private conversion-readiness flag with an arbitrary complete backend state. The actual Core entry schedule erases only that flag and retains every backend poststate and result, for every failed reply. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementGuardState
open RegistrationAgreementExecutor
variable {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}

def implementation (base : QueryImpl Spec (StateT S m)) : QueryImpl Spec (StateT (Bool × S) m) :=
  fun request before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((RegistrationAgreementIdentityGuard.implementation base request).run before.1).run before.2

theorem program {Value : Type} (base : QueryImpl Spec (StateT S m)) (work : OracleComp Spec Value)
    (flag : Bool) (before : S) :
    (simulateQ (implementation base) work).run (flag, before) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((simulateQ (RegistrationAgreementIdentityGuard.implementation base) work).run flag).run before := by
  induction work using OracleComp.inductionOn generalizing flag before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [implementation, StateT.run, map_bind, bind_map_left]
    apply bind_congr
    rintro ⟨⟨reply, nextFlag⟩, after⟩
    exact ih reply nextFlag after

theorem server (base : QueryImpl Spec (StateT S m)) (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (before : S) :
    Prod.map id Prod.snd <$> (simulateQ (implementation base)
      (RegistrationAgreementExecutor.server control status authenticated)).run (false, before) =
      (simulateQ base (RegistrationAgreementExecutor.server control status authenticated)).run before := by
  rw [program, Functor.map_map]
  have erased := congrArg (fun work => work.run before)
    (RegistrationAgreementEntryReadiness.server base control status authenticated)
  simpa only [StateT.run_map, Functor.map_map, Prod.map, id_eq] using erased

theorem lookup (base : QueryImpl Spec (StateT S m)) (pending : peer.RegistrationLookup) (consumed : Bool) (before : S) :
    Prod.map id Prod.snd <$> (simulateQ (implementation base)
      (continueWith (pending.resume consumed) (drive 9))).run (false, before) =
      (simulateQ base (continueWith (pending.resume consumed) (drive 9))).run before := by
  rw [program, Functor.map_map]
  have erased := congrArg (fun work => work.run before)
    (RegistrationAgreementEntryReadiness.lookup base pending consumed)
  simpa only [StateT.run_map, Functor.map_map, Prod.map, id_eq] using erased
end BeaconcryptCore.Computational.RegistrationAgreementGuardState

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementGuardState.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementGuardState.program

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementGuardState.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementGuardState.server

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementGuardState.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementGuardState.lookup
