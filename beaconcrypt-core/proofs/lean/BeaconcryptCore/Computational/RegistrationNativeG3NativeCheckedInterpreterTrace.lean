-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter

/-! The native unchecked preparation audit is reconstructed from the exact same final G2 chronology of the full native interpreter. The reconstruction retains every frontend reply, ordinary state, provider state and trace event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreterTrace
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordNativePlain (NativeFrame NativeProvider native)
open RegistrationNativeG3NativeCheckedInterpreter (observed)
open RegistrationNativeG3NativeCheckedTrace (read)
open RegistrationNativeKeyCompiler (KeySpec)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (target : Option PqxdhJointIdentity.DhOutput) (provider : NativeProvider KemSK ProviderState)

abbrev Base (n : Nat) (KemSK ProviderState : Type) := RegistrationNativeG2Trace.State × NativeFrame n KemSK ProviderState
abbrev Observed (n : Nat) (KemSK ProviderState : Type) := RegistrationNativeG2Trace.State × (RegistrationNativeG3NativeChecked.State × NativeFrame n KemSK ProviderState)

def embed (before : Base n KemSK ProviderState) : Observed n KemSK ProviderState :=
  (before.1, (read (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) before.1.events, before.2))

noncomputable def unobserved : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
    (StateT (Base n KemSK ProviderState) (OracleComp KeySpec)) :=
  ((native setup wire route sign seed scalar target provider).mapStateTBase RegistrationNativeG2Trace.handler).flattenStateT

noncomputable def traced : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
    (StateT (Observed n KemSK ProviderState) (OracleComp KeySpec)) :=
  ((observed setup wire route sign seed scalar target provider).mapStateTBase RegistrationNativeG2Trace.handler).flattenStateT

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem flattened_apply {S T : Type}
    (outer : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT T (OracleComp KeySpec)))
    (inner : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT S (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK))))
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : S × T) :
    (outer.mapStateTBase inner).flattenStateT query before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ outer ((inner query).run before.1)).run before.2 := rfl

/-- Every original native traced callback reconstructs the unchecked audit from that same reached chronological state. -/
theorem query_source (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : Base n KemSK ProviderState) :
    Prod.map id (embed setup seed scalar) <$>
      (unobserved setup wire route sign seed scalar target provider query).run before =
      (traced setup wire route sign seed scalar target provider query).run (embed setup seed scalar before) := by
  simp only [unobserved, traced, flattened_apply, RegistrationNativeG2Trace.handler,
    StateT.run, simulateQ_map, simulateQ_spec_query, observed, state_map_apply,
    Functor.map_map, Prod.map_def, id_eq, embed, RegistrationNativeG3NativeCheckedTrace.query_read]

/-- The complete adaptive native interpretation retains its output and full state while reconstructing the unchecked audit from its own final trace. -/
theorem program_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : Base n KemSK ProviderState) :
    Prod.map id (embed setup seed scalar) <$>
      (simulateQ (unobserved setup wire route sign seed scalar target provider) work).run before =
      (simulateQ (traced setup wire route sign seed scalar target provider) work).run (embed setup seed scalar before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (embed setup seed scalar)
    (query_source setup wire route sign seed scalar target provider) work before

/-- The actual nested traced interpreter yields exactly the same final audit fold, including the original complete chronological trace. -/
theorem nested_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (trace : RegistrationNativeG2Trace.State) (before : NativeFrame n KemSK ProviderState) :
    (simulateQ (observed setup wire route sign seed scalar target provider)
      ((simulateQ RegistrationNativeG2Trace.handler work).run trace)).run
        (read (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) trace.events, before) =
      (fun result => (result.1, (read (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) result.1.2.events, result.2))) <$>
        (simulateQ (native setup wire route sign seed scalar target provider)
          ((simulateQ RegistrationNativeG2Trace.handler work).run trace)).run before := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun result : Value × Observed n KemSK ProviderState => ((result.1, result.2.1), result.2.2)) <$>
      (simulateQ (traced setup wire route sign seed scalar target provider) work).run
        (embed setup seed scalar (trace, before)) = _
  rw [← program_source]
  simp only [Functor.map_map, Prod.map_def, id_eq, embed, unobserved]

end BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreterTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreterTrace.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreterTrace.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreterTrace.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreterTrace.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreterTrace.nested_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreterTrace.nested_source
