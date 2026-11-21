-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterChecked

/-! The finite checked closure projects only analysis preparation flags. Ordinary World/cache state and the complete word KEM pool/phase remain literal. Residual callbacks run on that same current state, and real suffix-key interpretation restores each actual material branch before adaptive composition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (State Provider handler)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationNativeSecretWordCheckedFrontend (PlainSpec)
open RegistrationNativeKeyCompiler (KeySpec)
open RegistrationNativeSecretWordServiceSource (realize)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Frame (n : Nat) (KemSK : Type) :=
  RegistrationNativePublicInterpreter.State n KemSK × RegistrationNativeSecretWordKemProvider.State KemSK

def drop (before : State n KemSK) : Frame n KemSK := (before.ordinary, before.kem)
def put (before : Frame n KemSK) : State n KemSK := ⟨fun _ => false, before.1, before.2⟩

noncomputable def residual (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain) :
    StateT (Frame n KemSK) (OracleComp KeySpec) ((RegistrationNativeSecretWordInterface.Spec n KemSK).Range query) := fun before =>
  simulateQ (realize setup.source candidate)
    (Prod.map id drop <$> (handler setup wire route sign input inside provider query).run (put before))

noncomputable def plain (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (PlainSpec n KemSK) (StateT (Frame n KemSK) (OracleComp KeySpec))
  | .inl query => StateT.lift (KeySpec.query query)
  | .inr (.inl query) => residual setup wire route sign input inside provider candidate (.inl (.inr (.inl (.inr query))))
  | .inr (.inr (.inl query)) => residual setup wire route sign input inside provider candidate (.inl (.inr (.inr query)))
  | .inr (.inr (.inr query)) => residual setup wire route sign input inside provider candidate (.inr query)

def IsRoot : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain → Prop
  | .inl (.inl _) | .inl (.inr (.inl (.inl _))) => True
  | _ => False

/-- Actual residual Common, KEM and record callbacks are independent of the dropped preparation flags and retain every other state coordinate. -/
theorem residual_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain) (quiet : ¬ IsRoot query) (before : State n KemSK) :
    simulateQ (realize setup.source candidate)
      (Prod.map id drop <$> (handlerChecked setup wire route sign input inside provider query).run before) =
      (residual setup wire route sign input inside provider candidate query).run (drop before) := by
  rcases query with (message | (message | common) | kem) | record
  · exact False.elim (quiet trivial)
  · exact False.elim (quiet trivial)
  all_goals simp only [residual, drop, put, handlerChecked, handler,
    RegistrationNativeSecretWordInterpreter.ordinary, RegistrationNativeSecretWordInterpreter.routed,
    StateT.run, Functor.map_map, Prod.map_def, id_eq]

def keys : QueryImpl KeySpec (OracleComp (PlainSpec n KemSK)) := fun query =>
  (PlainSpec n KemSK).query (.inl query)

def opened (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option Key) :
    QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (OracleComp (PlainSpec n KemSK))
  | .inl (.inl message) => pure ((input message).map (fun _ => message))
  | .inl (.inr (.inl (.inl message))) => match input message with
      | none => pure none
      | some key => (some ∘ RegistrationNativePairedChoice.Choice.known) <$>
          simulateQ keys (RegistrationNativeSecretWordServiceSource.nativeMaterial source inside candidate key)
  | .inl (.inr (.inl (.inr query))) => (PlainSpec n KemSK).query (.inr (.inl query))
  | .inl (.inr (.inr query)) => (PlainSpec n KemSK).query (.inr (.inr (.inl query)))
  | .inr query => (PlainSpec n KemSK).query (.inr (.inr (.inr query)))

/-- Erasing the Unit audit leaves the actual open checked callback, with all native residual requests forwarded exactly once. -/
theorem erase_query (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option Key) (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain) :
    simulateQ RegistrationNativeSecretWordCheckedFrontend.erase
      (RegistrationNativeSecretWordCheckedFrontend.implementation source inside candidate input query) =
      opened source inside candidate input query := by
  rcases query with (message | (message | common) | kem) | record
  · simp only [RegistrationNativeSecretWordCheckedFrontend.implementation,
      RegistrationNativeSecretWordChecked.preparation, RegistrationNativeSecretWordChecked.audit,
      simulateQ_bind, simulateQ_spec_query, RegistrationNativeSecretWordCheckedFrontend.localLift,
      RegistrationNativeSecretWordCheckedFrontend.erase, simulateQ_pure, pure_bind, opened]
  · simp only [RegistrationNativeSecretWordCheckedFrontend.implementation,
      RegistrationNativeSecretWordChecked.material, RegistrationNativeSecretWordChecked.audit,
      simulateQ_bind, simulateQ_spec_query, RegistrationNativeSecretWordCheckedFrontend.localLift,
      RegistrationNativeSecretWordCheckedFrontend.erase, pure_bind, opened]
    cases input message with
    | none => simp only [simulateQ_pure]
    | some key =>
        simp only [simulateQ_map, ← QueryImpl.simulateQ_compose]
        rfl
  · simp only [RegistrationNativeSecretWordCheckedFrontend.implementation, simulateQ_spec_query,
      RegistrationNativeSecretWordCheckedFrontend.erase, opened]
  · simp only [RegistrationNativeSecretWordCheckedFrontend.implementation, simulateQ_spec_query,
      RegistrationNativeSecretWordCheckedFrontend.erase, opened]
  · simp only [RegistrationNativeSecretWordCheckedFrontend.implementation, simulateQ_spec_query,
      RegistrationNativeSecretWordCheckedFrontend.erase, opened]

private theorem keys_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (work : OracleComp KeySpec Value) (before : Frame n KemSK) :
    (simulateQ (plain setup wire route sign input inside provider candidate) (simulateQ keys work)).run before =
      (fun value => (value, before)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, keys, plain, StateT.run_bind,
        StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
      exact bind_congr fun reply => ih reply

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) :
    (observe <$> work) state = Prod.map observe id <$> work state := by
  change (work state >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

private theorem keys_apply (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (work : OracleComp KeySpec Value) (before : Frame n KemSK) :
    (simulateQ (plain setup wire route sign input inside provider candidate) (simulateQ keys work)) before =
      (fun value => (value, before)) <$> work :=
  keys_program setup wire route sign input inside provider candidate work before

/-- The checked symbolic callback closes into the same literal key/residual interpreter after dropping only its preparation flags. -/
theorem query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain) (before : State n KemSK) :
    simulateQ (realize setup.source candidate)
      (Prod.map id drop <$> (handlerChecked setup wire route sign input inside provider query).run before) =
      (simulateQ (plain setup wire route sign input inside provider candidate)
        (simulateQ RegistrationNativeSecretWordCheckedFrontend.erase
          (RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate input query))).run (drop before) := by
  rw [erase_query]
  rcases query with (message | (message | common) | kem) | record
  · simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.roots, StateT.run,
      RegistrationNativeSecretWordServiceChecked.checked, RegistrationNativeSecretWordService.handler,
      map_pure, simulateQ_pure, opened, state_pure_apply, Prod.map_def, id_eq, drop]
  · simp only [handlerChecked, RegistrationNativeSecretWordInterpreter.roots, StateT.run,
      RegistrationNativeSecretWordServiceChecked.checked, opened]
    cases formed : input message with
    | none => simp only [map_pure, simulateQ_pure, state_pure_apply, Prod.map_def, id_eq, drop]
    | some key =>
        simp only [Functor.map_map, simulateQ_map,
          RegistrationNativeSecretWordServiceSource.material_source,
          state_map_apply, keys_apply, Functor.map_map, Prod.map_def, id_eq, Function.comp_def, drop]
  · simpa only [opened, simulateQ_spec_query, plain] using residual_input setup wire route sign input inside provider candidate (.inl (.inr (.inl (.inr common)))) (by simp only [IsRoot, not_false_eq_true]) before
  · simpa only [opened, simulateQ_spec_query, plain] using residual_input setup wire route sign input inside provider candidate (.inl (.inr (.inr kem))) (by simp only [IsRoot, not_false_eq_true]) before
  · simpa only [opened, simulateQ_spec_query, plain] using residual_input setup wire route sign input inside provider candidate (.inr record) (by simp only [IsRoot, not_false_eq_true]) before

/-- The exact finite callback frame composes through every adaptive symbolic program, retaining the complete ordinary World and opaque provider state. -/
theorem program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value) (before : State n KemSK) :
    simulateQ (realize setup.source candidate)
      (Prod.map id drop <$> (simulateQ (handlerChecked setup wire route sign input inside provider) work).run before) =
      (simulateQ (plain setup wire route sign input inside provider candidate)
        (simulateQ (RegistrationNativeSecretWordCheckedFrontend.erase ∘ₛ
          RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate input) work)).run (drop before) := by
  rw [simulateQ_map, QueryImpl.simulateQ_mapStateTBase_run]
  rw [← QueryImpl.simulateQ_compose]
  apply map_run_simulateQ_eq_of_query_map_eq _ _ drop ?_ work before
  intro current state
  simpa only [QueryImpl.mapStateTBase, StateT.run_mk, QueryImpl.compose,
    simulateQ_map, QueryImpl.simulateQ_compose] using
      query setup wire route sign input inside provider candidate current state

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure.residual_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure.residual_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure.erase_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure.erase_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedClosure.program
