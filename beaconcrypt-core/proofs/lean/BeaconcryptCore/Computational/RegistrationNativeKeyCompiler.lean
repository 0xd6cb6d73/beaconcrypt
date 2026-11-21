-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationNativeKeyHybrid

/-! The actual prepare/demand phase interface compiles into a client that contains no protected PRK or root reply. It preserves known/off-protected source computations and preparation metadata. The only private table request occurs on an admitted protected material demand. This concrete client is the one supplied to the indexed five-hop key-schedule reduction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKeyCompiler
open RegistrationNativeKeyPhases (Meta State Value prepareMeta demandMeta onMeta erased cacheLens)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (HmacBlock HmacSha512 HmacOracle)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
abbrev KeySpec := RegistrationNativeKeyHybrid.Spec

def coins : QueryImpl unifSpec (OracleComp KeySpec) := fun query => KeySpec.query (.inl query)

def liftProb {Result : Type} (work : StateT Meta ProbComp Result) : StateT Meta (OracleComp KeySpec) Result :=
  fun before => simulateQ coins (work.run before)

def compiler (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl RegistrationNativeKeyPhases.Spec (StateT Meta (OracleComp KeySpec))
  | .inl coin => liftProb (StateT.lift (unifSpec.query coin))
  | .inr (.prepare message) => liftProb (prepareMeta input message)
  | .inr (.demand message) => do
      let selected ← liftProb (demandMeta input inside message)
      match selected with
      | none => pure none
      | some (bytes, protectedInput) =>
        if protectedInput then
          (fun output => some (.hidden output)) <$> StateT.lift (KeySpec.query (.inr bytes))
        else pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot source
          (RegistrationNativeRelatedRoot.nativeRoot source bytes))))

def client {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp RegistrationNativeKeyPhases.Spec Result) (initialMeta : Meta) : OracleComp KeySpec Result :=
  (simulateQ (compiler source input inside) work).run' initialMeta

/-- This private source interpreter retains the complete PRK cache while evaluating the real dependent root/initial/ongoing key schedule at material demand. -/
noncomputable def sourceInterpreter (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) :
    QueryImpl KeySpec (StateT HmacOracle.QueryCache ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin)
  | .inr bytes => PqxdhServerAuthKeySchedule.keySchedule source hmac <$> HmacOracle.randomOracle bytes

def interpret {Result : Type} (primitive : QueryImpl KeySpec (StateT HmacOracle.QueryCache ProbComp))
    (work : StateT Meta (OracleComp KeySpec) Result) : StateT State ProbComp Result := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ primitive (work.run before.1)).run before.2

private theorem map_apply {S Input Result : Type} (f : Input → Result) (work : StateT S ProbComp Input)
    (before : S) : (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

theorem interpret_pure {Result : Type}
    (primitive : QueryImpl KeySpec (StateT HmacOracle.QueryCache ProbComp)) (result : Result) :
    interpret primitive (pure result) = pure result := by
  funext before
  simp only [interpret, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

theorem interpret_bind {Input Result : Type}
    (primitive : QueryImpl KeySpec (StateT HmacOracle.QueryCache ProbComp))
    (work : StateT Meta (OracleComp KeySpec) Input) (next : Input → StateT Meta (OracleComp KeySpec) Result) :
    interpret primitive (work >>= next) = (interpret primitive work >>= fun result => interpret primitive (next result)) := by
  funext before
  change (interpret primitive (work >>= next)).run before =
    (interpret primitive work >>= fun result => interpret primitive (next result)).run before
  simp only [StateT.run_bind]
  simp only [interpret, StateT.run, StateT.monad_bind_def, StateT.bind,
    simulateQ_bind, map_bind, bind_map_left]

theorem liftProb_exact {Result : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (work : StateT Meta ProbComp Result) :
    interpret (sourceInterpreter source hmac) (liftProb work) = onMeta work := by
  funext before
  simp only [interpret, liftProb, StateT.run, ← QueryImpl.simulateQ_compose]
  have forward : sourceInterpreter source hmac ∘ₛ coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT HmacOracle.QueryCache ProbComp) := by
    funext query
    rfl
  rw [forward, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (liftM (work.run before.1) : StateT HmacOracle.QueryCache ProbComp _).run before.2 = onMeta work before
  rw [StateT.run_liftM, bind_pure_comp]
  simp only [onMeta, LazyOracleDiscard.StateLens.lift, LazyOracleDiscard.StateLens.fst,
    StateT.run, Functor.map_map]

theorem query_source (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : RegistrationNativeKeyPhases.Spec.Domain) :
    interpret (sourceInterpreter source hmac) (compiler source input inside query) =
      erased source hmac input inside query := by
  cases query with
  | inl coin => exact liftProb_exact _ _ _
  | inr request => cases request with
    | prepare message => exact liftProb_exact _ _ _
    | demand message =>
      simp only [compiler, interpret_bind, liftProb_exact, erased]
      apply congrArg (fun next => onMeta (demandMeta input inside message) >>= next)
      funext selected
      cases selected with
      | none => exact interpret_pure _ _
      | some selected =>
        rcases selected with ⟨bytes, protectedInput⟩
        cases protectedInput
        · exact interpret_pure _ _
        · simp only [ite_true]
          funext before
          simp only [interpret, StateT.run_map, StateT.run_lift, simulateQ_map,
            simulateQ_spec_query, sourceInterpreter, bind_pure_comp, Functor.map_map]
          simp only [map_apply, cacheLens, LazyOracleDiscard.StateLens.snd,
            LazyOracleDiscard.StateLens.query, StateT.run, Functor.map_map, Prod.map, id_eq]

/-- The concrete source key service and the PRK-free client agree through arbitrary adaptive commands, retaining preparation/demand metadata and the private PRK cache. -/
theorem program_source {Result : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp RegistrationNativeKeyPhases.Spec Result) :
    interpret (sourceInterpreter source hmac) (simulateQ (compiler source input inside) work) =
      simulateQ (erased source hmac input inside) work := by
  induction work using OracleComp.inductionOn with
  | pure result => simpa only [simulateQ_pure] using interpret_pure (sourceInterpreter source hmac) result
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, interpret_bind, query_source]
    apply congrArg (fun continuation => erased source hmac input inside query >>= continuation)
    funext reply
    exact ih reply

end BeaconcryptCore.Computational.RegistrationNativeKeyCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyCompiler.interpret_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyCompiler.interpret_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyCompiler.interpret_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyCompiler.interpret_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyCompiler.liftProb_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyCompiler.liftProb_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyCompiler.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyCompiler.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyCompiler.program_source
