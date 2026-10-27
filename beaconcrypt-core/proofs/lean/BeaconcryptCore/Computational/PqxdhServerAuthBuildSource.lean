import BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds

/-! The complete selected first-record builder preserves the literal source result, log and shared cache. Its actual one-seal bound discharges local nonce freshness from an initially unused selected endpoint, including every native failure and publication branch. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthBuildSource
open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthBuildProgram PqxdhServerAuthBuildProgramBounds
open PqxdhServerAuthCtxCalls (Residual)
open PqxdhServerAuthCtxNative (Local evaluate)
open RawCtxSelectedReceiveCompiler (State project)
open PqxdhServerAuthExperiment (Setup Codec Checks)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Interpret the executable optional component computation without collapsing its explicit refusal into a native reply. -/
noncomputable def evaluated (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : Compiler Result) :
    OptionT (StateT (State Log) ProbComp) Result :=
  OptionT.mk (evaluate source key read work.run)

/-- Complete component evaluation preserves every optional continuation and both states. -/
theorem evaluated_bind {Value : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : Compiler Result) (next : Result → Compiler Value) :
    evaluated source key read (work >>= next) =
      (evaluated source key read work >>= fun result => evaluated source key read (next result)) := by
  apply OptionT.ext
  simp only [evaluated, OptionT.run_mk, OptionT.run_bind, Option.elimM, evaluate,
    PqxdhSelectedStateInterpreter.bind_evaluate]
  congr 1
  funext result
  cases result <;> simp only [Option.elim_none, Option.elim_some, PqxdhSelectedStateInterpreter.pure_evaluate]

/-- Evaluation of a pure optional computation keeps the complete local/component state. -/
theorem evaluated_pure (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (value : Result) :
    evaluated source key read (pure value) = pure value := by
  apply OptionT.ext
  simp only [evaluated, OptionT.run_mk, OptionT.run_pure, evaluate, PqxdhSelectedStateInterpreter.pure_evaluate]

/-- The complete executable service program evaluates through the same optional service interpreter, preserving all state and refusals. -/
theorem evaluated_program {κ : Type} {input : OracleSpec κ}
    (source : FixedHkdfSha512NoSaltSource) (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (handler : QueryImpl input Compiler) (work : OracleComp input Result) :
    evaluated source key read (simulateQ handler work) =
      simulateQ (fun query => evaluated source key read (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, evaluated_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, evaluated_bind, ih]

/-- Literal deterministic outcomes of the original auxiliary callbacks. -/
def auxValue (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.AuxSpec.Domain) : PqxdhServerRegistrationPublication.AuxSpec.Range query :=
  match query with
  | .checkIdentity identity => checks.beaconIdentity identity
  | .reservePeer => checks.reservePeer
  | .reservePlaintext length => checks.reservePlaintext length
  | .erase _ => ()
  | .write fields => codec.write2 fields

/-- The actual source auxiliary interpreter is pure and preserves the whole seal log/shared cache. -/
theorem source_aux (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.AuxSpec.Domain) :
    PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks query = pure (auxValue codec checks query) := by
  simp only [PqxdhServerAuthLoggedSendFactor.loggedAux, PqxdhServerAuthExperiment.tailImpl,
    PqxdhServerAuthExperiment.nativeTail, QueryImpl.apply_compose,
    PqxdhServerRegistrationPublication.nativeAdapter, simulateQ_spec_query,
    PqxdhRegistrationProtocolState.registrationImpl]
  cases query <;> rfl

/-- The executable auxiliary branch keeps all component bookkeeping, so it cannot introduce a selected nonce before the sole sealing attempt. -/
theorem evaluated_aux (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response) (checks : Checks)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (query : PqxdhServerRegistrationPublication.AuxSpec.Domain) :
    evaluated source key read (compiler source codec checks (.inr query)) = pure (auxValue codec checks query) := by
  cases query <;> apply OptionT.ext <;>
    simp only [evaluated, compiler, impl, PqxdhServerAuthCtxNative.aux, OptionT.run_mk, OptionT.run_lift,
      pure_bind, OptionT.run_pure, evaluate, PqxdhSelectedStateInterpreter.pure_evaluate, auxValue]

/-- Exact projected optional prefixes compose with every complete continuation. Refusal preserves its reached full state. -/
theorem projected_bind {A B X Y : Type} (projection : B → A)
    (left : StateT A ProbComp X) (right : OptionT (StateT B ProbComp) X)
    (leftNext : X → StateT A ProbComp Y) (rightNext : X → OptionT (StateT B ProbComp) Y)
    (state : B)
    (first : (fun result => (some result.1, result.2)) <$> left.run (projection state) =
      Prod.map id projection <$> right.run.run state)
    (next : ∀ value after,
      (fun result => (some result.1, result.2)) <$> (leftNext value).run (projection after) =
        Prod.map id projection <$> (rightNext value).run.run after) :
    (fun result => (some result.1, result.2)) <$> (left >>= leftNext).run (projection state) =
      Prod.map id projection <$> (right >>= rightNext).run.run state := by
  let continuation : Option X × A → ProbComp (Option Y × A) := fun result =>
    match result.1 with
    | none => pure (none, result.2)
    | some value => (fun output => (some output.1, output.2)) <$> (leftNext value).run result.2
  have same := congrArg (fun work => work >>= continuation) first
  simp only [bind_map_left, continuation] at same
  simp only [StateT.run_bind, map_bind, OptionT.run_bind, Option.elimM]
  rw [same]
  refine bind_congr fun ⟨reply, after⟩ => ?_
  cases reply with
  | none => rfl
  | some value => exact next value after

/-- A complete service program with at most one attempted seal needs only the actual initially empty selected nonce log. Auxiliary calls cannot change that log, and after the sole seal every continuation has zero seal queries. -/
theorem bounded_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (work : OracleComp Spec Result)
    (bound : Nat) (bounded : work.IsQueryBoundP IsSealing bound) (one : bound ≤ 1)
    (state : State Log) (empty : 0 < bound → state.2.selected.1.usedNonces = []) :
    (fun result => (some result.1, result.2)) <$>
        (simulateQ (impl (sourceSealer setup.source codec.frameWrite key)
          (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks)) work).run (project state) =
      Prod.map id project <$>
        (simulateQ (fun query => evaluated setup.source key read
          (compiler setup.source codec checks query)) work).run.run state := by
  induction work using OracleComp.inductionOn generalizing bound state with
  | pure value => rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    cases query with
    | inl pending =>
      simp only [IsSealing, Sum.isLeft_inl, not_true_eq_false, false_or, ite_true] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query]
      apply projected_bind
      · exact sealer_source setup.source codec.frameWrite key read pending state
          (fun nonce _ _ => by rw [empty bounded.1]; simp)
      · intro value after
        exact ih value (bound - 1) (bounded.2 value) (by omega) after (by omega)
    | inr auxiliary =>
      simp only [simulateQ_bind, simulateQ_spec_query, evaluated_aux, impl, source_aux, pure_bind]
      exact ih (auxValue codec checks auxiliary) bound
        (by simpa only [IsSealing, Sum.isLeft_inr, Bool.false_eq_true, ite_false] using
          bounded.2 (auxValue codec checks auxiliary)) one state empty

variable {Metadata PeerMetadata Consumed : Type}

/-- The complete executable selected builder equals the literal source factor builder whenever the selected endpoint has made no prior seal. The actual program's one-seal theorem discharges every reached nonce condition; native failure, source log, cache and complete returned Server state remain unchanged. -/
theorem compiled_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (rest : Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (server : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (state : State Log) (empty : state.2.selected.1.usedNonces = []) :
    (fun result => (some result.1, result.2)) <$>
        (PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None))
          (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source
          (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks)
          (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest))
          pending data metadata server).run (project state) =
      Prod.map id project <$>
        (evaluate setup.source key read
          (compiled setup.source codec checks rest pending data metadata server).run).run state := by
  rw [program_logged]
  have same := bounded_source setup codec checks key read
    (program setup.source rest pending data metadata server) 1
    (program_bound setup.source rest pending data metadata server) (by omega) state (fun _ => empty)
  rw [← evaluated_program] at same
  exact same

end BeaconcryptCore.Computational.PqxdhServerAuthBuildSource

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.evaluated_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.evaluated_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.evaluated_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.evaluated_pure
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.evaluated_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.evaluated_program
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.source_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.source_aux
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.evaluated_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.evaluated_aux
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.projected_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.projected_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.bounded_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.bounded_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.compiled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildSource.compiled_source
