import BeaconcryptCore.Computational.PqxdhServerAuthBuildMap
import BeaconcryptCore.Computational.PqxdhServerAuthCtxNative

/-! The complete material builder exposes actual sealing and auxiliary calls as an oracle program. Its interpretation retains the entire original continuation, including optional failures, publication and effects. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram
open PqxdhServerRegistrationPublication (AuxSpec Response registrationWitness)
open PqxdhInitialGenericPublication (State)

variable {ι : Type} {spec : OracleSpec ι} {K Metadata PeerMetadata Consumed : Type}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def interpretCalls (handler : QueryImpl spec m) (calls : RawCtxChainOwner.Calls K (OracleComp spec)) :
    RawCtxChainOwner.Calls K m :=
  ⟨fun entry sequence context => simulateQ handler (calls.receive entry sequence context),
    fun entry context => simulateQ handler (calls.send entry context)⟩

/-- Full first-send, erasure and both optional publication branches commute with their actual oracle interpretation. -/
theorem after_interpret (handler : QueryImpl spec m) (calls : RawCtxChainOwner.Calls K (OracleComp spec))
    (aux : QueryImpl AuxSpec (OracleComp spec)) (candidate : pqxdh.ServerRegistrationCandidate)
    (authenticated : Pqxdh.Bytes) (kernel : K) (metadata : PeerMetadata)
    (state : State K Metadata PeerMetadata Consumed) :
    simulateQ handler (PqxdhInitialGenericPublication.afterInitialization calls aux
      candidate authenticated kernel metadata state) =
      PqxdhInitialGenericPublication.afterInitialization (interpretCalls handler calls) (handler ∘ₛ aux)
        candidate authenticated kernel metadata state := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, interpretCalls,
    simulateQ_bind, QueryImpl.apply_compose]
  refine bind_congr fun ⟨advanced, encrypted⟩ => bind_congr fun _ => ?_
  cases encrypted <;> simp only [simulateQ_pure, simulateQ_bind]
  refine bind_congr fun written => ?_
  cases written <;> simp only [simulateQ_pure]

/-- The original candidate gates and exact binding prefix commute with oracle interpretation, including every rejected or diagnostic branch. -/
theorem candidate_interpret (handler : QueryImpl spec m) (calls : RawCtxChainOwner.Calls K (OracleComp spec))
    (aux : QueryImpl AuxSpec (OracleComp spec)) (initial : RustM K)
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : State K Metadata PeerMetadata Consumed) :
    simulateQ handler (PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state) =
      PqxdhInitialGenericBuilder.candidate (interpretCalls handler calls) (handler ∘ₛ aux)
        initial candidate data metadata state := by
  simp only [PqxdhInitialGenericBuilder.candidate, simulateQ_bind, QueryImpl.apply_compose]
  refine bind_congr fun valid => ?_
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    simulateQ_pure, simulateQ_bind]
  refine bind_congr fun reserved => ?_
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    simulateQ_pure]
  cases initial <;> simp only [PqxdhInitialGenericBuilder.continueRust, simulateQ_pure]
  case true.true.ok kernel =>
    by_cases empty : (data.getD registrationWitness).isEmpty = true
    all_goals simp only [empty, Bool.false_eq_true, ite_true, ite_false, simulateQ_pure]
    by_cases fits : 8 + (data.getD registrationWitness).length ≤ Usize.max
    all_goals simp only [fits, ite_true, ite_false, simulateQ_bind, simulateQ_pure]
    refine bind_congr fun allocated => ?_
    cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
      simulateQ_pure]
    cases candidate.key_id_binding <;> simp only [simulateQ_pure, simulateQ_map, after_interpret]

/-- Actual next-ID allocation and pending-token Server-binding admission retain their complete optional result and peer publication under oracle interpretation. -/
theorem build_interpret (handler : QueryImpl spec m) (calls : RawCtxChainOwner.Calls K (OracleComp spec))
    (aux : QueryImpl AuxSpec (OracleComp spec)) (initial : RustM K)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : State K Metadata PeerMetadata Consumed) :
    simulateQ handler (PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata state) =
      PqxdhServerAuthSendFactor.genericBuild (interpretCalls handler calls) (handler ∘ₛ aux)
        initial pending data metadata state := by
  unfold PqxdhServerAuthSendFactor.genericBuild
  cases next : pqxdh.server_next_key_id state.control <;>
    simp only [PqxdhInitialGenericBuilder.continueRust, simulateQ_pure]
  case ok value =>
    cases value <;> simp only [simulateQ_pure]
    rename_i key
    cases prepared : pqxdh.server_prepare_commit state.control pending
        ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers key).isSome then .Occupied else .Available) <;>
      simp only [simulateQ_pure]
    case ok value =>
      cases value <;> simp only [simulateQ_pure, candidate_interpret]

open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthCtxCalls (Kernel Residual)

abbrev Spec := (PqxdhServerAuthCtxSend.Pending →ₒ Option RawCtxSourceSend.Encrypted) + AuxSpec

noncomputable def impl (sealer : PqxdhServerAuthCtxSend.Pending → m (Option RawCtxSourceSend.Encrypted))
    (aux : QueryImpl AuxSpec m) : QueryImpl Spec m
  | .inl pending => sealer pending
  | .inr query => aux query

def sealQuery (pending : PqxdhServerAuthCtxSend.Pending) : OracleComp Spec (Option RawCtxSourceSend.Encrypted) :=
  Spec.query (.inl pending)

def auxQuery : QueryImpl AuxSpec (OracleComp Spec) := fun query => Spec.query (.inr query)

/-- The concrete send-query interpreter performs the exact material driver; its only external operation is the reached sealing request. -/
theorem calls_interpret (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (sealer : PqxdhServerAuthCtxSend.Pending → m (Option RawCtxSourceSend.Encrypted))
    (aux : QueryImpl AuxSpec m) :
    interpretCalls (impl sealer aux)
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealQuery) =
      PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealer := by
  unfold interpretCalls PqxdhServerAuthCtxBuildSettlement.calls
  congr 1
  funext entry context
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  cases query <;> simp only [QueryImpl.apply_compose, PqxdhServerAuthCtxBuildSettlement.labels,
    simulateQ_pure, sealQuery, simulateQ_spec_query, impl]

/-- The material-marker builder exposes only its actual sealing and original auxiliary callbacks. Its final native projection uses the proved known material image. -/
noncomputable def program (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    OracleComp Spec
      (RustM (Option Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)) :=
  Functor.map (Prod.map id (PqxdhInitialGenericPublication.native PqxdhServerAuthCtxBuildSettlement.resolve)) <$>
    PqxdhServerAuthSendFactor.genericBuild
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealQuery)
      auxQuery (PqxdhServerAuthCtxCalls.initial false rest.2.2) pending data metadata
      (PqxdhServerAuthCtxBuildSettlement.embed state)

/-- The complete concrete oracle program interprets to the actual builder for every full sealer and auxiliary monad, including explicit stop and stateful logging. -/
theorem program_interpret (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (sealer : PqxdhServerAuthCtxSend.Pending → m (Option RawCtxSourceSend.Encrypted))
    (aux : QueryImpl AuxSpec m)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    simulateQ (impl sealer aux) (program source rest pending data metadata state) =
      Functor.map (Prod.map id (PqxdhInitialGenericPublication.native PqxdhServerAuthCtxBuildSettlement.resolve)) <$>
        PqxdhServerAuthSendFactor.genericBuild
          (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealer)
          aux (PqxdhServerAuthCtxCalls.initial false rest.2.2) pending data metadata
          (PqxdhServerAuthCtxBuildSettlement.embed state) := by
  have same : impl sealer aux ∘ₛ auxQuery = aux := by
    funext query
    simp only [QueryImpl.apply_compose, auxQuery, simulateQ_spec_query, impl]
  simp only [program, simulateQ_map, build_interpret, calls_interpret, same]

/-- The actual complete factor builder is this concrete service program with the original mathematical sealer and auxiliary callbacks. No callback correspondence hypothesis remains. -/
theorem program_factor (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (aux : QueryImpl AuxSpec m) (key : RootOutput) (rest : Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None)) prim source aux
        (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest)) pending data metadata state =
      simulateQ (impl (PqxdhServerAuthBuildMap.materialSealer prim key) aux)
        (program source rest pending data metadata state) := by
  rw [PqxdhServerAuthBuildMap.material_build, program_interpret]
  rfl

abbrev Log := List RawCtxSourceSend.SealContext
abbrev Compiler := OptionT (PqxdhServerAuthCtxNative.Local Log)

/-- The executable sealer propagates the ordinary component's explicit nonce stop. It appends the actual context only for a successful inner writer reply. It requires no selected-key argument. -/
noncomputable def sealer (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhServerAuthCtxSend.Pending) : Compiler (Option RawCtxSourceSend.Encrypted) := do
  let sealed ← OptionT.mk (StateT.lift
    (RawCtxSelectedSealConsumer.sealing source.crypto writer (PqxdhServerAuthCtxSend.sealing pending)))
  if sealed.isSome then modify fun log => log ++ [pending.context]
  pure sealed

variable {Reader WireResponse : Type}
open PqxdhServerAuthExperiment (Codec Checks)

/-- Actual auxiliary outcomes remain unchanged, including allocation, identity and response-writer failures. -/
noncomputable def compiler (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) : QueryImpl Spec Compiler :=
  impl (sealer source codec.frameWrite) (fun query => OptionT.lift (PqxdhServerAuthCtxNative.aux codec checks query))

/-- The complete executable builder keeps component refusal outside every native optional/diagnostic result and preserves the full successful-seal log. -/
noncomputable def compiled (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :=
  simulateQ (compiler source codec checks) (program source rest pending data metadata state)

/-- The executable log update is determined by the actual nested optional reply; explicit component refusal and native writer failure both retain the old log. -/
theorem sealer_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhServerAuthCtxSend.Pending) (before : Log) :
    (sealer source writer pending).run.run before =
      (fun result => (result, match result with
        | some (some _) => before ++ [pending.context]
        | _ => before)) <$>
        RawCtxSelectedSealConsumer.sealing source.crypto writer (PqxdhServerAuthCtxSend.sealing pending) := by
  simp only [sealer, OptionT.run_bind, OptionT.run_mk, Option.elimM, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun result => ?_
  cases result with
  | none => rfl
  | some encrypted => cases encrypted <;> rfl

noncomputable def sourceSealer (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (pending : PqxdhServerAuthCtxSend.Pending) :
    StateT (RawCtxSharedPrimitive.SharedState Log) ProbComp (Option RawCtxSourceSend.Encrypted) := do
  let sealed ← PqxdhServerAuthCtxSend.sourceSealing source writer key pending
  if sealed.isSome then modify fun state => (state.1 ++ [pending.context], state.2)
  pure sealed

/-- The complete mathematical callback keeps the actual post-seal cache and changes only its source log after successful frame writing. -/
theorem sourceSealer_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (pending : PqxdhServerAuthCtxSend.Pending)
    (state : RawCtxSharedPrimitive.SharedState Log) :
    (sourceSealer source writer key pending).run state =
      (fun result => (result.1, (if result.1.isSome then result.2.1 ++ [pending.context] else result.2.1, result.2.2))) <$>
        (PqxdhServerAuthCtxSend.sourceSealing source writer key pending).run state := by
  simp only [sourceSealer, StateT.run_bind]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun ⟨encrypted, after⟩ => ?_
  cases encrypted <;> rfl

/-- Before explicit selected-nonce refusal, the executable callback preserves the full original seal log, actual optional writer result and shared cache. The local nonce condition remains an obligation for the stopped scheduler's one-seal proof. -/
theorem sealer_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (pending : PqxdhServerAuthCtxSend.Pending)
    (state : RawCtxSelectedReceiveCompiler.State Log)
    (fresh : ∀ nonce, pending.material = .hidden nonce → pending.context.associatedData.length = 153 →
      nonce ∉ state.2.selected.1.usedNonces) :
    (fun result => (some result.1, result.2)) <$>
        (sourceSealer source writer key pending).run (RawCtxSelectedReceiveCompiler.project state) =
      Prod.map id RawCtxSelectedReceiveCompiler.project <$>
        (PqxdhServerAuthCtxNative.evaluate source key read (sealer source writer pending).run).run state := by
  let post : Option (Option RawCtxSourceSend.Encrypted) × RawCtxSharedPrimitive.SharedState Log →
      Option (Option RawCtxSourceSend.Encrypted) × RawCtxSharedPrimitive.SharedState Log :=
    fun result => (result.1, ((match result.1 with
      | some (some _) => result.2.1 ++ [pending.context]
      | _ => result.2.1), result.2.2))
  have same := congrArg (Functor.map post)
    (PqxdhServerAuthCtxSend.sealing_project source writer key read pending state fresh)
  rw [sourceSealer_run]
  simp only [Functor.map_map] at same ⊢
  have postSome : (fun a : Option RawCtxSourceSend.Encrypted × RawCtxSharedPrimitive.SharedState Log =>
      post (some a.1, a.2)) = (fun a =>
        (some a.1, (if a.1.isSome then a.2.1 ++ [pending.context] else a.2.1, a.2.2))) := by
    funext result
    cases result.1 <;> rfl
  rw [← postSome, same]
  simp only [StateT.run, RawCtxSelectedReceiveCompiler.evaluated, PqxdhServerAuthCtxNative.evaluate,
    PqxdhSelectedStateInterpreter.evaluate,
    Functor.map_map, post, Prod.map_def, RawCtxSelectedReceiveCompiler.project,
    PqxdhSelectedStateInterpreter.pair, id_eq]
  change _ = (fun a => (a.1.1, a.1.2, a.2.cache)) <$>
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      ((sealer source writer pending).run.run state.1)).run state.2
  rw [sealer_run, simulateQ_map, StateT.run_map]
  simp only [Functor.map_map]
  rfl

variable {baseSpec : OracleSpec ι} {KemSK : Type}
open PqxdhServerAuthExperiment (Setup)

/-- The whole original selected factor builder runs this actual service program with the literal source sealer log and unchanged auxiliary callbacks. No source callback simulation premise remains. -/
theorem program_logged (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (key : RootOutput) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None))
        (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source
        (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks)
        (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest)) pending data metadata state =
      simulateQ (impl (sourceSealer setup.source codec.frameWrite key)
        (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks))
        (program setup.source rest pending data metadata state) := by
  have same : PqxdhServerAuthBuildMap.materialSealer
      (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) key =
        sourceSealer setup.source codec.frameWrite key :=
    funext (PqxdhServerAuthBuildMap.material_logged setup codec checks key)
  rw [program_factor, same]

end BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.after_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.after_interpret
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.candidate_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.candidate_interpret
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.build_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.build_interpret
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.calls_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.calls_interpret
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.program_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.program_interpret
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.program_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.program_factor
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.sealer_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.sealer_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.sourceSealer_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.sourceSealer_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.sealer_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.sealer_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.program_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram.program_logged
