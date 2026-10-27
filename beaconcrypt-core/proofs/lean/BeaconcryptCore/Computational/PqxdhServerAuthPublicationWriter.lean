import BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory

/-! Literal outer serialization and Server publication retain the complete optional component result and the actual callback trace. No writer totality is assumed. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter
open PqxdhJointKdfGame
open PqxdhServerAuthExperiment (Codec Checks)
open PqxdhServerAuthPublicationTrace (Compiler Event Trace)
open PqxdhServerRegistrationPublication (AuxSpec Response responseFields firstContext)
open PqxdhServerAuthCtxCalls (Kernel Residual)
variable {Reader WireResponse Metadata PeerMetadata Consumed : Type}

noncomputable def aux (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader WireResponse) (checks : Checks) : QueryImpl AuxSpec Compiler :=
  fun query => PqxdhServerAuthPublicationTrace.compiler source codec checks (.inr query)

/-- The actual erasure callback changes neither the prior successful-seal log nor the private callback trace. -/
theorem erase_run (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (bytes : Pqxdh.Bytes) (before : PqxdhServerAuthPublicationTrace.State) :
    (aux source codec checks (.erase bytes)).run.run before = pure (some (), before) := by
  simp [aux, PqxdhServerAuthPublicationTrace.compiler, PqxdhServerAuthPublicationTrace.observe,
    PqxdhServerAuthPublicationTrace.observation, PqxdhServerAuthBuildProgram.compiler,
    PqxdhServerAuthBuildProgram.impl, PqxdhServerAuthCtxNative.aux, StateT.run]
  rfl

/-- Every actual send result, including component refusal and native rejection, is retained before the optional response writer. Only its literal successful reply installs the advanced kernel. -/
theorem after_run {K : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader WireResponse) (checks : Checks)
    (calls : RawCtxChainOwner.Calls K Compiler) (candidate : pqxdh.ServerRegistrationCandidate)
    (authenticated : Pqxdh.Bytes) (kernel : K) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)
    (before : PqxdhServerAuthPublicationTrace.State) :
    (PqxdhInitialGenericPublication.afterInitialization calls (aux source codec checks)
      candidate authenticated kernel metadata state).run.run before = (do
      let (sent, afterSend) ← (calls.send kernel (firstContext candidate authenticated)).run.run before
      match sent with
      | none => pure (none, afterSend)
      | some (advanced, encrypted) =>
        match encrypted with
        | none => pure (some (none, state), afterSend)
        | some encrypted => do
          let fields := responseFields candidate encrypted
          let written := codec.write2 fields
          pure (some (written.map (fun bytes => ⟨bytes, candidate.key_id⟩),
            if written.isSome then PqxdhInitialGenericPublication.publish state candidate advanced metadata else state),
            (afterSend.1, afterSend.2 ++ [.write fields (some written)]))) := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, OptionT.run_bind,
    Option.elimM, StateT.run_bind]
  refine bind_congr fun ⟨sent, afterSend⟩ => ?_
  cases sent with
  | none => rfl
  | some sent =>
      rcases sent with ⟨advanced, encrypted⟩
      simp only [Option.elim_some, StateT.run_bind]
      have erased := erase_run source codec checks authenticated afterSend
      simp only [StateT.run] at erased
      simp only [StateT.run, erased, pure_bind, Option.elim_some]
      cases encrypted with
      | none => rfl
      | some encrypted =>
          have written := PqxdhServerAuthPublicationTrace.write_run source codec checks
            (responseFields candidate encrypted) afterSend
          simp only [StateT.run] at written
          simp only [OptionT.run_bind, Option.elimM, aux]
          change (StateT.run (_ >>= _) afterSend) = _
          rw [StateT.run_bind]
          simp only [StateT.run, written, pure_bind]
          cases codec.write2 (responseFields candidate encrypted) <;> rfl

/-- Retain only actual outer serialization callbacks, including their optional replies. -/
def writes (trace : Trace) : List (PqxdhServerRegistrationPublication.ResponseFields × Option (Option Pqxdh.Bytes)) :=
  trace.filterMap fun event => match event with
    | .seal _ _ => none
    | .write fields reply => some (fields, reply)

noncomputable def calls (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) : RawCtxChainOwner.Calls Kernel Compiler :=
  PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest
    (fun pending => PqxdhServerAuthPublicationTrace.compiler source codec checks (.inl pending))

/-- The actual send driver executes no outer response writer, for every starting kernel and optional component reply. -/
theorem send_writes (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (kernel : Kernel) (context : RawCtxSourceSend.SealContext)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (result : Option (Kernel × Option RawCtxSourceSend.Encrypted))
    (supported : (result, after) ∈ support (((calls source codec checks rest).send kernel context).run.run before)) :
    writes after.2 = writes before.2 := by
  unfold calls PqxdhServerAuthCtxBuildSettlement.calls RawCtxChainSend.execute at supported
  cases begun : RawCtxChainSend.normalBegin kernel context with
  | exhausted previous actual =>
      simp only [begun, RawCtxChainSend.program, simulateQ_pure, OptionT.run_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      exact congrArg (fun outcome => writes outcome.2.2) supported
  | requested pending =>
      simp only [begun, RawCtxChainSend.program, simulateQ_bind, simulateQ_spec_query,
        PqxdhServerAuthCtxBuildSettlement.labels, pure_bind,
        bind_pure_comp, simulateQ_map, OptionT.run_map, StateT.run_map] at supported
      rw [PqxdhServerAuthPublicationTrace.seal_run, Functor.map_map, support_map] at supported
      obtain ⟨reply, _, same⟩ := supported
      have traceSame := congrArg (fun outcome => outcome.2.2) same
      simp only at traceSame
      rw [← traceSame]
      simp [writes]

/-- Native optional failure retains the complete old Server state; explicit component and diagnostic failures remain separate. -/
def Unpublished {S : Type} (state : S) :
    Option (RustM (Option Response × S)) → Prop
  | some (.ok (reply, after)) => reply = none ∧ after = state
  | _ => True

/-- The actual trace has no outer write, or exactly its reached writer reply followed by the source's optional publication. This is a source-control relation, not a security assumption. -/
def Shape {K : Type} (codec : Codec Reader WireResponse) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (result : Option (RustM (Option Response × PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed))) : Prop :=
  (writes after.2 = writes before.2 ∧ Unpublished state result) ∨
    ∃ (candidate : pqxdh.ServerRegistrationCandidate) (advanced : K) (encrypted : RawCtxSourceSend.Encrypted),
      let fields := responseFields candidate encrypted
      let written := codec.write2 fields
      writes after.2 = writes before.2 ++ [(fields, some written)] ∧
      result = some (.ok (written.map (fun bytes => ⟨bytes, candidate.key_id⟩),
        if written.isSome then PqxdhInitialGenericPublication.publish state candidate advanced metadata else state))

/-- The complete actual first-send tail derives its serialization/publication relation from its supported execution, retaining all optional failures. -/
theorem after_shape (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (candidate : pqxdh.ServerRegistrationCandidate)
    (authenticated : Pqxdh.Bytes) (kernel : Kernel) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (result : Option (Option Response × PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed))
    (supported : (result, after) ∈ support ((PqxdhInitialGenericPublication.afterInitialization
      (calls source codec checks rest) (aux source codec checks)
      candidate authenticated kernel metadata state).run.run before)) :
    Shape codec metadata state before after (RustM.ok <$> result) := by
  rw [after_run, mem_support_bind_iff] at supported
  obtain ⟨⟨sent, afterSend⟩, reached, supported⟩ := supported
  have retained := send_writes source codec checks rest kernel
    (firstContext candidate authenticated) before afterSend sent reached
  cases sent with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl ⟨retained, trivial⟩
  | some sent =>
      rcases sent with ⟨advanced, encrypted⟩
      cases encrypted with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact Or.inl ⟨retained, rfl, rfl⟩
      | some encrypted =>
          simp only [support_pure, Set.mem_singleton_iff] at supported
          cases supported
          refine Or.inr ⟨candidate, advanced, encrypted, ?_, rfl⟩
          simp only [writes, List.filterMap_append, List.filterMap_cons,
            List.filterMap_nil, List.append_left_inj]
          exact retained

/-- Literal pure auxiliary replies, including failed allocation and writer replies. -/
def auxValue (codec : Codec Reader WireResponse) (checks : Checks) : (query : AuxSpec.Domain) → AuxSpec.Range query
  | .checkIdentity identity => checks.beaconIdentity identity
  | .reservePeer => checks.reservePeer
  | .reservePlaintext length => checks.reservePlaintext length
  | .erase _ => ()
  | .write fields => codec.write2 fields

/-- Actual auxiliary execution records a write exactly for the writer callback and retains every other state field. -/
theorem aux_run (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (query : AuxSpec.Domain) (before : PqxdhServerAuthPublicationTrace.State) :
    (aux source codec checks query).run.run before = pure (some (auxValue codec checks query),
      (before.1, PqxdhServerAuthPublicationTrace.record (.inr query) (some (auxValue codec checks query)) before.2)) := by
  cases query <;> simp [aux, auxValue, PqxdhServerAuthPublicationTrace.compiler,
    PqxdhServerAuthPublicationTrace.observe, PqxdhServerAuthPublicationTrace.record,
    PqxdhServerAuthPublicationTrace.observation, PqxdhServerAuthBuildProgram.compiler,
    PqxdhServerAuthBuildProgram.impl, PqxdhServerAuthCtxNative.aux, StateT.run] <;> rfl

/-- Every actual non-writer auxiliary callback is pure in the complete traced compiler state. -/
theorem aux_quiet (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (query : AuxSpec.Domain)
    (quiet : ∀ fields, query ≠ .write fields) :
    aux source codec checks query = pure (auxValue codec checks query) := by
  apply OptionT.ext
  funext before
  have run := aux_run source codec checks query before
  simp only [StateT.run] at run
  rw [run]
  cases query <;> simp_all [PqxdhServerAuthPublicationTrace.record,
    PqxdhServerAuthPublicationTrace.observation] <;> rfl

/-- Every actual candidate gate precedes the same complete serialization/publication relation. Rejection and diagnostics cannot fabricate writer observations. -/
theorem candidate_shape (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (initial : RustM Kernel)
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (result : Option (RustM (Option Response × PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)))
    (supported : (result, after) ∈ support ((PqxdhInitialGenericBuilder.candidate
      (calls source codec checks rest) (aux source codec checks)
      initial candidate data metadata state).run.run before)) :
    Shape codec metadata state before after result := by
  simp only [PqxdhInitialGenericBuilder.candidate] at supported
  rw [aux_quiet source codec checks (.checkIdentity _) (by intros; simp)] at supported
  simp only [auxValue, pure_bind] at supported
  cases identity : checks.beaconIdentity candidate.beacon_identity_public_key
  · simp only [identity, Bool.not_false, ite_true, OptionT.run_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · simp only [identity, Bool.not_true, Bool.false_eq_true, ite_false] at supported
    rw [aux_quiet source codec checks .reservePeer (by intros; simp)] at supported
    simp only [auxValue, pure_bind] at supported
    cases reserved : checks.reservePeer
    · simp only [reserved, Bool.not_false, ite_true, OptionT.run_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · simp only [reserved, Bool.not_true, Bool.false_eq_true, ite_false] at supported
      cases initial with
      | fail error =>
          simp only [PqxdhInitialGenericBuilder.continueRust, OptionT.run_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact Or.inl ⟨rfl, trivial⟩
      | div =>
          simp only [PqxdhInitialGenericBuilder.continueRust, OptionT.run_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact Or.inl ⟨rfl, trivial⟩
      | ok kernel =>
          simp only [PqxdhInitialGenericBuilder.continueRust] at supported
          by_cases empty : (data.getD PqxdhServerRegistrationPublication.registrationWitness).isEmpty = true
          · simp only [empty, ite_true, OptionT.run_pure, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at supported
            cases supported
            exact Or.inl ⟨rfl, rfl, rfl⟩
          · simp only [empty, Bool.false_eq_true, ite_false] at supported
            by_cases fits : 8 + (data.getD PqxdhServerRegistrationPublication.registrationWitness).length ≤ Usize.max
            · simp only [fits, ite_true] at supported
              rw [aux_quiet source codec checks (.reservePlaintext _) (by intros; simp)] at supported
              simp only [auxValue, pure_bind] at supported
              cases allocated : checks.reservePlaintext (8 + (data.getD PqxdhServerRegistrationPublication.registrationWitness).length)
              · simp only [allocated, Bool.not_false, ite_true, OptionT.run_pure,
                  StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
                cases supported
                exact Or.inl ⟨rfl, rfl, rfl⟩
              · simp only [allocated, Bool.not_true, Bool.false_eq_true, ite_false] at supported
                cases binding : candidate.key_id_binding with
                | fail error =>
                    simp only [binding, OptionT.run_pure, StateT.run_pure,
                      support_pure, Set.mem_singleton_iff] at supported
                    cases supported
                    exact Or.inl ⟨rfl, trivial⟩
                | div =>
                    simp only [binding, OptionT.run_pure, StateT.run_pure,
                      support_pure, Set.mem_singleton_iff] at supported
                    cases supported
                    exact Or.inl ⟨rfl, trivial⟩
                | ok binding =>
                    simp only [binding, OptionT.run_map, StateT.run_map, support_map] at supported
                    obtain ⟨⟨reply, stateAfter⟩, reached, same⟩ := supported
                    cases same
                    exact after_shape source codec checks rest candidate _ kernel metadata state before stateAfter reply reached
            · simp only [fits, ite_false, OptionT.run_pure, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at supported
              cases supported
              exact Or.inl ⟨rfl, rfl, rfl⟩

/-- Actual next-ID allocation, pending binding and peer availability retain the same writer/publication relation. -/
theorem build_shape (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (initial : RustM Kernel)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (result : Option (RustM (Option Response × PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)))
    (supported : (result, after) ∈ support ((PqxdhServerAuthSendFactor.genericBuild
      (calls source codec checks rest) (aux source codec checks)
      initial pending data metadata state).run.run before)) :
    Shape codec metadata state before after result := by
  unfold PqxdhServerAuthSendFactor.genericBuild at supported
  cases next : pqxdh.server_next_key_id state.control with
  | fail error =>
      simp only [next, PqxdhInitialGenericBuilder.continueRust, OptionT.run_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl ⟨rfl, trivial⟩
  | div =>
      simp only [next, PqxdhInitialGenericBuilder.continueRust, OptionT.run_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl ⟨rfl, trivial⟩
  | ok value =>
      cases value with
      | Err error =>
          simp only [next, PqxdhInitialGenericBuilder.continueRust, OptionT.run_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact Or.inl ⟨rfl, rfl, rfl⟩
      | Ok key =>
          simp only [next, PqxdhInitialGenericBuilder.continueRust] at supported
          cases prepared : pqxdh.server_prepare_commit state.control pending
            ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then .Occupied else .Available) with
          | fail error =>
              simp only [prepared, OptionT.run_pure, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at supported
              cases supported
              exact Or.inl ⟨rfl, trivial⟩
          | div =>
              simp only [prepared, OptionT.run_pure, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at supported
              cases supported
              exact Or.inl ⟨rfl, trivial⟩
          | ok value =>
              cases value with
              | Err error =>
                  simp only [prepared, OptionT.run_pure, StateT.run_pure,
                    support_pure, Set.mem_singleton_iff] at supported
                  cases supported
                  exact Or.inl ⟨rfl, rfl, rfl⟩
              | Ok candidate =>
                  simp only [prepared] at supported
                  exact candidate_shape source codec checks rest initial candidate data metadata state before after result supported

/-- Projecting private kernel representation preserves the complete native optional rejection condition. -/
theorem unpublished_map {S T : Type} (f : S → T) (state : S)
    (result : Option (RustM (Option Response × S))) (quiet : Unpublished state result) :
    Unpublished (f state) ((fun reply => Prod.map id f <$> reply) <$> result) := by
  cases result with
  | none => trivial
  | some result =>
      cases result with
      | fail error => trivial
      | div => trivial
      | ok reply =>
          rcases reply with ⟨response, after⟩
          exact ⟨quiet.1, congrArg f quiet.2⟩

/-- The complete native source state follows the actual observed writer result. -/
def NativeShape (codec : Codec Reader WireResponse) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (result : Option (RustM (Option Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed))) : Prop :=
  (writes after.2 = writes before.2 ∧ Unpublished state result) ∨
    ∃ (candidate : pqxdh.ServerRegistrationCandidate) (advanced : ratchet.concrete.ConcreteRatchetKernel)
      (encrypted : RawCtxSourceSend.Encrypted),
      let fields := responseFields candidate encrypted
      let written := codec.write2 fields
      writes after.2 = writes before.2 ++ [(fields, some written)] ∧
      result = some (.ok (written.map (fun bytes => ⟨bytes, candidate.key_id⟩),
        if written.isSome then PqxdhServerRegistrationPublication.publish state candidate advanced metadata else state))

/-- The actual full-state native projection preserves each writer receipt and its optional publication. -/
theorem shape_native {K : Type} (interpret : K → ratchet.concrete.ConcreteRatchetKernel)
    (codec : Codec Reader WireResponse) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (result : Option (RustM (Option Response × PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)))
    (shape : Shape codec metadata state before after result) :
    NativeShape codec metadata (PqxdhInitialGenericPublication.native interpret state) before after
      ((fun reply => Prod.map id (PqxdhInitialGenericPublication.native interpret) <$> reply) <$> result) := by
  rcases shape with ⟨same, quiet⟩ | ⟨candidate, advanced, encrypted, same, returned⟩
  · exact Or.inl ⟨same, unpublished_map _ state result quiet⟩
  · refine Or.inr ⟨candidate, interpret advanced, encrypted, same, ?_⟩
    rw [returned]
    cases written : codec.write2 (responseFields candidate encrypted) <;>
      simp [RawCtxMaterialInterpretation.rust_map_ok, PqxdhInitialGenericPublication.publish_native]

/-- The literal observed compiler preserves all native fields and derives its optional publication solely from the reached actual outer writer. -/
theorem compiled_shape (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (result : Option (RustM (Option Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)))
    (supported : (result, after) ∈ support
      ((PqxdhServerAuthPublicationTrace.compiled source codec checks rest pending data metadata state).run.run before)) :
    NativeShape codec metadata state before after result := by
  have handler : PqxdhServerAuthPublicationTrace.compiler source codec checks =
      PqxdhServerAuthBuildProgram.impl
        (fun pending => PqxdhServerAuthPublicationTrace.compiler source codec checks (.inl pending))
        (aux source codec checks) := by
    funext query
    cases query <;> rfl
  rw [PqxdhServerAuthPublicationTrace.compiled, handler,
    PqxdhServerAuthBuildProgram.program_interpret] at supported
  simp only [OptionT.run_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨original, originalAfter⟩, reached, same⟩ := supported
  cases same
  have shape := build_shape source codec checks rest (PqxdhServerAuthCtxCalls.initial false rest.2.2)
    pending data metadata (PqxdhServerAuthCtxBuildSettlement.embed state) before originalAfter original reached
  have native := shape_native PqxdhServerAuthCtxBuildSettlement.resolve codec metadata _ before originalAfter original shape
  have collapse : PqxdhInitialGenericPublication.native PqxdhServerAuthCtxBuildSettlement.resolve
      (PqxdhServerAuthCtxBuildSettlement.embed state) = state :=
    PqxdhServerAuthCtxBuildSettlement.native_embed _ state
  rw [collapse] at native
  exact native

/-- A successful native response occurs exactly when the newly reached outer writer returned bytes. This compares actual callback occurrences, not decoded aliases or old trace membership. -/
theorem shape_publication_iff (codec : Codec Reader WireResponse) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (result : Option (RustM (Option Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)))
    (shape : NativeShape codec metadata state before after result) :
    (∃ response published, result = some (.ok (some response, published))) ↔
      ∃ fields bytes, writes after.2 = writes before.2 ++ [(fields, some (some bytes))] := by
  rcases shape with ⟨same, quiet⟩ | ⟨candidate, advanced, encrypted, same, returned⟩
  · constructor
    · rintro ⟨response, published, equality⟩
      rw [equality] at quiet
      have impossible : (some response : Option Response) = none := quiet.1
      cases impossible
    · rintro ⟨fields, bytes, equality⟩
      rw [same] at equality
      have impossible := congrArg List.length equality
      simp only [List.length_append, List.length_singleton] at impossible
      omega
  · cases written : codec.write2 (responseFields candidate encrypted) with
    | none =>
        simp only [written, Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false] at returned same
        constructor
        · rintro ⟨response, published, equality⟩
          rw [returned] at equality
          cases equality
        · rintro ⟨fields, bytes, equality⟩
          rw [same] at equality
          have impossible := List.append_cancel_left equality
          cases impossible
    | some bytes =>
        simp only [written, Option.map_some, Option.isSome_some, ite_true] at returned same
        exact ⟨fun _ => ⟨responseFields candidate encrypted, bytes, same⟩,
          fun _ => ⟨⟨bytes, candidate.key_id⟩,
            PqxdhServerRegistrationPublication.publish state candidate advanced metadata, returned⟩⟩

/-- The complete actual compiler supplies both directions of writer-success versus successful native response, with no caller-supplied source trace premise. -/
theorem compiled_publication_iff (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (result : Option (RustM (Option Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)))
    (supported : (result, after) ∈ support
      ((PqxdhServerAuthPublicationTrace.compiled source codec checks rest pending data metadata state).run.run before)) :
    (∃ response published, result = some (.ok (some response, published))) ↔
      ∃ fields bytes, writes after.2 = writes before.2 ++ [(fields, some (some bytes))] :=
  shape_publication_iff codec metadata state before after result
    (compiled_shape source codec checks rest pending data metadata state before after result supported)

/-- Actual successful publication retains the precise response bytes, assigned ID, writer arguments and advanced peer installation. -/
theorem compiled_success (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state published : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State) (response : Response)
    (supported : (some (.ok (some response, published)), after) ∈ support
      ((PqxdhServerAuthPublicationTrace.compiled source codec checks rest pending data metadata state).run.run before)) :
    ∃ (candidate : pqxdh.ServerRegistrationCandidate) (advanced : ratchet.concrete.ConcreteRatchetKernel)
      (encrypted : RawCtxSourceSend.Encrypted),
      codec.write2 (responseFields candidate encrypted) = some response.serialized ∧
      response.keyId = candidate.key_id ∧
      published = PqxdhServerRegistrationPublication.publish state candidate advanced metadata ∧
      writes after.2 = writes before.2 ++ [(responseFields candidate encrypted, some (some response.serialized))] := by
  rcases compiled_shape source codec checks rest pending data metadata state before after _ supported with
    ⟨_, quiet⟩ | ⟨candidate, advanced, encrypted, same, returned⟩
  · have impossible : (some response : Option Response) = none := quiet.1
    cases impossible
  · cases written : codec.write2 (responseFields candidate encrypted) with
    | none => simp [written] at returned
    | some bytes =>
        simp only [written, Option.map_some, Option.isSome_some, ite_true, Option.some.injEq,
          RustM.ok.injEq, Prod.mk.injEq] at returned
        rcases returned with ⟨responseSame, publishedSame⟩
        subst response
        exact ⟨candidate, advanced, encrypted, written, rfl, publishedSame, by simpa only [written] using same⟩

/-- Every native optional rejection leaves the original complete Server state intact, including an inner or outer writer failure. Component/cache effects and private receipts remain in the retained execution. -/
theorem compiled_rejection (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state rejected : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (before after : PqxdhServerAuthPublicationTrace.State)
    (supported : (some (.ok (none, rejected)), after) ∈ support
      ((PqxdhServerAuthPublicationTrace.compiled source codec checks rest pending data metadata state).run.run before)) :
    rejected = state := by
  rcases compiled_shape source codec checks rest pending data metadata state before after _ supported with
    ⟨_, quiet⟩ | ⟨candidate, advanced, encrypted, _, returned⟩
  · exact quiet.2
  · cases written : codec.write2 (responseFields candidate encrypted) with
    | none =>
        simpa only [written, Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false,
          Option.some.injEq, RustM.ok.injEq, Prod.mk.injEq, true_and] using returned
    | some bytes => simp [written] at returned

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.erase_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.erase_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.after_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.after_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.send_writes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.send_writes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.after_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.after_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.aux_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.aux_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.aux_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.aux_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.candidate_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.candidate_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.build_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.build_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.unpublished_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.unpublished_map
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.shape_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.shape_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.compiled_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.compiled_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.shape_publication_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.shape_publication_iff
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.compiled_publication_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.compiled_publication_iff
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.compiled_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.compiled_success
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.compiled_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter.compiled_rejection
