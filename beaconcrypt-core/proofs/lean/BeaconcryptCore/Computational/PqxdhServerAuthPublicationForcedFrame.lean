import BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter

/-! A reference inner writer returns native None after the unchanged sealing work. This is an explicit comparison program, not a changed protocol or an assumed property of the production writer. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame
open CtxRomAuth PqxdhFullSecretInputKdf
open RawCtxSelectedMessageSealing RawCtxSelectedMessageKey

/-- A deterministic reference writer suppresses bytes without invoking any oracle. -/
def writer : RawCtxMixedShared.Writer := fun _ => none

/-- Preserve the selected endpoint's explicit refusal while suppressing the native optional output. -/
def suppress (result : Option (Option RawCtxSourceSend.Encrypted)) : Option (Option RawCtxSourceSend.Encrypted) :=
  result.map fun _ => none

/-- The complete actual local known-key encryption/hash program is unchanged before its purely suppressed writer result. -/
theorem known_mask (crypto : Pqxdh.Crypto) (actual : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) :
    known crypto writer input = (fun _ => none) <$> known crypto actual input := by
  unfold known RawCtxCanonicalSeal.typedSource
  split
  · simp only [simulateQ_bind, simulateQ_pure, map_bind, map_pure, writer]
  · simp only [simulateQ_pure, map_pure]

/-- Selected sealing forwards the identical actual challenge request and retains nonce refusal; only the local native writer result is suppressed. -/
theorem selected_mask (actual : RawCtxMixedShared.Writer) (nonce : NonceOutput)
    (sequence : Std.U64) (context : RawCtxSourceSend.SealContext) :
    selected writer nonce sequence context =
      (fun result => match result with
        | .repeatedNonce => SealResult.repeatedNonce
        | .completed _ => .completed none) <$> selected actual nonce sequence context := by
  unfold selected
  split
  · simp only [map_bind, map_pure]
    refine bind_congr fun reply => ?_
    cases reply <;> rfl
  · rfl

/-- The literal dynamic adapter preserves all known-key work and the exact selected query before the reference suppresses native bytes. -/
theorem call_mask (crypto : Pqxdh.Crypto) (actual : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext) :
    RawCtxSelectedSealConsumer.call crypto writer input =
      (fun result => match result with
        | .repeatedNonce => SealResult.repeatedNonce
        | .completed _ => .completed none) <$> RawCtxSelectedSealConsumer.call crypto actual input := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden nonce =>
      simp only [RawCtxSelectedSealConsumer.call]
      rw [selected_mask actual nonce sequence context, simulateQ_map]
  | known material =>
      simp only [RawCtxSelectedSealConsumer.call]
      rw [known_mask crypto actual ⟨material, sequence, context⟩]
      simp only [simulateQ_map, Functor.map_map]

/-- Suppression commutes with the complete source sealing adapter, including explicit nonce refusal, arbitrary known-key aliases and the original shared hash program. -/
theorem sealing_mask (crypto : Pqxdh.Crypto) (actual : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext) :
    RawCtxSelectedSealConsumer.sealing crypto writer pending =
      suppress <$> RawCtxSelectedSealConsumer.sealing crypto actual pending := by
  simp only [RawCtxSelectedSealConsumer.sealing]
  rw [call_mask crypto actual (RawCtxInterpretedArguments.sealArguments pending)]
  simp only [Functor.map_map]
  congr 1
  funext result
  cases result <;> rfl

/-- The reference sealer retains the old source log and every original component request. It still propagates an actual component refusal. -/
theorem sealer_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (actual : RawCtxMixedShared.Writer) (pending : PqxdhServerAuthCtxSend.Pending)
    (before : PqxdhServerAuthBuildProgram.Log) :
    (PqxdhServerAuthBuildProgram.sealer source writer pending).run.run before =
      (fun result => (suppress result, before)) <$>
        RawCtxSelectedSealConsumer.sealing source.crypto actual (PqxdhServerAuthCtxSend.sealing pending) := by
  rw [PqxdhServerAuthBuildProgram.sealer_run,
    sealing_mask source.crypto actual (PqxdhServerAuthCtxSend.sealing pending), Functor.map_map]
  congr 1
  funext result
  cases result <;> rfl

open PqxdhJointKdfGame PqxdhServerAuthCtxCalls
open PqxdhServerAuthBuildProgram (Log Compiler)

/-- The same concrete driver is interpreted with the supplied frame writer. -/
noncomputable def calls (source : FixedHkdfSha512NoSaltSource) (actual : RawCtxMixedShared.Writer)
    (rest : Residual) : RawCtxChainOwner.Calls Kernel Compiler :=
  PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest
    (PqxdhServerAuthBuildProgram.sealer source actual)

/-- Every original driver/KDF/sealing request remains in the reference execution. The returned native encrypted value and newly added source seal log are suppressed while component refusal is preserved. -/
theorem send_mask (source : FixedHkdfSha512NoSaltSource) (actual : RawCtxMixedShared.Writer)
    (rest : Residual) (kernel : Kernel) (context : RawCtxSourceSend.SealContext) (before : Log) :
    ((calls source writer rest).send kernel context).run.run before =
      (fun result => (result.1.map (fun sent => (sent.1, none)), before)) <$>
        ((calls source actual rest).send kernel context).run.run before := by
  unfold calls PqxdhServerAuthCtxBuildSettlement.calls RawCtxChainSend.execute
  cases begun : RawCtxChainSend.normalBegin kernel context with
  | exhausted previous actual =>
      simp only [begun, RawCtxChainSend.program, simulateQ_pure, OptionT.run_pure,
        StateT.run_pure, map_pure]
      rfl
  | requested pending =>
      simp only [begun, RawCtxChainSend.program, simulateQ_bind, simulateQ_spec_query,
        PqxdhServerAuthCtxBuildSettlement.labels, pure_bind, bind_pure_comp,
        simulateQ_map, OptionT.run_map, StateT.run_map]
      rw [sealer_run source actual _, PqxdhServerAuthBuildProgram.sealer_run]
      simp only [Functor.map_map]
      congr 1
      funext result
      cases result <;> rfl

open PqxdhServerAuthExperiment (Codec Checks)
open PqxdhServerRegistrationPublication (AuxSpec Response responseFields firstContext)
variable {Reader WireResponse Metadata PeerMetadata Consumed K : Type}

noncomputable def plainAux (codec : Codec Reader WireResponse) (checks : Checks) : QueryImpl AuxSpec Compiler :=
  fun query => OptionT.lift (PqxdhServerAuthCtxNative.aux codec checks query)

def finish (codec : Codec Reader WireResponse) (candidate : pqxdh.ServerRegistrationCandidate)
    (metadata : PeerMetadata) (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)
    (sent : K × Option RawCtxSourceSend.Encrypted) :
    Option Response × PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed :=
  match sent.2 with
  | none => (none, state)
  | some encrypted =>
    match codec.write2 (responseFields candidate encrypted) with
    | none => (none, state)
    | some bytes => (some ⟨bytes, candidate.key_id⟩,
        PqxdhInitialGenericPublication.publish state candidate sent.1 metadata)

/-- After the unchanged actual send, erasure and outer serialization are precisely the source's pure optional settlement. No source gate or component work is removed. -/
theorem after_pure (codec : Codec Reader WireResponse) (checks : Checks)
    (driver : RawCtxChainOwner.Calls K Compiler) (candidate : pqxdh.ServerRegistrationCandidate)
    (authenticated : Pqxdh.Bytes) (kernel : K) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed) :
    PqxdhInitialGenericPublication.afterInitialization driver (plainAux codec checks)
      candidate authenticated kernel metadata state =
      finish codec candidate metadata state <$> driver.send kernel (firstContext candidate authenticated) := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, map_eq_bind_pure_comp]
  refine bind_congr fun ⟨advanced, encrypted⟩ => ?_
  simp only [plainAux, PqxdhServerAuthCtxNative.aux, OptionT.lift_pure, pure_bind]
  cases encrypted with
  | none => rfl
  | some encrypted =>
      simp only [Function.comp_apply, finish]
      cases codec.write2 (responseFields candidate encrypted) <;> rfl

/-- The reference first-send tail has the same component program, with only its complete native result forced to rejection and its source log restored. Explicit component refusal stays unchanged. -/
theorem after_mask (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (candidate : pqxdh.ServerRegistrationCandidate)
    (authenticated : Pqxdh.Bytes) (kernel : Kernel) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) (before : Log) :
    (PqxdhInitialGenericPublication.afterInitialization (calls source writer rest) (plainAux codec checks)
      candidate authenticated kernel metadata state).run.run before =
      (fun result => (result.1.map (fun _ => (none, state)), before)) <$>
        (PqxdhInitialGenericPublication.afterInitialization (calls source codec.frameWrite rest) (plainAux codec checks)
          candidate authenticated kernel metadata state).run.run before := by
  rw [after_pure, after_pure]
  simp only [OptionT.run_map, StateT.run_map]
  rw [send_mask]
  simp only [Functor.map_map]
  congr 1
  funext result
  cases result.1 <;> rfl

/-- Every original auxiliary reply is pure at this executable interface, including arbitrary failed writes. -/
theorem plain_aux (codec : Codec Reader WireResponse) (checks : Checks) (query : AuxSpec.Domain) :
    plainAux codec checks query = pure (PqxdhServerAuthPublicationWriter.auxValue codec checks query) := by
  cases query <;> simp [plainAux, PqxdhServerAuthCtxNative.aux, PqxdhServerAuthPublicationWriter.auxValue]

/-- Suppress only a normal native response; component refusal and Rust diagnostics retain their original distinctions. -/
def suppressNative {S : Type} (state : S) (result : Option (RustM (Option Response × S))) :
    Option (RustM (Option Response × S)) :=
  (fun outcome => (fun _ => (none, state)) <$> outcome) <$> result

/-- Every source candidate gate and source coin/query remains before the reference's forced native rejection. This is an unconditional complete-program equality. -/
theorem candidate_mask (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (initial : RustM Kernel)
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) (before : Log) :
    (PqxdhInitialGenericBuilder.candidate (calls source writer rest) (plainAux codec checks)
      initial candidate data metadata state).run.run before =
      (fun result => (suppressNative state result.1, before)) <$>
        (PqxdhInitialGenericBuilder.candidate (calls source codec.frameWrite rest) (plainAux codec checks)
          initial candidate data metadata state).run.run before := by
  simp only [PqxdhInitialGenericBuilder.candidate, plain_aux,
    PqxdhServerAuthPublicationWriter.auxValue, pure_bind]
  cases checks.beaconIdentity candidate.beacon_identity_public_key <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  · simp only [OptionT.run_pure, StateT.run_pure, map_pure]
    rfl
  · cases checks.reservePeer <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
    · simp only [OptionT.run_pure, StateT.run_pure, map_pure]
      rfl
    · cases initial with
      | fail error => rfl
      | div => rfl
      | ok kernel =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          by_cases empty : (data.getD PqxdhServerRegistrationPublication.registrationWitness).isEmpty = true
          · simp only [empty, ite_true, OptionT.run_pure, StateT.run_pure, map_pure]
            rfl
          · simp only [empty, Bool.false_eq_true, ite_false]
            by_cases fits : 8 + (data.getD PqxdhServerRegistrationPublication.registrationWitness).length ≤ Usize.max
            · simp only [fits, ite_true]
              cases checks.reservePlaintext (8 + (data.getD PqxdhServerRegistrationPublication.registrationWitness).length) <;>
                simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
              · rfl
              · cases binding : candidate.key_id_binding with
                | fail error => rfl
                | div => rfl
                | ok binding =>
                    simp only [OptionT.run_map, StateT.run_map]
                    rw [after_mask]
                    simp only [Functor.map_map]
                    congr 1
                    funext result
                    cases result.1 <;> rfl
            · simp only [fits, ite_false]
              rfl

/-- The complete pending-token builder preserves every original gate and component effect before forcing its normal native reply to rejection. -/
theorem build_mask (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (initial : RustM Kernel)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) (before : Log) :
    (PqxdhServerAuthSendFactor.genericBuild (calls source writer rest) (plainAux codec checks)
      initial pending data metadata state).run.run before =
      (fun result => (suppressNative state result.1, before)) <$>
        (PqxdhServerAuthSendFactor.genericBuild (calls source codec.frameWrite rest) (plainAux codec checks)
          initial pending data metadata state).run.run before := by
  unfold PqxdhServerAuthSendFactor.genericBuild
  cases next : pqxdh.server_next_key_id state.control <;>
    simp only [PqxdhInitialGenericBuilder.continueRust]
  case fail error => rfl
  case div => rfl
  case ok value =>
    cases value with
    | Err error => rfl
    | Ok key =>
        simp only []
        cases prepared : pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩
          (if (state.server.peers key).isSome then .Occupied else .Available) with
        | fail error => rfl
        | div => rfl
        | ok value =>
            cases value with
            | Err error => rfl
            | Ok candidate => exact candidate_mask source codec checks rest initial candidate data metadata state before

/-- Only the selected reference callback uses this codec; ordinary and public source callbacks retain the original codec. -/
def referenceCodec (codec : Codec Reader WireResponse) : Codec Reader WireResponse :=
  { codec with frameWrite := writer }

/-- Changing only the reference inner writer leaves every original auxiliary callback exactly unchanged. -/
theorem reference_aux (codec : Codec Reader WireResponse) (checks : Checks) :
    plainAux (referenceCodec codec) checks = plainAux codec checks := by
  funext query
  cases query <;> rfl

/-- The literal complete executable builder is the native projection of its actual material-driver program, with every optional result and source log retained. -/
theorem compiled_run (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (before : Log) :
    (PqxdhServerAuthBuildProgram.compiled source codec checks rest pending data metadata state).run.run before =
      (fun result => ((fun reply => Prod.map id
        (PqxdhInitialGenericPublication.native PqxdhServerAuthCtxBuildSettlement.resolve) <$> reply) <$> result.1,
        result.2)) <$>
        (PqxdhServerAuthSendFactor.genericBuild (calls source codec.frameWrite rest) (plainAux codec checks)
          (PqxdhServerAuthCtxCalls.initial false rest.2.2) pending data metadata
          (PqxdhServerAuthCtxBuildSettlement.embed state)).run.run before := by
  unfold PqxdhServerAuthBuildProgram.compiled PqxdhServerAuthBuildProgram.compiler
  rw [PqxdhServerAuthBuildProgram.program_interpret]
  simp only [OptionT.run_map, StateT.run_map]
  rfl

/-- Unconditionally suppressing the selected reference frame writer preserves the exact whole component program and its original optional refusal/diagnostics. Every normal native response becomes None with the old complete Server state, and the old source log is retained. -/
theorem compiled_mask (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (before : Log) :
    (PqxdhServerAuthBuildProgram.compiled source (referenceCodec codec) checks rest pending data metadata state).run.run before =
      (fun result => (suppressNative state result.1, before)) <$>
        (PqxdhServerAuthBuildProgram.compiled source codec checks rest pending data metadata state).run.run before := by
  rw [compiled_run, compiled_run, reference_aux]
  change (fun result => ((fun reply => Prod.map id
    (PqxdhInitialGenericPublication.native PqxdhServerAuthCtxBuildSettlement.resolve) <$> reply) <$> result.1,
    result.2)) <$>
    (PqxdhServerAuthSendFactor.genericBuild (calls source writer rest) (plainAux codec checks)
      (PqxdhServerAuthCtxCalls.initial false rest.2.2) pending data metadata
      (PqxdhServerAuthCtxBuildSettlement.embed state)).run.run before = _
  rw [build_mask]
  simp only [Functor.map_map]
  congr 1
  funext result
  cases result.1 with
  | none => rfl
  | some outcome =>
      have collapse : PqxdhInitialGenericPublication.native PqxdhServerAuthCtxBuildSettlement.resolve
          (PqxdhServerAuthCtxBuildSettlement.embed state) = state :=
        PqxdhServerAuthCtxBuildSettlement.native_embed _ state
      cases outcome <;> simp only [suppressNative, Functor.map_map, Prod.map_apply, id_eq]
      all_goals rw [collapse]

/-- The unconditional local comparison preserves every generalized all-replies query certificate, including plaintext-byte budgets. This is a single builder statement, not a bound on a changed adaptive API continuation. -/
theorem compiled_budget_iff {Budget : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader WireResponse) (checks : Checks) (rest : Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (before : Log)
    (budget : Budget) (canQuery : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Prop)
    (cost : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Budget) :
    ((PqxdhServerAuthBuildProgram.compiled source (referenceCodec codec) checks rest pending data metadata state).run.run before).IsQueryBound budget canQuery cost ↔
      ((PqxdhServerAuthBuildProgram.compiled source codec checks rest pending data metadata state).run.run before).IsQueryBound budget canQuery cost := by
  rw [compiled_mask, isQueryBound_map_iff]

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.known_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.known_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.selected_mask' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.selected_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.call_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.call_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.sealing_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.sealing_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.sealer_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.sealer_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.send_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.send_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.after_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.after_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.after_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.after_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.plain_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.plain_aux

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.candidate_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.candidate_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.build_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.build_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.reference_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.reference_aux

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.compiled_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.compiled_run

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.compiled_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.compiled_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.compiled_budget_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame.compiled_budget_iff

