import BeaconcryptCore.Computational.RawCtxMixedPositionCapability
import BeaconcryptCore.Computational.RawCtxSelectiveReplay
import BeaconcryptCore.Computational.RawCtxSupportedSample
import BeaconcryptCore.Refinement.RatchetInitialization

/-!
The original receive and send programs preserve their initial directional positions under an arbitrary fixed private KDF interpreter. The opening and sealing programs retain every probabilistic effect and complete shared state. This is the invariant used after support-only replay of a mutable private table; no reached table is assumed uniform, and no program probability or query cost is transferred by replay.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFunctionalPositions
open RawCtxMaterialPositions
variable {AD PT CT Context Plaintext Output State ι : Type} {base : OracleSpec ι}

/-- Every original optional receive preserves both initial directional origins, including failed openings and all rejection paths. -/
theorem receive (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (sendOrigin receiveOrigin : RatchetChain) (entry : ConcreteRatchetKernel)
    (valid : RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin entry)
    (target : Std.U64) (context : Context)
    (opening : ReceiveOpen Context → StateT State (OracleComp base) (core.option.Option Plaintext))
    (state : State) (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × State)
    (supported : result ∈ support ((simulateQ (bareReceiveImpl execute opening)
      (RawCtxOwnerOracle.receive entry target context)).run state)) :
    RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin result.1.1 := by
  rw [← receive_complete_erase execute opening (RawCtxOwnerOracle.receive entry target context) (state, []), support_map] at supported
  obtain ⟨original, reached, same⟩ := supported
  obtain ⟨send, receive, refined, aligned⟩ := valid
  obtain ⟨nextReceive, preserved⟩ := receive_preserves_positions cr execute receiveOrigin send receive entry context target
    refined opening (state, []) original reached
  subst result
  exact ⟨send, nextReceive, preserved, aligned⟩

/-- Every original send attempt preserves both directional origins, including an exhausted counter and an unsuccessful seal. -/
theorem send (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (sendOrigin receiveOrigin : RatchetChain) (entry : ConcreteRatchetKernel)
    (valid : RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin entry)
    (context : Context)
    (sealing : SendSeal Context → StateT State (OracleComp base) (Option Output))
    (state : State) (result : (ConcreteRatchetKernel × Option Output) × State)
    (supported : result ∈ support ((simulateQ (bareSendImpl execute sealing)
      (RawCtxSourceSend.send entry context)).run state)) :
    RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin result.1.1 := by
  rw [← send_complete_erase execute sealing (RawCtxSourceSend.send entry context) (state, []), support_map] at supported
  obtain ⟨original, reached, same⟩ := supported
  obtain ⟨send, receive, refined, aligned⟩ := valid
  obtain ⟨nextSend, preserved, nextAligned⟩ := send_preserves_positions cr execute receiveOrigin sendOrigin send receive entry context
    refined aligned sealing (state, []) original reached
  subst result
  exact ⟨nextSend, receive, preserved, nextAligned⟩

/-- Every successful source send response identifies its actual sealing invocation and the material at that original directional sequence. -/
theorem send_reply (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (entry : ConcreteRatchetKernel)
    (aligned : entry.refined.send_chain = Ratchet.chainAt (withInterpreter cr execute) origin entry.refined.control.send_sequence.val)
    (context : RawCtxSourceSend.SealContext)
    (sealing : RawCtxSourceSend.SealInput → StateT State (OracleComp base) (Option Pqxdh.Bytes))
    (state : State) (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × State)
    (reply : RawCtxSourceSend.Encrypted)
    (supported : result ∈ support ((simulateQ (bareSendImpl execute (RawCtxMixedPositionCapability.sealingAt sealing))
      (RawCtxSourceSend.send entry context)).run state))
    (success : result.1.2 = some reply) :
    ∃ input : RawCtxSourceSend.SealInput,
      input.context = context ∧ input.sequence = reply.sequence ∧
      reply.sequence.val = entry.refined.control.send_sequence.val + 1 ∧
      input.material = Ratchet.msgKeyAt (withInterpreter cr execute) origin (reply.sequence.val - 1) ∧
      (some reply.ciphertext, result.2) ∈ support ((sealing input).run state) := by
  by_cases exhausted : entry.refined.control.send_sequence = core.num.U64.MAX
  · rw [RawCtxSourceSend.send_exhausted entry context exhausted] at supported
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    cases success
  · obtain ⟨ready, material, sequence, ctx, advanced, actual⟩ := RawCtxMixedPositionCapability.bare_positioned_run
      cr execute origin entry context aligned exhausted (RawCtxMixedPositionCapability.sealingAt sealing)
    rw [actual] at supported
    simp only [RawCtxMixedPositionCapability.sealingAt, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨⟨ciphertext, finalState⟩, sealed, rfl⟩ := supported
    cases ciphertext with
    | none => cases success
    | some ciphertext =>
      simp only [Option.map_some, Option.some.injEq] at success
      subst reply
      refine ⟨RawCtxSourceSend.arguments ready, ctx, rfl, sequence, ?_, sealed⟩
      simpa only [RawCtxSourceSend.arguments, RawCtxSourceSend.encrypted, sequence, Nat.add_sub_cancel] using material

structure Located (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter) where
  kernel : ConcreteRatchetKernel
  sendOrigin : RatchetChain
  receiveOrigin : RatchetChain
  valid : RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin kernel

noncomputable def calls (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (opening : ReceiveOpen RawCtxWholeOwner.OpenContext → StateT State (OracleComp base) (core.option.Option RawCtxWholeOwner.Decrypted))
    (sealing : SendSeal RawCtxSourceSend.SealContext → StateT State (OracleComp base) (Option RawCtxSourceSend.Encrypted)) :
    RawCtxChainOwner.Calls (Located cr execute) (StateT State (OracleComp base)) where
  receive entry target context state :=
    (fun result => ((⟨result.val.1.1, entry.sendOrigin, entry.receiveOrigin, result.property⟩, result.val.1.2), result.val.2)) <$>
      RawCtxSupportedSample.certify ((simulateQ (bareReceiveImpl execute opening)
        (RawCtxOwnerOracle.receive entry.kernel target context)).run state)
        (fun result => RoleReachable (withInterpreter cr execute) entry.sendOrigin entry.receiveOrigin result.1.1)
        (receive cr execute entry.sendOrigin entry.receiveOrigin entry.kernel entry.valid target context opening state)
  send entry context state :=
    (fun result => ((⟨result.val.1.1, entry.sendOrigin, entry.receiveOrigin, result.property⟩, result.val.1.2), result.val.2)) <$>
      RawCtxSupportedSample.certify ((simulateQ (bareSendImpl execute sealing)
        (RawCtxSourceSend.send entry.kernel context)).run state)
        (fun result => RoleReachable (withInterpreter cr execute) entry.sendOrigin entry.receiveOrigin result.1.1)
        (send cr execute entry.sendOrigin entry.receiveOrigin entry.kernel entry.valid context sealing state)

/-- Forgetting only the origin certificate recovers the literal original receive and complete primitive state. -/
theorem receive_erase (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (opening : ReceiveOpen RawCtxWholeOwner.OpenContext → StateT State (OracleComp base) (core.option.Option RawCtxWholeOwner.Decrypted))
    (sealing : SendSeal RawCtxSourceSend.SealContext → StateT State (OracleComp base) (Option RawCtxSourceSend.Encrypted))
    (entry : Located cr execute) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    Prod.map Located.kernel id <$> (calls cr execute opening sealing).receive entry target context =
      simulateQ (bareReceiveImpl execute opening) (RawCtxOwnerOracle.receive entry.kernel target context) := by
  funext state
  change (Prod.map Located.kernel id <$> (calls cr execute opening sealing).receive entry target context).run state = _
  rw [StateT.run_map]
  change (Prod.map (Prod.map Located.kernel id) id) <$> ((calls cr execute opening sealing).receive entry target context).run state = _
  simp only [calls, StateT.run, Functor.map_map, Prod.map_apply, id_eq]
  exact RawCtxSupportedSample.erase _ _ _

/-- Forgetting only the origin certificate recovers the original send, optional reply and complete primitive state. -/
theorem send_erase (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (opening : ReceiveOpen RawCtxWholeOwner.OpenContext → StateT State (OracleComp base) (core.option.Option RawCtxWholeOwner.Decrypted))
    (sealing : SendSeal RawCtxSourceSend.SealContext → StateT State (OracleComp base) (Option RawCtxSourceSend.Encrypted))
    (entry : Located cr execute) (context : RawCtxSourceSend.SealContext) :
    Prod.map Located.kernel id <$> (calls cr execute opening sealing).send entry context =
      simulateQ (bareSendImpl execute sealing) (RawCtxSourceSend.send entry.kernel context) := by
  funext state
  change (Prod.map Located.kernel id <$> (calls cr execute opening sealing).send entry context).run state = _
  rw [StateT.run_map]
  change (Prod.map (Prod.map Located.kernel id) id) <$> ((calls cr execute opening sealing).send entry context).run state = _
  simp only [calls, StateT.run, Functor.map_map, Prod.map_apply, id_eq]
  exact RawCtxSupportedSample.erase _ _ _

/-- The actual zero-counter constructor establishes the origin relation for every fixed private interpreter and its exact returned kernel. -/
theorem initialized (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (sendOrigin receiveOrigin : RatchetChain) (kernel : ConcreteRatchetKernel)
    (constructed : ConcreteRatchetKernel.new sendOrigin receiveOrigin = ok kernel) :
    RoleReachable (withInterpreter cr execute) sendOrigin receiveOrigin kernel := by
  obtain ⟨actual, made, _, valid⟩ := new_reachable (withInterpreter cr execute) sendOrigin receiveOrigin
  have same := RustM.ok.inj (constructed.symm.trans made)
  exact same ▸ valid

end BeaconcryptCore.Computational.RawCtxFunctionalPositions

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalPositions.receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalPositions.receive

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalPositions.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalPositions.send

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalPositions.send_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalPositions.send_reply

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalPositions.receive_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalPositions.receive_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalPositions.send_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalPositions.send_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxFunctionalPositions.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFunctionalPositions.initialized
