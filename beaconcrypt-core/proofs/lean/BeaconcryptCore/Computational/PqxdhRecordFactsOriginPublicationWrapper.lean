-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationHistory

/-! Literal experiment coins and secrecy sends preserve current-prefix publication evidence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordLiftInterface PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginPublicationHistory
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Entry Spec)
variable {n : Nat} {ι KemSK Reader Response E : Type} {baseSpec : OracleSpec ι}

/-- An actual native uniform query preserves dictionary publication evidence without adding a transcript entry. -/
theorem coin_history (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (coin : Nat) (before : NativeState n E) (transcript : List Entry)
    (history : History codec before.1.2 before.2 transcript)
    (result : Fin (coin + 1) × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inl coin)).run before)) :
    History codec result.2.1.2 result.2.2 transcript := by
  rw [nativeImpl_coin, support_map] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  exact history

/-- The experiment's actual hidden-bit draw preserves current-prefix record evidence. -/
theorem drawBit_history (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (before : NativeState n E) (transcript : List Entry)
    (history : History codec before.1.2 before.2 transcript)
    (result : Bool × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      PqxdhDeploymentSecrecy.drawBit).run before)) :
    History codec result.2.1.2 result.2.2 transcript := by
  simp only [PqxdhDeploymentSecrecy.drawBit, PqxdhDeploymentSecrecy.coin, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact coin_history modes replace setup codec route env 1 before transcript history inner reached

/-- The complete experiment-generated fresh plaintext sampler preserves current-prefix record evidence. -/
theorem uniformBytes_history (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (length : Nat) (before : NativeState n E) (transcript : List Entry)
    (history : History codec before.1.2 before.2 transcript)
    (result : Pqxdh.Bytes × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      (PqxdhDeploymentSecrecy.uniformBytes length)).run before)) :
    History codec result.2.1.2 result.2.2 transcript := by
  induction length generalizing before result with
  | zero =>
    simp only [PqxdhDeploymentSecrecy.uniformBytes, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact history
  | succ length ih =>
    simp only [PqxdhDeploymentSecrecy.uniformBytes, PqxdhDeploymentSecrecy.coin,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff] at supported
    obtain ⟨drawn, drawReached, rest, restReached, finished⟩ := supported
    obtain rfl := (mem_support_pure_iff _ _).mp finished
    exact ih drawn.2 (coin_history modes replace setup codec route env 255 before transcript history drawn drawReached)
      rest restReached

/-- The secrecy wrapper records the same actual optional ciphertext as its native send. -/
theorem send_history (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (handle : Handle) (plaintext : Pqxdh.Bytes) (before : NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) (transcript : List Entry)
    (history : History codec before.1.2 before.2 transcript)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      (PqxdhDeploymentSecrecy.send handle plaintext)).run before)) (event : Entry)
    (published : event.published = result.1.map (fun encrypted => (handle, encrypted))) :
    History codec result.2.1.2 result.2.2 (transcript ++ [event]) := by
  cases handle with
  | peer keyId =>
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] at supported
    have actual := native_history modes ideal replace setup codec route readback env (.inr (.serverSend keyId plaintext))
      before safe transcript history result supported
    apply history_publications_eq codec result.2.1.2 result.2.2 _ _ _ actual
    simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, published]
    cases result.1 <;> rfl
  | owner owner =>
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] at supported
    have actual := native_history modes ideal replace setup codec route readback env (.inr (.beaconSend owner plaintext))
      before safe transcript history result supported
    apply history_publications_eq codec result.2.1.2 result.2.2 _ _ _ actual
    simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, published]
    cases result.1 <;> rfl

/-- Appending entries without changing source control or dictionaries retains every earlier publication witness. -/
theorem history_append (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) (transcript suffix : List Entry)
    (history : History codec control secret transcript) : History codec control secret (transcript ++ suffix) := by
  intro label entry member
  obtain ⟨handle, frame, owned, matched, outcome⟩ := history label entry member
  exact ⟨handle, frame, owned, matched, outcome.imp_right (published_append codec transcript suffix handle frame)⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper.coin_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper.coin_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper.drawBit_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper.drawBit_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper.uniformBytes_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper.uniformBytes_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper.send_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper.send_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper.history_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationWrapper.history_append
