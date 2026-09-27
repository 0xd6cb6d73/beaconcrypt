import BeaconcryptCore.Computational.RawCtxFreshChainCut
import BeaconcryptCore.Computational.JointEagerTable

/-!
At a selected full76 response, only the first32 message key becomes unavailable. The original second32 next chain and final12 nonce remain simulator data; this does not make them network-public. A private material slot holds either this selected key with its nonce or an unchanged known material value. The interpreter may map different slots to equal byte strings.

The actual source decoder and receive/send resumption preserve every preexisting field and staged slot while installing the selected marker. The full-continuation distribution equality applies only to an already justified uniform full76 draw. It does not assert that fixed HKDF outputs are uniform, that other keys are independent, that known material cannot alias the selected key, or that selected-key reveals can be answered. Those obligations remain part of the consuming stopped source experiment.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageKey
open PqxdhFullSecretInputKdf PqxdhSecretInputKdf PqxdhOrderedChainHybrids
open RawCtxFreshChainCut RawCtxMaterialInterpretation

inductive Slot where
  | hidden : NonceOutput → Slot
  | known : RatchetMaterial → Slot

def interpret (key : RootOutput) : Slot → RatchetMaterial
  | .hidden nonce => concreteMaterial (key, nonce)
  | .known value => value

/-- The original full response retains the next chain and nonce while its first32 is interpreted only at the selected material slot. -/
theorem decoded_selected (output : FullOutput) :
    RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output) =
      (concreteChain (nextChain output), interpret (material output).1 (.hidden (material output).2)) :=
  decoded_parts output

/-- Lifting all earlier material as known retains the entire original source kernel, even if byte aliases exist. -/
theorem known_kernel {Send Receive : Type} (key : RootOutput)
    (entry : RefinedRatchet Send Receive RatchetMaterial) :
    mapRefined (interpret key) (mapRefined Slot.known entry) = entry := by
  cases entry
  simp only [mapRefined, mapArray, List.map_map]
  congr 1
  apply Subtype.ext
  simp only [Function.comp_def]
  have identity : (fun x : core.option.Option (CachedReceiveKey RatchetMaterial) =>
      mapOption (mapCached (interpret key)) (mapOption (mapCached Slot.known) x)) = id := by
    funext value
    cases value with
    | none => rfl
    | some value => cases value; rfl
  simp only [identity, List.map_id]

/-- All staged skipped-key slots retain presence, tags and complete material under known lifting. -/
theorem known_slots {size : Std.Usize} (key : RootOutput)
    (slots : Std.Array (core.option.Option (CachedReceiveKey RatchetMaterial)) size) :
    mapArray (mapOption (mapCached (interpret key)))
      (mapArray (mapOption (mapCached Slot.known)) slots) = slots := by
  apply Subtype.ext
  simp only [mapArray, List.map_map]
  have identity : (mapOption (mapCached (interpret key))) ∘
      (mapOption (mapCached Slot.known)) = id := by
    funext value
    cases value with
    | none => rfl
    | some value => cases value; rfl
  simp only [identity, List.map_id]

/-- The actual receive request, including rollback entry and staged skipped keys, is unchanged before the selected response. -/
theorem known_receive {Context : Type} (key : RootOutput)
    (pending : RawCtxInterpretedReceive.Kdf RatchetMaterial Context) :
    RawCtxInterpretedReceive.mapKdf (interpret key)
      (RawCtxInterpretedReceive.mapKdf Slot.known pending) = pending := by
  cases pending
  simp only [RawCtxInterpretedReceive.mapKdf, known_kernel, known_slots]

/-- The actual send request and complete previous kernel are unchanged before the selected response. -/
theorem known_send {Context : Type} (key : RootOutput)
    (pending : RawCtxInterpretedSend.Kdf RatchetMaterial Context) :
    RawCtxInterpretedSend.mapKdf (interpret key)
      (RawCtxInterpretedSend.mapKdf Slot.known pending) = pending := by
  cases pending
  simp only [RawCtxInterpretedSend.mapKdf, known_kernel]

/-- The actual receive resumes from the same complete request with the selected message key unavailable, including rejection and skipped-key staging. -/
theorem receive_selected {Context : Type}
    (pending : RawCtxInterpretedReceive.Kdf RatchetMaterial Context) (output : FullOutput) :
    RawCtxInterpretedReceive.normalResume pending
      (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)) =
      RawCtxInterpretedReceive.mapEffect (interpret (material output).1)
        (RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf Slot.known pending)
          (concreteChain (nextChain output), .hidden (material output).2)) := by
  rw [decoded_selected]
  have mapped := RawCtxInterpretedReceive.normalResume_map (interpret (material output).1)
    (RawCtxInterpretedReceive.mapKdf Slot.known pending)
    (concreteChain (nextChain output), .hidden (material output).2)
  simpa only [known_receive] using mapped

/-- The same full response preserves native send advancement and passes only the hidden selected material slot to sealing. -/
theorem send_selected {Context : Type}
    (pending : RawCtxInterpretedSend.Kdf RatchetMaterial Context) (output : FullOutput) :
    RawCtxInterpretedSend.ready pending
      (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)) =
      RawCtxInterpretedSend.mapSeal (interpret (material output).1)
        (RawCtxInterpretedSend.ready (RawCtxInterpretedSend.mapKdf Slot.known pending)
          (concreteChain (nextChain output), .hidden (material output).2)) := by
  rw [decoded_selected]
  have mapped := RawCtxInterpretedSend.ready_map (interpret (material output).1)
    (RawCtxInterpretedSend.mapKdf Slot.known pending)
    (concreteChain (nextChain output), .hidden (material output).2)
  simpa only [known_send] using mapped

/-- Sampling the selected message key after the known nonce and next chain preserves every complete continuation, not just marginal key distributions. -/
theorem key_observed {Result : Type}
    (continuation : RootOutput → NonceOutput → RootOutput → ProbComp Result) :
    𝒮[($ᵗ FullOutput) >>= fun output =>
      continuation (material output).1 (material output).2 (nextChain output)] =
      𝒮[(do let nonce ← $ᵗ NonceOutput
             let chain ← $ᵗ RootOutput
             let key ← $ᵗ RootOutput
             continuation key nonce chain)] := by
  have original := fullOutput_observed (fun value chain => continuation value.1 value.2 chain)
  have reordered := evalSPMF_bind_bind_swap ($ᵗ RootOutput)
    ($ᵗ (NonceOutput × RootOutput)) (fun key pair => continuation key pair.1 pair.2)
  simp only [← pairSample, bind_assoc, pure_bind] at original reordered
  exact original.trans reordered

/-- The exact native decoder, with all three projections used jointly, factors through the ordinary uniform selected key sample. -/
theorem decoded_observed {Result : Type}
    (continuation : (RatchetChain × RatchetMaterial) → ProbComp Result) :
    𝒮[($ᵗ FullOutput) >>= fun output =>
      continuation (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))] =
      𝒮[(do let nonce ← $ᵗ NonceOutput
             let chain ← $ᵗ RootOutput
             let key ← $ᵗ RootOutput
             continuation (concreteChain chain, interpret key (.hidden nonce)))] := by
  simpa only [decoded_selected] using key_observed
    (fun key nonce chain => continuation (concreteChain chain, interpret key (.hidden nonce)))

/-- The original complete receive continuation consumes the same justified full76 draw with one hidden message-key slot; malformed control and rollback branches are included. -/
theorem receive_observed {Context Result : Type}
    (pending : RawCtxInterpretedReceive.Kdf RatchetMaterial Context)
    (continuation : RawCtxInterpretedReceive.Effect RatchetMaterial Context → ProbComp Result) :
    𝒮[($ᵗ FullOutput) >>= fun output => continuation
      (RawCtxInterpretedReceive.normalResume pending
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)))] =
      𝒮[(do let nonce ← $ᵗ NonceOutput
             let chain ← $ᵗ RootOutput
             let key ← $ᵗ RootOutput
             continuation (RawCtxInterpretedReceive.mapEffect (interpret key)
               (RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf Slot.known pending)
                 (concreteChain chain, .hidden nonce))))] := by
  simpa only [receive_selected] using key_observed
    (fun key nonce chain => continuation (RawCtxInterpretedReceive.mapEffect (interpret key)
      (RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf Slot.known pending)
        (concreteChain chain, .hidden nonce))))

/-- The reduction's selected receive preparation samples only the nonce and next chain; it has no selected message-key argument or draw. -/
noncomputable def prepareReceive {Context : Type}
    (sample : ProbComp (RawCtxInterpretedReceive.Kdf RatchetMaterial Context)) :
    ProbComp (RawCtxInterpretedReceive.Effect Slot Context) := do
  let pending ← sample
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  pure (RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf Slot.known pending)
    (concreteChain chain, .hidden nonce))

/-- The exact source-selected uniform response and full continuation have the ordinary prepare-then-uniform-key order, with the unavailable key confined to interpretation. -/
theorem receive_prepared {Context Result : Type}
    (sample : ProbComp (RawCtxInterpretedReceive.Kdf RatchetMaterial Context))
    (continuation : RawCtxInterpretedReceive.Effect RatchetMaterial Context → ProbComp Result) :
    𝒮[(do let pending ← sample
           let output ← $ᵗ FullOutput
           continuation (RawCtxInterpretedReceive.normalResume pending
             (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))))] =
      𝒮[(do let prepared ← prepareReceive sample
             let key ← $ᵗ RootOutput
             continuation (RawCtxInterpretedReceive.mapEffect (interpret key) prepared))] := by
  simp only [prepareReceive, bind_assoc, pure_bind]
  exact evalSPMF_bind_congr' sample (fun pending => receive_observed pending continuation)

/-- Every original preparation random query remains charged, plus the actual 12-byte nonce and 32-byte next chain; the primitive challenger separately supplies its 32-byte key. -/
theorem prepare_receive_bound {Context : Type}
    (sample : ProbComp (RawCtxInterpretedReceive.Kdf RatchetMaterial Context))
    (qPrior : Nat) (bounded : sample.IsTotalQueryBound qPrior) :
    (prepareReceive sample).IsTotalQueryBound (qPrior + 44) := by
  unfold prepareReceive
  apply isTotalQueryBound_bind bounded
  intro pending
  apply isTotalQueryBound_bind (n₂ := 32) (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 12)
  intro nonce
  simpa only [Nat.add_zero] using isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
    (fun chain => (show (pure (RawCtxInterpretedReceive.normalResume
      (RawCtxInterpretedReceive.mapKdf Slot.known pending) (concreteChain chain, .hidden nonce)) :
      ProbComp _).IsTotalQueryBound 0 from by trivial))

end BeaconcryptCore.Computational.RawCtxSelectedMessageKey

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.decoded_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.decoded_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.known_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.known_kernel

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.known_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.known_slots

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.known_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.known_receive

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.known_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.known_send

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.receive_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.receive_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.send_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.send_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.key_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.key_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.decoded_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.decoded_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.receive_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.receive_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.receive_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.receive_prepared

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageKey.prepare_receive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageKey.prepare_receive_bound
