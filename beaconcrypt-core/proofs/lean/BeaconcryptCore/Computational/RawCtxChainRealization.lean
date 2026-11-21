import BeaconcryptCore.Computational.RawCtxChainReceiveBounds
import BeaconcryptCore.Computational.RawCtxInterpretedArguments

/-!
Simultaneous arbitrary chain and material interpretation preserves the complete extracted send and skip/open drivers. Source admission, pending requests, actual response conversion and whole optional results are retained under exact operational callback equations in any lawful monad, including full StateT. The maps may be noninjective; neither inverse lookup nor label equality controls source branching.

These are functional realization equations, not cryptographic premises. Concrete callbacks must discharge them before a source-security application. Fixed interpretation does not justify a changing hidden-input table, input freshness, reveals, live retained ancestors, or independent output distributions. Private kernels and pending arguments remain interpreter context. All source control/conversion/copying and local primitive work remain computation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxChainRealization
open RawCtxChainInterpretation RawCtxMaterialInterpretation
open RawCtxInterpretedOpening hiding sequence

abbrev kernel {Send Receive Material Value : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) (material : Material → Value)
    (entry : RefinedRatchet Send Receive Material) := mapRefined material (mapChains send receive entry)

abbrev receiveEffect {Send Receive Material Value Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) (material : Material → Value)
    (effect : RawCtxChainReceive.Effect Send Receive Material Context) :=
  RawCtxInterpretedReceive.mapEffect material (RawCtxChainReceive.nativeEffect send receive effect)

/-- Simultaneous interpretation retains every chain/material continuation, without inverse lookup. -/
theorem receive_program {Send Receive Material Value Context Plaintext : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) (material : Material → Value)
    (labels : QueryImpl (RawCtxChainReceive.ReceiveSpec Send Receive Material Context Plaintext) m)
    (native : QueryImpl (RawCtxInterpretedReceive.ReceiveSpec Value Context Plaintext) m)
    (kdf : ∀ request, native (.inl (RawCtxChainSend.nativeRequest (receive request))) =
      (fun reply => (receive reply.1, material reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, native (.inr (mapOpening material (mapOpeningChains send receive pending))) =
      labels (.inr pending))
    (effect : RawCtxChainReceive.Effect Send Receive Material Context) :
    simulateQ native (RawCtxInterpretedReceive.program (receiveEffect send receive material effect)) =
      (fun result => (kernel send receive material result.1, result.2)) <$>
        simulateQ labels (RawCtxChainReceive.program effect) := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | kdfRequested pending =>
      simp only [receiveEffect, RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.mapEffect,
        RawCtxChainReceive.program, RawCtxInterpretedReceive.program, simulateQ_bind,
        simulateQ_spec_query, RawCtxInterpretedReceive.mapKdf, RawCtxChainReceive.nativeKdf, kdf, map_bind]
      dsimp only [OracleSpec.Range, RawCtxChainReceive.ReceiveSpec, RawCtxInterpretedReceive.ReceiveSpec,
        OracleSpec.add_def, Sum.elim_inl, OracleSpec.ofFn]
      rw [_root_.bind_map_left]
      refine bind_congr (fun reply => ?_)
      change simulateQ native (RawCtxInterpretedReceive.program
        (RawCtxInterpretedReceive.normalResume
          (RawCtxInterpretedReceive.mapKdf material (RawCtxChainReceive.nativeKdf send receive pending))
          (receive reply.1, material reply.2))) = _
      rw [RawCtxInterpretedReceive.normalResume_map material _ (receive reply.1, reply.2),
        RawCtxChainReceive.normalResume_native]
      exact ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending reply) _ rfl
    | rejected entry context =>
      simp only [receiveEffect, RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.mapEffect,
        RawCtxChainReceive.program, RawCtxInterpretedReceive.program, simulateQ_pure, map_pure, kernel]
    | openRequested pending =>
      simp only [receiveEffect, RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.mapEffect,
        RawCtxChainReceive.program, RawCtxInterpretedReceive.program, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, opening, map_bind, map_pure,
        RawCtxInterpretedReceive.normalFinish_map, RawCtxChainReceive.normalFinish_native, kernel]
      rfl

/-- Actual admission precedes the complete interpreted receive continuation. -/
theorem receive_execute {Send Receive Material Value Context Plaintext : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) (material : Material → Value)
    (labels : QueryImpl (RawCtxChainReceive.ReceiveSpec Send Receive Material Context Plaintext) m)
    (native : QueryImpl (RawCtxInterpretedReceive.ReceiveSpec Value Context Plaintext) m)
    (kdf : ∀ request, native (.inl (RawCtxChainSend.nativeRequest (receive request))) =
      (fun reply => (receive reply.1, material reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, native (.inr (mapOpening material (mapOpeningChains send receive pending))) =
      labels (.inr pending))
    (entry : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    simulateQ native (RawCtxInterpretedReceive.receive (kernel send receive material entry) target context) =
      (fun result => (kernel send receive material result.1, result.2)) <$>
        simulateQ labels (RawCtxChainReceive.execute entry target context) := by
  simpa only [RawCtxInterpretedReceive.receive, RawCtxChainReceive.execute, kernel,
    RawCtxInterpretedReceive.normalBegin_map, RawCtxChainReceive.normalBegin_native, receiveEffect] using
    receive_program send receive material labels native kdf opening (RawCtxChainReceive.normalBegin entry target context)

abbrev sendStart {Send Receive Material Value Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) (material : Material → Value)
    (start : RawCtxChainSend.Start Send Receive Material Context) :=
  RawCtxInterpretedSend.mapStart material (RawCtxChainSend.nativeStart send receive start)

/-- Joint chain/material interpretation preserves active failed-seal advancement and all callback effects. -/
theorem send_program {Send Receive Material Value Context Output : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) (material : Material → Value)
    (labels : QueryImpl (RawCtxChainSend.SendSpec Send Receive Material Context Output) m)
    (native : QueryImpl (RawCtxInterpretedSend.SendSpec Value Context Output) m)
    (kdf : ∀ request, native (.inl (RawCtxChainSend.nativeRequest (send request))) =
      (fun reply => (send reply.1, material reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, native (.inr (RawCtxInterpretedSend.mapSeal material
      (RawCtxChainSend.nativeSeal send receive pending))) = labels (.inr pending))
    (start : RawCtxChainSend.Start Send Receive Material Context) :
    simulateQ native (RawCtxInterpretedSend.program (sendStart send receive material start)) =
      (fun result => (kernel send receive material result.1, result.2)) <$>
        simulateQ labels (RawCtxChainSend.program start) := by
  cases start with
  | requested pending =>
    simp only [sendStart, RawCtxChainSend.nativeStart, RawCtxInterpretedSend.mapStart,
      RawCtxChainSend.program, RawCtxInterpretedSend.program, simulateQ_bind,
      simulateQ_spec_query, simulateQ_pure, RawCtxInterpretedSend.mapKdf,
      RawCtxChainSend.nativeKdf, kdf, map_bind, map_pure]
    dsimp only [OracleSpec.Range, RawCtxChainSend.SendSpec, RawCtxInterpretedSend.SendSpec,
      OracleSpec.add_def, Sum.elim_inl, OracleSpec.ofFn]
    rw [_root_.bind_map_left]
    refine bind_congr (fun reply => ?_)
    change (do
      let sealed ← native (.inr (RawCtxInterpretedSend.mapSeal material
        (RawCtxChainSend.nativeSeal send receive (RawCtxChainSend.ready pending reply))))
      pure (kernel send receive material (RawCtxChainSend.ready pending reply).advanced, sealed)) = _
    rw [sealing]
    rfl
  | exhausted entry context =>
    simp only [sendStart, RawCtxChainSend.nativeStart, RawCtxInterpretedSend.mapStart,
      RawCtxChainSend.program, RawCtxInterpretedSend.program, simulateQ_pure, map_pure, kernel]

/-- Original source admission is retained before the complete jointly interpreted send. -/
theorem send_execute {Send Receive Material Value Context Output : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) (material : Material → Value)
    (labels : QueryImpl (RawCtxChainSend.SendSpec Send Receive Material Context Output) m)
    (native : QueryImpl (RawCtxInterpretedSend.SendSpec Value Context Output) m)
    (kdf : ∀ request, native (.inl (RawCtxChainSend.nativeRequest (send request))) =
      (fun reply => (send reply.1, material reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, native (.inr (RawCtxInterpretedSend.mapSeal material
      (RawCtxChainSend.nativeSeal send receive pending))) = labels (.inr pending))
    (entry : RefinedRatchet Send Receive Material) (context : Context) :
    simulateQ native (RawCtxInterpretedSend.send (kernel send receive material entry) context) =
      (fun result => (kernel send receive material result.1, result.2)) <$>
        simulateQ labels (RawCtxChainSend.execute entry context) := by
  simpa only [RawCtxInterpretedSend.send, RawCtxChainSend.execute, kernel,
    RawCtxInterpretedSend.normalBegin_map, RawCtxChainSend.normalBegin_native, sendStart] using
    send_program send receive material labels native kdf sealing (RawCtxChainSend.normalBegin entry context)

/-- The native typed source receive is the complete joint handle program under actual primitive realization. -/
theorem receive_native {Send Receive Material Context Plaintext : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) (material : Material → RatchetMaterial)
    (labels : QueryImpl (RawCtxChainReceive.ReceiveSpec Send Receive Material Context Plaintext) m)
    (native : QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) m)
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$>
      native (.inl (RawCtxChainSend.nativeRequest (receive request))) =
      (fun reply => (receive reply.1, material reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, native (.inr (toNative (mapOpening material (mapOpeningChains send receive pending)))) =
      labels (.inr pending))
    (entry : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    simulateQ native (RawCtxOwnerOracle.receive ⟨kernel send receive material entry⟩ target context) =
      (fun result => (ConcreteRatchetKernel.mk (kernel send receive material result.1), result.2)) <$>
        simulateQ labels (RawCtxChainReceive.execute entry target context) := by
  rw [RawCtxInterpretedReceive.receive_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have mapped := receive_execute send receive material labels
    (native ∘ₛ RawCtxInterpretedReceive.nativeAdapter) ?_ ?_ entry target context
  · rw [mapped, Functor.map_map]
  · exact fun request => (simulateQ_map native
      ((RawCtxOwnerOracle.ReceiveSpec Context Plaintext).query (.inl (RawCtxChainSend.nativeRequest (receive request))))
      RawCtxInterpretedReceive.decodeResponse).trans
        ((congrArg (fun computation => RawCtxInterpretedReceive.decodeResponse <$> computation)
          (simulateQ_spec_query native (.inl (RawCtxChainSend.nativeRequest (receive request))))).trans (kdf request))
  · exact fun pending => (simulateQ_spec_query native _).trans (opening pending)
/-- The complete native send retains joint private handles and actual optional output under primitive realization. -/
theorem send_native {Send Receive Material Context Output : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) (material : Material → RatchetMaterial)
    (labels : QueryImpl (RawCtxChainSend.SendSpec Send Receive Material Context Output) m)
    (native : QueryImpl (RawCtxSourceSend.SendSpec Context Output) m)
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$>
      native (.inl (RawCtxChainSend.nativeRequest (send request))) =
      (fun reply => (send reply.1, material reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, native (.inr (RawCtxInterpretedSend.nativeSeal
      (RawCtxInterpretedSend.mapSeal material (RawCtxChainSend.nativeSeal send receive pending)))) =
      labels (.inr pending))
    (entry : RefinedRatchet Send Receive Material) (context : Context) :
    simulateQ native (RawCtxSourceSend.send ⟨kernel send receive material entry⟩ context) =
      (fun result => (ConcreteRatchetKernel.mk (kernel send receive material result.1), result.2)) <$>
        simulateQ labels (RawCtxChainSend.execute entry context) := by
  rw [RawCtxInterpretedSend.send_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have mapped := send_execute send receive material labels
    (native ∘ₛ RawCtxInterpretedSend.nativeAdapter) ?_ ?_ entry context
  · rw [mapped, Functor.map_map]
  · exact fun request => (simulateQ_map native
      ((RawCtxSourceSend.SendSpec Context Output).query (.inl (RawCtxChainSend.nativeRequest (send request))))
      RawCtxInterpretedReceive.decodeResponse).trans
        ((congrArg (fun computation => RawCtxInterpretedReceive.decodeResponse <$> computation)
          (simulateQ_spec_query native (.inl (RawCtxChainSend.nativeRequest (send request))))).trans (kdf request))
  · exact fun pending => (simulateQ_spec_query native _).trans (sealing pending)

end BeaconcryptCore.Computational.RawCtxChainRealization

/-- info: 'BeaconcryptCore.Computational.RawCtxChainRealization.receive_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainRealization.receive_program

/-- info: 'BeaconcryptCore.Computational.RawCtxChainRealization.receive_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainRealization.receive_execute

/-- info: 'BeaconcryptCore.Computational.RawCtxChainRealization.send_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainRealization.send_program

/-- info: 'BeaconcryptCore.Computational.RawCtxChainRealization.send_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainRealization.send_execute

/-- info: 'BeaconcryptCore.Computational.RawCtxChainRealization.receive_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainRealization.receive_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainRealization.send_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainRealization.send_native
