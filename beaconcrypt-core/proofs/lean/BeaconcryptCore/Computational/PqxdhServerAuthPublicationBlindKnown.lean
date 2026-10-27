import BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind

/-! Successful selected-record replacement commutes with the actual adaptive known-key reduction, preserving every known history and public-query effect. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxDynamicKnownKeys
variable {Result : Type}

/-- The ordinary challenger request is executed unchanged; only its successful selected reply is replaced for the source continuation. -/
noncomputable def scrub (replacement : CtxRomRecord) : QueryImpl ReceiveSpec (OracleComp ReceiveSpec)
  | .inl (.inr (.inr input)) => do
      let reply ← ReceiveSpec.query (.inl (.inr (.inr input)))
      pure (reply.map fun _ => replacement)
  | query => ReceiveSpec.query query

/-- Programs with zero ordinary selected seals keep all original public, random and raw requests under replacement. -/
theorem quiet (replacement : CtxRomRecord) (work : OracleComp ReceiveSpec Result)
    (bounded : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0) :
    simulateQ (scrub replacement) work = work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
    simp only [OracleComp.isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at bounded
    rcases query with ((coin | (input | request)) | raw)
    all_goals simp only [simulateQ_bind, simulateQ_spec_query, scrub]
    all_goals first
      | exact False.elim (bounded.1 trivial)
      | exact bind_congr fun reply => ih reply (bounded.2 reply)

/-- The actual known-key reduction commutes with successful-record replacement, preserving its complete history and every forwarded shared hash. -/
theorem step (replacement : CtxRomRecord) (crypto : Pqxdh.Crypto)
    (query : Spec.Domain) (state : ReductionState) :
    simulateQ (scrub replacement) ((AdaptiveCtxDynamicKnownKeys.reductionImpl crypto query).run state) =
      (simulateQ (AdaptiveCtxDynamicKnownKeys.reductionImpl crypto) (PqxdhServerAuthPublicationBlind.scrub replacement query)).run state := by
  cases query with
  | inl query =>
    rcases query with ((coin | (input | request)) | raw)
    all_goals simp only [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, scrub, PqxdhServerAuthPublicationBlind.scrub,
      bind_assoc, pure_bind]
    all_goals rfl
  | inr known =>
    simp only [PqxdhServerAuthPublicationBlind.scrub, simulateQ_spec_query]
    apply quiet
    exact AdaptiveCtxDynamicKnownBounds.target_step crypto AdaptiveCtxQueryBounds.SourceSeal
      AdaptiveCtxSharedTarget.forward_seal_class (.inr known) state

/-- Complete adaptive known-key generation and local histories commute with the same successful-record replacement. The reduction requires no selected-key argument; known byte aliases are not excluded. -/
theorem program (replacement : CtxRomRecord) (crypto : Pqxdh.Crypto)
    (client : OracleComp Spec Result) (state : ReductionState) :
    simulateQ (scrub replacement) (AdaptiveCtxDynamicKnownKeys.wrapped crypto client state) =
      AdaptiveCtxDynamicKnownKeys.wrapped crypto
        (simulateQ (PqxdhServerAuthPublicationBlind.scrub replacement) client) state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [AdaptiveCtxDynamicKnownKeys.wrapped, simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [AdaptiveCtxDynamicKnownKeys.wrapped, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [step]
    exact bind_congr fun ⟨reply, after⟩ => ih reply after

open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
variable {ι KemSK Reader WireResponse : Type} {baseSpec : OracleSpec ι}

/-- The literal fully sampled reference remains blind after lowering every adaptive known-key operation into the ordinary one-key interface, retaining all known-key histories. -/
theorem reference (replacement : CtxRomRecord)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (state : ReductionState) :
    simulateQ (scrub replacement) (AdaptiveCtxDynamicKnownKeys.wrapped setup.source.crypto
      (PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j) state) =
      AdaptiveCtxDynamicKnownKeys.wrapped setup.source.crypto
        (PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j) state := by
  rw [program, PqxdhServerAuthPublicationBlind.client_scrub]

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown.quiet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown.quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown.step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown.program
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown.reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown.reference
