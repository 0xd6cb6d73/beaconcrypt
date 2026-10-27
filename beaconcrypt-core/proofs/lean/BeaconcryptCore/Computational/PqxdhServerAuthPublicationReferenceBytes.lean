import BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources
import BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds

/-! The mixed reference retains the source checked plaintext limit on every adaptive path. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxByteBounds PqxdhServerAuthPublicationReference
open PqxdhJointKdfGame
open PqxdhServerAuthCtxCalls (Residual)
variable {ι KemSK Reader WireResponse Result : Type} {baseSpec : OracleSpec ι}

/-- Actual pending-token and marked/ordinary dispatch retain the source plaintext limit; ordinary local encryption adds no selected plaintext. -/
theorem build_route_bounded (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK) :
    ((PqxdhServerAuthPublicationReference.build source codec checks rest session payload).run.run state).IsQueryBoundP Oversized 0 := by
  simpa only [ite_self, Nat.zero_mul] using
    PqxdhServerAuthPublicationReference.build_query_bound source codec checks rest session payload Oversized 0 0
      (fun token server state => by
        simpa only [PqxdhServerAuthCtxBuild.selected, PqxdhServerAuthCtxBuild.after,
          OptionT.run_mk, StateT.run, isQueryBoundP_map_iff] using
          compiled_bounded source (PqxdhServerAuthPublicationForcedFrame.referenceCodec codec) checks rest token.pending payload () server [])
      (fun token server state => no_seal _
        (PqxdhServerAuthCtxBuildBounds.known_bills source codec checks session token payload server state).2.2.1)
      state



/-- Every original API route either uses the checked registration builder or issues no selected sealing request. -/
theorem route_bounded (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (select : Bool)
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((PqxdhServerAuthPublicationReference.route setup codec checks context rest select query).run.run state).IsQueryBoundP Oversized 0 := by
  have bill := (PqxdhServerAuthPublicationReference.route_record_bills setup codec checks context rest select query state).1
  cases query with
  | inl coin =>
      apply no_seal
      simpa only [PqxdhServerAuthCtxStop.buildBill] using bill
  | inr query =>
      cases query
      case build session payload => exact build_route_bounded setup.source codec checks rest session payload state
      all_goals
        apply no_seal
        simpa only [PqxdhServerAuthCtxStop.buildBill] using bill


/-- The actual full handler's source settlement adds no oversized request. -/
theorem handler_bounded (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((PqxdhServerAuthPublicationReference.handler setup codec checks context rest Q j query).run.run state).IsQueryBoundP Oversized 0 := by
  simpa only [PqxdhServerAuthPublicationReference.handler, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff] using
    route_bounded setup codec checks context rest (!state.2 && hiddenDesignated Q j query state.1) query state



/-- Optional stopping preserves the byte gate along every adaptive reply path and complete local state. -/
theorem stopped_bounded {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthPublicationReference.handler setup codec checks context rest Q j)) work).run.run state).IsQueryBoundP Oversized 0 := by
  apply PqxdhServerAuthBuildProgramBounds.stopping_bound _ (fun _ => False) Oversized _ work 0
    (isQueryBoundP_false work 0) state
  intro query before
  change ((PqxdhServerAuthCtxReserve.stopped
    (PqxdhServerAuthPublicationReference.handler setup codec checks context rest Q j) query).run before).IsQueryBoundP Oversized 0
  rw [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped_step, isQueryBoundP_map_iff]
  exact handler_bounded setup codec checks context rest Q j query before.1



/-- The fully sampled reference issues no oversized selected plaintext on any adaptive reply path, retaining every optional result and complete sampler values. -/
theorem client_bounded (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (client setup codec checks adversary Q j).IsQueryBoundP Oversized 0 := by
  unfold client
  simp only [bind_pure_comp]
  apply (isQueryBoundP_bind (no_seal _ (PqxdhServerAuthCtxAmbient.coin_other _).2.1) (m := 0) ?_).mono (by omega)
  intro context _
  apply (isQueryBoundP_bind (no_seal _ (PqxdhServerAuthCtxAmbient.coin_other _).2.1) (m := 0) ?_).mono (by omega)
  intro rest _
  simpa only [execution, PqxdhServerAuthPublicationReference.stopped, isQueryBoundP_map_iff] using
    stopped_bounded setup codec checks context rest Q j (adversary (contextInput setup false context))
      (PqxdhServerAuthCtxReserve.initial setup context).1


/-- The actual reference submits at most the source-sized single selected plaintext across its complete adaptive execution. No caller-supplied payload-size or writer condition is required. -/
theorem client_plaintext (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    AdaptiveCtxDynamicKnownBounds.PlaintextBound (client setup codec checks adversary Q j) Usize.max := by
  exact weighted _ 1 Usize.max
    (PqxdhServerAuthPublicationReferenceResources.client_record_bills setup codec checks adversary Q j).1
    (client_bounded setup codec checks adversary Q j) (by simp)

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.build_route_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.build_route_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.route_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.route_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.handler_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.handler_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.stopped_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.stopped_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.client_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.client_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.client_plaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes.client_plaintext
