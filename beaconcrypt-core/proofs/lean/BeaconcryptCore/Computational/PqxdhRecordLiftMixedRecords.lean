-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainOrder
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget
import BeaconcryptCore.Computational.RawCtxChainReceiveBounds

/-! Complete source record execution transports the concrete mixed table's finite-depth invariant and actual KDF ledger. Operational callback transport is discharged by the real/mixed lookup and literal native services; no security assumption is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable
open PqxdhRecordLiftChainCompiler PqxdhRecordLiftChainOrder
variable {n : Nat} {Context Plaintext PrimitiveState : Type}

/-- Complete receive recursion retains a depth invariant whenever the actual lookup advances its ledger and opening does not decrease it. These operational callbacks are instantiated with the concrete mixed/native services below. -/
theorem receive_depth (seeds : Seeds (Fin n)) (valid : Table (Fin n) → Prop)
    (lookup : Lookup (Fin n) PrimitiveState) (opening : Open Context Plaintext PrimitiveState)
    (preserves : LookupPreserves valid lookup) (metric : PrimitiveState → Nat)
    (lookupDepth : ∀ coordinate state, valid state.1 → Available state.1 coordinate →
      DepthBound state.1 (metric state.2) → ∀ result ∈ support ((lookup coordinate).run state),
        DepthBound result.2.1 (metric result.2.2))
    (openingMono : ∀ pending state result, result ∈ support ((opening pending).run state) →
      metric state ≤ metric result.2)
    (effect : Effect (Fin n) Context) (state : Execution (Fin n) PrimitiveState)
    (good : valid state.1) (refs : References state.1 effect)
    (bounded : DepthBound state.1 (metric state.2))
    (result : (LabeledKernel (Fin n) × core.option.Option Plaintext) × Execution (Fin n) PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening effect).run state)) :
    DepthBound result.2.1 (metric result.2.2) := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result
  case h depth ih =>
    cases effect with
    | kdfRequested pending =>
      simp only [StateT.run, receive, mem_support_bind_iff] at supported
      obtain ⟨reply, member, continued⟩ := supported
      have facts := preserves pending.request state good refs.1.2 reply member
      exact ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
        _ reply.2 facts.2.2 (resume_references state.1 reply.2.1 facts.1 pending refs reply.1 facts.2.1)
        (lookupDepth pending.request state good refs.1.2 bounded reply member) result continued rfl
    | openRequested pending =>
      simp only [StateT.run, receive, bind_pure_comp, support_map] at supported
      obtain ⟨reply, member, rfl⟩ := supported
      exact depth_mono state.1 bounded (openingMono _ state.2 reply member)
    | rejected entry context =>
      simp_all only [StateT.run, receive, support_pure, Set.mem_singleton_iff]

/-- Every concrete real call, ideal hit and ideal miss leaves each other logical coordinate unchanged. No table-validity or byte-separation premise is needed. -/
theorem lookup_other (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool) (coordinate : Coordinate (Fin n))
    (state : Execution (Fin n) PqxdhRecordLiftWorld.Primitive)
    (result : PqxdhFullSecretInputKdf.FullOutput × Execution (Fin n) PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((PqxdhRecordLiftChainOracle.lookup source seeds ideal coordinate).run state))
    (other : Coordinate (Fin n)) (different : other ≠ coordinate) :
    result.2.1 other = state.1 other := by
  cases selected : ideal coordinate with
  | false =>
    rw [PqxdhRecordLiftChainOracle.lookup_real source seeds ideal coordinate state selected,
      support_pure, Set.mem_singleton_iff] at supported
    simpa only [supported, PqxdhRecordLiftRealTable.record] using
      (QueryCache.cacheQuery_of_ne state.1 (PqxdhRecordLiftRealTable.output source seeds state.1 coordinate) different)
  | true =>
    cases found : state.1 coordinate with
    | none =>
      rw [PqxdhRecordLiftChainOracle.lookup_miss source seeds ideal coordinate state selected found,
        support_map] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact QueryCache.cacheQuery_of_ne state.1 value different
    | some value =>
      rw [PqxdhRecordLiftChainOracle.lookup_hit source seeds ideal coordinate state selected value found,
        support_pure, Set.mem_singleton_iff] at supported
      simp only [supported]

/-- The actual mixed callback satisfies the source compiler's one-coordinate write footprint for every selector, including inconsistent input tables. -/
theorem lookup_writesOnly (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool) :
    PqxdhRecordLiftTableScope.LookupWritesOnly (PqxdhRecordLiftChainOracle.lookup source seeds ideal) := by
  exact fun coordinate state result supported other value found =>
    (eq_or_ne other coordinate).elim (fun same => Or.inl same)
      (fun different => Or.inr ⟨value,
        (lookup_other source seeds ideal coordinate state result supported other different).symm.trans found⟩)

/-- A prefix that has not queried a chosen coordinate cannot populate its entry through an unselected real or ideal callback. -/
theorem lookup_avoids (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (coordinate target : Coordinate (Fin n)) (different : coordinate ≠ target)
    (state : Execution (Fin n) PqxdhRecordLiftWorld.Primitive) (missing : state.1 target = none)
    (result : PqxdhFullSecretInputKdf.FullOutput × Execution (Fin n) PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((PqxdhRecordLiftChainOracle.lookup source seeds ideal coordinate).run state)) :
    result.2.1 target = none :=
  (lookup_other source seeds ideal coordinate state result supported target (Ne.symm different)).trans missing

open PqxdhServerAuthExperiment (Setup Codec)

/-- Every literal native program can only increase each native query counter. -/
theorem native_mono {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec X) (kind : RawCtxMixedOwner.CallKind)
    (state : PqxdhRecordLiftWorld.Primitive) (result : X × PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftWorld.primitives setup codec) client).run state)) :
    state.1.native kind ≤ result.2.1.native kind := by
  refine simulateQ_run_preservesInv (PqxdhRecordLiftWorld.primitives setup codec)
    (fun current => state.1.native kind ≤ current.1.native kind) ?_ client state (Nat.le_refl _) result supported
  intro query before unchanged after reached
  simp only [PqxdhRecordLiftWorld.primitives, StateT.run, bind_pure_comp, support_map] at reached
  obtain ⟨inner, _, rfl⟩ := reached
  by_cases same : RawCtxMixedOwner.callKind query = kind
  · simpa [same] using unchanged.trans (Nat.le_succ _)
  · simpa only [Function.update_of_ne (Ne.symm same)] using unchanged

/-- Logging keeps every native call and its counter bounds, including source writer attempts returning failure. -/
theorem logged_native {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec X) (kind : RawCtxMixedOwner.CallKind)
    (bound : Nat) (bounded : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = kind) bound)
    (state : PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames)
    (result : X × (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftLoggedAdapters.loggedNative
      (PqxdhRecordLiftWorld.primitives setup codec)) client).run state)) :
    state.1.1.native kind ≤ result.2.1.1.native kind ∧
      result.2.1.1.native kind ≤ state.1.1.native kind + bound := by
  rw [PqxdhRecordLiftLoggedAdapters.program_logged] at supported
  simp only [support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact ⟨native_mono setup codec _ kind state.1 inner member,
    PqxdhRecordLiftWorldBudget.native_support setup codec _ kind bound
      (PqxdhDeploymentCompileBudget.logged_bound _ client bound state.2 bounded) state.1 inner member⟩

/-- The actual opening adapter issues no ratchet KDF call, including missing-material and malformed-input rejection. -/
theorem receive_open_noKdf
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    (simulateQ RawCtxMixedOwner.receiveAdapter (RawCtxWholeOwner.adapter
      (.inr (RawCtxInterpretedOpening.toNative pending)))).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = .kdf) 0 := by
  simp only [RawCtxMixedOwner.receiveAdapter, QueryImpl.simulateQ_compose]
  apply RawCtxMixedOwner.receiveLift_bound
  have bounded := RawCtxSourceOpen.owner_kdf_bound (.ReceiveOpenRequested (RawCtxInterpretedOpening.toNative pending))
  simp only [RawCtxOwnerOracle.program, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    isQueryBoundP_map_iff, effectDepth, RawCtxSourceOpen.ownerAdapter, QueryImpl.apply_compose] at bounded
  convert bounded using 1
  funext query
  rcases query with request | (bytes | input) <;> simp [RawCtxMixedOwner.receiveKind]

/-- Literal logged opening retains the current native KDF count for every actual optional plaintext reply. -/
theorem opening_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames)
    (result : core.option.Option RawCtxWholeOwner.Decrypted ×
      (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftNativeAdapters.receiveOpen
      (PqxdhRecordLiftWorldCompiler.receiveNative (PqxdhRecordLiftLoggedAdapters.loggedNative
        (PqxdhRecordLiftWorld.primitives setup codec))) pending).run state)) :
    result.2.1.1.native .kdf = state.1.1.native .kdf := by
  have bounded := logged_native setup codec _ .kdf 0 (receive_open_noKdf pending) state result
    (by simpa only [PqxdhRecordLiftNativeAdapters.receiveOpen, PqxdhRecordLiftWorldCompiler.receiveNative,
      QueryImpl.simulateQ_compose] using supported)
  exact Nat.le_antisymm (by simpa only [Nat.add_zero] using bounded.2) bounded.1

/-- The concrete mixed lookup depth law survives the private pending-frame log unchanged. -/
theorem logged_lookup_depth (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool) (coordinate : Coordinate (Fin n))
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (bounded : DepthBound state.1 (state.2.1.1.native .kdf)) (available : Available state.1 coordinate)
    (result : PqxdhFullSecretInputKdf.FullOutput ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftLoggedAdapters.liftLookup
      (PqxdhRecordLiftChainOracle.lookup source seeds ideal) coordinate).run state)) :
    DepthBound result.2.1 (result.2.2.1.1.native .kdf) := by
  simp only [PqxdhRecordLiftLoggedAdapters.liftLookup, StateT.run, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact PqxdhRecordLiftChainOrder.lookup_depth source seeds ideal coordinate
    (state.1, state.2.1) bounded available inner member

/-- The actual mixed receive preserves finite table depth against its own native KDF ledger; all callback side conditions are discharged by the concrete interpreter. -/
theorem mixed_receive_depth {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (effect : Effect (Fin n) RawCtxWholeOwner.OpenContext)
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (good : PqxdhRecordLiftChainOracle.Valid setup.source seeds ideal state.1)
    (refs : References state.1 effect) (bounded : DepthBound state.1 (state.2.1.1.native .kdf))
    (result : (LabeledKernel (Fin n) × core.option.Option RawCtxWholeOwner.Decrypted) ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((receive seeds
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup setup.source seeds ideal))
      (PqxdhRecordLiftNativeAdapters.receiveOpen (PqxdhRecordLiftWorldCompiler.receiveNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec)))) effect).run state)) :
    DepthBound result.2.1 (result.2.2.1.1.native .kdf) := by
  exact receive_depth seeds _ _ _
    (PqxdhRecordLiftLoggedAdapters.liftLookup_preserves _ _
      (PqxdhRecordLiftChainOracle.lookup_preserves setup.source seeds ideal))
    (fun primitive => primitive.1.1.native .kdf)
    (fun coordinate before _ available depth after member =>
      logged_lookup_depth setup.source seeds ideal coordinate before depth available after member)
    (fun pending before after member => (opening_kdf setup codec pending before after member).symm.le)
    effect state good refs bounded result supported

/-- Literal sealing and publication add no ratchet KDF request after the send step has advanced. -/
theorem send_seal_noKdf
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) :
    (simulateQ RawCtxMixedOwner.sendAdapter (RawCtxSourceSend.adapter
      (.inr (RawCtxInterpretedSend.nativeSeal pending)))).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = .kdf) 0 := by
  simp only [RawCtxMixedOwner.sendAdapter, QueryImpl.simulateQ_compose]
  apply RawCtxMixedOwner.sendLift_bound
  simp only [RawCtxSourceSend.adapter, bind_pure_comp, simulateQ_map, liftM,
    simulateQ_spec_query, isQueryBoundP_map_iff, RawCtxSourceSeal.nativeAdapter]
  refine (isQueryBoundP_congr_pred
    (p' := fun query : RawCtxSourceSeal.NativeSpec.Domain => query.isLeft = true) ?_).2 ?_
  · intro query
    rcases query with request | (input | (bytes | frame)) <;> simp [RawCtxMixedOwner.sendKind]
  · exact RawCtxSourceSeal.sealLift_no_kdf
      (RawCtxSourceSeal.sealInput (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal pending)))

/-- The actual optional seal/writer result preserves the native KDF count after source send advancement. -/
theorem sealing_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext)
    (state : PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames)
    (result : Option RawCtxSourceSend.Encrypted ×
      (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftNativeAdapters.sendSeal
      (PqxdhRecordLiftWorldCompiler.sendNative (PqxdhRecordLiftLoggedAdapters.loggedNative
        (PqxdhRecordLiftWorld.primitives setup codec))) pending).run state)) :
    result.2.1.1.native .kdf = state.1.1.native .kdf := by
  have bounded := logged_native setup codec _ .kdf 0 (send_seal_noKdf pending) state result
    (by simpa only [PqxdhRecordLiftNativeAdapters.sendSeal, PqxdhRecordLiftWorldCompiler.sendNative,
      QueryImpl.simulateQ_compose] using supported)
  exact Nat.le_antisymm (by simpa only [Nat.add_zero] using bounded.2) bounded.1

/-- Concrete mixed send preserves finite depth through lookup, actual sealing and failed writer replies; exhausted sends leave the whole table untouched. -/
theorem mixed_send_depth {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (start : Start (Fin n) RawCtxSourceSend.SealContext)
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (refs : SendReferences state.1 start) (bounded : DepthBound state.1 (state.2.1.1.native .kdf))
    (result : (LabeledKernel (Fin n) × Option RawCtxSourceSend.Encrypted) ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((send seeds
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup setup.source seeds ideal))
      (PqxdhRecordLiftNativeAdapters.sendSeal (PqxdhRecordLiftWorldCompiler.sendNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec)))) start).run state)) :
    DepthBound result.2.1 (result.2.2.1.1.native .kdf) := by
  cases start with
  | requested pending =>
      simp only [send, StateT.run, mem_support_bind_iff, bind_pure_comp, support_map] at supported
      obtain ⟨looked, lookupSupported, sealed, sealSupported, rfl⟩ := supported
      simpa only [sealing_kdf setup codec _ looked.2.2 sealed sealSupported] using
        logged_lookup_depth setup.source seeds ideal pending.request state bounded refs.1.2 looked lookupSupported
  | exhausted entry context =>
      simp_all only [send, StateT.run, support_pure, Set.mem_singleton_iff]

/-- Every concrete mixed lookup charges exactly one native KDF call, including ideal hits and repeated source callbacks. -/
theorem logged_lookup_kdf (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds (Fin n))
    (ideal : Coordinate (Fin n) → Bool) (coordinate : Coordinate (Fin n))
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (result : PqxdhFullSecretInputKdf.FullOutput ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftLoggedAdapters.liftLookup
      (PqxdhRecordLiftChainOracle.lookup source seeds ideal) coordinate).run state)) :
    result.2.2.1.1.native .kdf = state.2.1.1.native .kdf + 1 := by
  simp only [PqxdhRecordLiftLoggedAdapters.liftLookup, StateT.run, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have exactState := PqxdhRecordLiftChainOracle.lookup_primitive source seeds ideal coordinate
    (state.1, state.2.1) inner member
  simpa only [PqxdhRecordLiftChainOracle.charge, Function.update_self] using
    congrArg (fun primitive => primitive.1.native .kdf) exactState

/-- The unchanged source callback allowance bounds complete receive execution for any operational metric charged once per lookup and not charged by opening. -/
theorem receive_kdf (seeds : Seeds (Fin n)) (lookup : Lookup (Fin n) PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState) (metric : PrimitiveState → Nat)
    (lookupCost : ∀ coordinate state result, result ∈ support ((lookup coordinate).run state) →
      metric result.2.2 ≤ metric state.2 + 1)
    (openingCost : ∀ pending state result, result ∈ support ((opening pending).run state) →
      metric result.2 ≤ metric state)
    (effect : Effect (Fin n) Context) (state : Execution (Fin n) PrimitiveState)
    (result : (LabeledKernel (Fin n) × core.option.Option Plaintext) × Execution (Fin n) PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening effect).run state)) :
    metric result.2.2 ≤ metric state.2 + RawCtxChainReceiveBounds.kdfCost effect := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result
  case h depth ih =>
    cases effect with
    | kdfRequested pending =>
      simp only [StateT.run, receive, mem_support_bind_iff] at supported
      obtain ⟨reply, member, continued⟩ := supported
      have next := ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
        _ reply.2 result continued rfl
      have charged := lookupCost pending.request state reply member
      have decreases := RawCtxChainReceiveBounds.resume_cost pending (advance pending.request 1, pending.request)
      omega
    | openRequested pending =>
      simp only [StateT.run, receive, bind_pure_comp, support_map] at supported
      obtain ⟨reply, member, rfl⟩ := supported
      simpa only [RawCtxChainReceiveBounds.kdfCost, Nat.add_zero] using openingCost _ state.2 reply member
    | rejected entry context =>
      simp_all only [StateT.run, receive, support_pure, Set.mem_singleton_iff,
        RawCtxChainReceiveBounds.kdfCost, Nat.add_zero, le_refl]

/-- The concrete mixed receive charges no more than the actual source's remaining callback allowance; no table-validity or freshness premise is required. -/
theorem mixed_receive_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (effect : Effect (Fin n) RawCtxWholeOwner.OpenContext)
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (result : (LabeledKernel (Fin n) × core.option.Option RawCtxWholeOwner.Decrypted) ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((receive seeds
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup setup.source seeds ideal))
      (PqxdhRecordLiftNativeAdapters.receiveOpen (PqxdhRecordLiftWorldCompiler.receiveNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec)))) effect).run state)) :
    result.2.2.1.1.native .kdf ≤ state.2.1.1.native .kdf + RawCtxChainReceiveBounds.kdfCost effect := by
  exact receive_kdf seeds _ _ (fun primitive => primitive.1.1.native .kdf)
    (fun coordinate before after member => (logged_lookup_kdf setup.source seeds ideal coordinate before after member).le)
    (fun pending before after member => (opening_kdf setup codec pending before after member).le)
    effect state result supported

/-- Every mixed send charges at most one native KDF call, including failed seals/writers; counter exhaustion performs no callback. -/
theorem mixed_send_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (start : Start (Fin n) RawCtxSourceSend.SealContext)
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (result : (LabeledKernel (Fin n) × Option RawCtxSourceSend.Encrypted) ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((send seeds
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup setup.source seeds ideal))
      (PqxdhRecordLiftNativeAdapters.sendSeal (PqxdhRecordLiftWorldCompiler.sendNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec)))) start).run state)) :
    result.2.2.1.1.native .kdf ≤ state.2.1.1.native .kdf + 1 := by
  cases start with
  | requested pending =>
      simp only [send, StateT.run, mem_support_bind_iff, bind_pure_comp, support_map] at supported
      obtain ⟨looked, lookupSupported, sealed, sealSupported, rfl⟩ := supported
      simpa only [sealing_kdf setup codec _ looked.2.2 sealed sealSupported] using
        (logged_lookup_kdf setup.source seeds ideal pending.request state looked lookupSupported).le
  | exhausted entry context =>
      simp_all only [send, StateT.run, support_pure, Set.mem_singleton_iff, Nat.le_add_right]

/-- The literal caller-known receive keeps the same 51-call native KDF cap as hidden mixed execution. -/
theorem known_receive_bound (kernel : ConcreteRatchetKernel) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    (simulateQ RawCtxMixedOwner.receiveAdapter (simulateQ RawCtxWholeOwner.adapter
      (RawCtxOwnerOracle.receive kernel target context))).IsQueryBoundP
        (fun query => RawCtxMixedOwner.callKind query = .kdf) 51 := by
  simp only [RawCtxMixedOwner.receiveAdapter, QueryImpl.simulateQ_compose]
  apply RawCtxMixedOwner.receiveLift_bound
  have bounded := RawCtxKdfBudget.native_receive_bound kernel target context
  simp only [RawCtxSourceOpen.ownerAdapter, QueryImpl.simulateQ_compose] at bounded
  convert bounded using 1
  funext query
  rcases query with request | (bytes | input) <;> simp [RawCtxMixedOwner.receiveKind]

/-- The literal caller-known send has the same one-call KDF cap as hidden mixed execution. -/
theorem known_send_bound (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) :
    (simulateQ RawCtxMixedOwner.sendAdapter (simulateQ RawCtxSourceSend.adapter
      (RawCtxSourceSend.send kernel context))).IsQueryBoundP
        (fun query => RawCtxMixedOwner.callKind query = .kdf) 1 := by
  simp only [RawCtxMixedOwner.sendAdapter, QueryImpl.simulateQ_compose]
  apply RawCtxMixedOwner.sendLift_bound
  convert RawCtxSourceSeal.nativeAdapter_kdf_bound _ 1 (RawCtxSourceSend.selected_bounds kernel context).1 using 1
  funext query
  rcases query with request | (input | (bytes | frame)) <;> simp [RawCtxMixedOwner.sendKind]

/-- Every selected stored receive, caller-known or hidden, has the same source-window cap under the concrete mixed interpreter. -/
theorem kernelReceive_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (stored : PqxdhRecordLiftWorldCompiler.StoredKernel n) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext)
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (result : (PqxdhRecordLiftWorldCompiler.StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftWorldCompiler.kernelReceive seeds
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup setup.source seeds ideal))
      (PqxdhRecordLiftWorldCompiler.receiveNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec)))
      stored target context).run state)) :
    result.2.2.1.1.native .kdf ≤ state.2.1.1.native .kdf + 51 := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftWorldCompiler.kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact (logged_native setup codec _ .kdf 51 (known_receive_bound kernel target context) state.2 inner
        (by simpa only [PqxdhRecordLiftWorldCompiler.receiveNative, QueryImpl.simulateQ_compose, StateT.run] using member)).2
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftWorldCompiler.kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact (mixed_receive_kdf setup codec seeds ideal _ state inner member).trans
        (Nat.add_le_add_left (RawCtxChainReceiveBounds.begin_cost kernel target context) _)

/-- Every selected stored send has the one-call source cap, retaining the actual optional output. -/
theorem kernelSend_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (stored : PqxdhRecordLiftWorldCompiler.StoredKernel n) (context : RawCtxSourceSend.SealContext)
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (result : (PqxdhRecordLiftWorldCompiler.StoredKernel n × Option RawCtxSourceSend.Encrypted) ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftWorldCompiler.kernelSend seeds
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup setup.source seeds ideal))
      (PqxdhRecordLiftWorldCompiler.sendNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec)))
      stored context).run state)) :
    result.2.2.1.1.native .kdf ≤ state.2.1.1.native .kdf + 1 := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftWorldCompiler.kernelSend, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact (logged_native setup codec _ .kdf 1 (known_send_bound kernel context) state.2 inner
        (by simpa only [PqxdhRecordLiftWorldCompiler.sendNative, QueryImpl.simulateQ_compose, StateT.run] using member)).2
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftWorldCompiler.kernelSend, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact mixed_send_kdf setup codec seeds ideal _ state inner member

/-- Complete stored receives preserve finite depth; hidden source references come from the current stored kernel certificate. -/
theorem kernelReceive_depth {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (stored : PqxdhRecordLiftWorldCompiler.StoredKernel n) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext)
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (good : PqxdhRecordLiftChainOracle.Valid setup.source seeds ideal state.1)
    (ready : PqxdhRecordLiftWorldCompiler.StoredReady state.1 stored)
    (bounded : DepthBound state.1 (state.2.1.1.native .kdf))
    (result : (PqxdhRecordLiftWorldCompiler.StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftWorldCompiler.kernelReceive seeds
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup setup.source seeds ideal))
      (PqxdhRecordLiftWorldCompiler.receiveNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec)))
      stored target context).run state)) :
    DepthBound result.2.1 (result.2.2.1.1.native .kdf) := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftWorldCompiler.kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact depth_mono state.1 bounded
        (logged_native setup codec _ .kdf 51 (known_receive_bound kernel target context) state.2 inner
          (by simpa only [PqxdhRecordLiftWorldCompiler.receiveNative, QueryImpl.simulateQ_compose, StateT.run] using member)).1
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftWorldCompiler.kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact mixed_receive_depth setup codec seeds ideal _ state good
        ⟨begin_available state.1 kernel ready.1.1 target context, begin_present state.1 kernel ready.1.2 target context⟩
        bounded inner member

/-- Complete stored sends preserve finite depth, including exhaustion and unsuccessful publication. -/
theorem kernelSend_depth {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (stored : PqxdhRecordLiftWorldCompiler.StoredKernel n) (context : RawCtxSourceSend.SealContext)
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (ready : PqxdhRecordLiftWorldCompiler.StoredReady state.1 stored)
    (bounded : DepthBound state.1 (state.2.1.1.native .kdf))
    (result : (PqxdhRecordLiftWorldCompiler.StoredKernel n × Option RawCtxSourceSend.Encrypted) ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftWorldCompiler.kernelSend seeds
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup setup.source seeds ideal))
      (PqxdhRecordLiftWorldCompiler.sendNative
        (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec)))
      stored context).run state)) :
    DepthBound result.2.1 (result.2.2.1.1.native .kdf) := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftWorldCompiler.kernelSend, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact depth_mono state.1 bounded
        (logged_native setup codec _ .kdf 1 (known_send_bound kernel context) state.2 inner
          (by simpa only [PqxdhRecordLiftWorldCompiler.sendNative, QueryImpl.simulateQ_compose, StateT.run] using member)).1
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftWorldCompiler.kernelSend, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact mixed_send_depth setup codec seeds ideal _ state
        (send_begin_references state.1 kernel ready.1 context) bounded inner member

/-- Dynamic owner dispatch adds at most one KDF for sends or 51 for raw attempts, counting caller-known and hidden records together. -/
theorem ownerStep_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (result : (RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftWorldCompiler.Owner n) ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftWorldCompiler.ownerStep seeds
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup setup.source seeds ideal))
      (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec))
      sender decode query owner).run state)) :
    result.2.2.1.1.native .kdf ≤ state.2.1.1.native .kdf + (if query.isLeft then 1 else 51) := by
  cases query with
  | inl plaintext =>
      simp only [PqxdhRecordLiftWorldCompiler.ownerStep, PqxdhRecordLiftWorldCompiler.ownerSend, StateT.run] at supported
      split_ifs at supported with empty
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        simp only [Sum.isLeft, ite_true, Nat.le_add_right]
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact kernelSend_kdf setup codec seeds ideal owner.kernel _ state inner member
  | inr raw =>
      simp only [PqxdhRecordLiftWorldCompiler.ownerStep, PqxdhRecordLiftWorldCompiler.ownerReceive, StateT.run] at supported
      split at supported
      · simp_all only [support_pure, Set.mem_singleton_iff, Sum.isLeft, Bool.false_eq_true, ite_false, Nat.le_add_right]
      · split at supported
        · simp_all only [support_pure, Set.mem_singleton_iff, Sum.isLeft, Bool.false_eq_true, ite_false, Nat.le_add_right]
        · split at supported
          · simp only [bind_pure_comp, support_map] at supported
            obtain ⟨inner, member, rfl⟩ := supported
            exact kernelReceive_kdf setup codec seeds ideal owner.kernel _ _ state inner member
          · simp_all only [support_pure, Set.mem_singleton_iff, Sum.isLeft, Bool.false_eq_true, ite_false, Nat.le_add_right]

/-- Every actual owner dispatch preserves finite depth using its stored certificate, including parser rejection and rollback. -/
theorem ownerStep_depth {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seeds : Seeds (Fin n)) (ideal : Coordinate (Fin n) → Bool)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (state : Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (good : PqxdhRecordLiftChainOracle.Valid setup.source seeds ideal state.1)
    (ready : PqxdhRecordLiftWorldCompiler.StoredReady state.1 owner.kernel)
    (bounded : DepthBound state.1 (state.2.1.1.native .kdf))
    (result : (RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftWorldCompiler.Owner n) ×
      Execution (Fin n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support ((PqxdhRecordLiftWorldCompiler.ownerStep seeds
      (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup setup.source seeds ideal))
      (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec))
      sender decode query owner).run state)) :
    DepthBound result.2.1 (result.2.2.1.1.native .kdf) := by
  cases query with
  | inl plaintext =>
      simp only [PqxdhRecordLiftWorldCompiler.ownerStep, PqxdhRecordLiftWorldCompiler.ownerSend, StateT.run] at supported
      split_ifs at supported with empty
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact bounded
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact kernelSend_depth setup codec seeds ideal owner.kernel _ state ready bounded inner member
  | inr raw =>
      simp only [PqxdhRecordLiftWorldCompiler.ownerStep, PqxdhRecordLiftWorldCompiler.ownerReceive, StateT.run] at supported
      split at supported
      · simp_all only [support_pure, Set.mem_singleton_iff]
      · split at supported
        · simp_all only [support_pure, Set.mem_singleton_iff]
        · split at supported
          · simp only [bind_pure_comp, support_map] at supported
            obtain ⟨inner, member, rfl⟩ := supported
            exact kernelReceive_depth setup codec seeds ideal owner.kernel _ _ state good ready bounded inner member
          · simp_all only [support_pure, Set.mem_singleton_iff]

end BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.receive_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.receive_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.lookup_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.lookup_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.lookup_writesOnly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.lookup_writesOnly

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.lookup_avoids' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.lookup_avoids

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.native_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.native_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.logged_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.logged_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.receive_open_noKdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.receive_open_noKdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.opening_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.opening_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.logged_lookup_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.logged_lookup_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.mixed_receive_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.mixed_receive_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.send_seal_noKdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.send_seal_noKdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.sealing_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.sealing_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.mixed_send_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.mixed_send_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.logged_lookup_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.logged_lookup_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.receive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.receive_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.mixed_receive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.mixed_receive_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.mixed_send_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.mixed_send_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.known_receive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.known_receive_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.known_send_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.known_send_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.kernelReceive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.kernelReceive_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.kernelSend_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.kernelSend_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.kernelReceive_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.kernelReceive_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.kernelSend_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.kernelSend_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.ownerStep_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.ownerStep_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.ownerStep_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords.ownerStep_depth
