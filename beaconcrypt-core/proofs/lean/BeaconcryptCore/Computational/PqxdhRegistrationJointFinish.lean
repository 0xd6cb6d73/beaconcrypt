-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleCosts

/-! Full native Beacon finish with private service histories and the same shared primitive state. The existing restricted Extract and shared classical CTX/BLAKE2b ROM idealizations are retained; this representation adds no security assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointFinish
open PqxdhRefinement PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointPreparation (Pool)
open PqxdhRegistrationJointBundle (Identity Key encode identityMap keyMap)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

abbrev State (KemSK : Type) := Pool KemSK × NativeState KemSK
abbrev Spec (Response : Type) := PqxdhBeaconPhase2Publication.NativeSpec Identity ScalarBytes Key Nat Response
abbrev NativeSpec (KemSK Response : Type) := PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
  (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response

def onPool (work : StateT (Pool KemSK) ProbComp Result) : StateT (State KemSK) ProbComp Result :=
  fun state => (fun result => (result.1, (result.2, state.2))) <$> work state.1

def onNative (work : NativeGame KemSK Result) : StateT (State KemSK) ProbComp Result :=
  fun state => (fun result => (result.1, (state.1, result.2))) <$> work state.2

/-- Only preparation uses private services; the whole root, initialization and raw receive tail keeps the original shared native interpreter. -/
noncomputable def callbacks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (Spec Response) (StateT (State KemSK) ProbComp)
  | .inl query => onPool (PqxdhRegistrationJointPreparation.interpreted setup codec query)
  | .inr query => onNative (sourceBeaconTail setup codec query)

/-- The original source program gains only private service-reply histories; no original cache or native result is replaced. -/
noncomputable def annotated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) : QueryImpl (NativeSpec KemSK Response) (StateT (State KemSK) ProbComp)
  | .inl query => onPool (PqxdhRegistrationJointPreparation.annotated setup codec identityIndex kemIndex query)
  | .inr query => onNative (sourceBeaconTail setup codec query)

/-- Mapping the owner's private representation commutes with both terminal abort and successful native publication. -/
theorem finish_map (setup : Setup baseSpec KemSK) (identityIndex kemIndex : Nat)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    PqxdhBeaconPhase2Publication.finish control (encode setup identityIndex kemIndex owner) staged =
      ((PqxdhBeaconPhase2Publication.finish control owner staged).1,
        encode setup identityIndex kemIndex (PqxdhBeaconPhase2Publication.finish control owner staged).2) := by
  cases staged <;> simp only [PqxdhBeaconPhase2Publication.finish, encode,
    PqxdhBeaconPhase1Publication.mapState, PqxdhBeaconPhase2Preparation.abort,
    PqxdhBeaconPhase1Publication.mapPhase, PqxdhBeaconPhase2Publication.publish]
  split_ifs <;> simp_all

private theorem onPool_run (work : StateT (Pool KemSK) ProbComp Result) (state : State KemSK) :
    (onPool work).run state = (fun result => (result.1, (result.2, state.2))) <$> work.run state.1 := rfl

/-- Lifting a complete preparation program preserves the untouched native coordinate and the entire private service result. -/
theorem pool_program {κ : Type} {spec : OracleSpec κ}
    (handler : QueryImpl spec (StateT (Pool KemSK) ProbComp)) (program : OracleComp spec Result)
    (state : State KemSK) :
    (simulateQ (fun query => onPool (handler query)) program).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (simulateQ handler program).run state.1 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, onPool_run,
        bind_map_left, ih, map_bind]

private theorem onNative_run (work : NativeGame KemSK Result) (state : State KemSK) :
    (onNative work).run state = (fun result => (result.1, (state.1, result.2))) <$> work.run state.2 := rfl

/-- The complete original tail updates its actual shared state while leaving both entire private service histories intact. -/
theorem native_program {κ : Type} {spec : OracleSpec κ}
    (handler : QueryImpl spec (NativeGame KemSK)) (program : OracleComp spec Result)
    (state : State KemSK) :
    (simulateQ (fun query => onNative (handler query)) program).run state =
      (fun result => (result.1, (state.1, result.2))) <$> (simulateQ handler program).run state.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, onNative_run,
        bind_map_left, ih, map_bind]

/-- An evaluated view of the original owner, separating only its existing preparation and tail callback alphabets. -/
noncomputable def run {I D K X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (pre : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (tail : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) m)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State I D K) : m (Option Pqxdh.Bytes × PqxdhBeaconPhase2Preparation.State I D K) :=
  match owner.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ pre (PqxdhBeaconPhase2Preparation.prepare control owner.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (PqxdhBeaconPhase2Publication.finish control owner none)
      | some prepared => do
          let staged ← simulateQ tail (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
            (PqxdhBeaconPhase2Publication.tail decode prepared))
          pure (PqxdhBeaconPhase2Publication.finish control owner staged)
  | _ => pure (none, owner)

/-- The evaluated view is the literal whole native owner for every lawful effect monad, with no state or failure-path projection. -/
theorem native_run {I D K X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response) m)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State I D K) :
    simulateQ handler (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner) =
      run (fun query => handler (.inl query)) (fun query => handler (.inr query)) decode raw owner := by
  have pre : (handler ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ PqxdhBeaconPhase2Publication.preLift =
      fun query => handler (.inl query) := by
    funext query
    exact (simulateQ_spec_query (handler ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) (.inl query)).trans
      (simulateQ_spec_query handler (.inl query))
  have tailLift : handler ∘ₛ PqxdhBeaconPhase2Publication.nativeTailLift = fun query => handler (.inr query) := by
    funext query
    exact simulateQ_spec_query handler (.inr query)
  have tail : (handler ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ PqxdhBeaconPhase2Publication.tailLift =
      (fun query => handler (.inr query)) ∘ₛ PqxdhBeaconPhase2Publication.nativeTailAdapter := by
    funext query
    refine (simulateQ_spec_query (handler ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) (.inr query)).trans ?_
    change simulateQ handler (simulateQ PqxdhBeaconPhase2Publication.nativeTailLift
      (PqxdhBeaconPhase2Publication.nativeTailAdapter query)) = _
    rw [← QueryImpl.simulateQ_compose, tailLift]
    rfl
  unfold PqxdhBeaconPhase2Publication.nativeOwner
  rw [← QueryImpl.simulateQ_compose]
  cases phase : owner.beacon.phase <;> simp only [PqxdhBeaconPhase2Publication.owner, run, phase,
    simulateQ_bind, simulateQ_pure, ← QueryImpl.simulateQ_compose, pre]
  apply bind_congr
  intro prepared
  cases prepared <;> simp only [simulateQ_pure, simulateQ_bind, ← QueryImpl.simulateQ_compose, tail]

/-- The complete native owner is represented by the indexed client on every phase. The exact active KEM slot and identity slot are local representation conditions, not origin or authentication premises. -/
theorem owner_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys) :
    (simulateQ (callbacks setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw (encode setup identityIndex kemIndex owner))).run state =
      (fun result => ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) <$>
        (simulateQ (annotated setup codec identityIndex kemIndex)
          (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state := by
  rw [native_run, native_run]
  have mappedPhase : (encode setup identityIndex kemIndex owner).beacon.phase =
      PqxdhBeaconPhase1Publication.mapPhase (keyMap kemIndex) owner.beacon.phase := rfl
  cases phase : owner.beacon.phase <;> simp only [run, mappedPhase, phase,
    PqxdhBeaconPhase1Publication.mapPhase, StateT.run_pure, map_pure]
  simp only [callbacks, annotated, StateT.run_bind, pool_program, bind_map_left, map_bind]
  rw [show (encode setup identityIndex kemIndex owner).beacon.identity =
    identityMap setup identityIndex owner.beacon.identity from rfl]
  rw [PqxdhRegistrationJointPreparation.prepare_source setup codec identityIndex kemIndex
    owner.beacon.identity _ _ _ _ raw state.1 identityOwned (kemOwned _ _ _ _ phase)]
  apply bind_congr
  rintro ⟨_ | prepared, pool⟩
  all_goals simp only [StateT.run_pure, map_pure, finish_map, bind_pure_comp,
    StateT.run_map, Functor.map_map]

/-- Forgetting private service histories preserves the original callback's whole native result and state, including cache effects on failure. -/
theorem annotated_query_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (query : (NativeSpec KemSK Response).Domain) (state : State KemSK) :
    (fun result => (result.1, result.2.2)) <$> (annotated setup codec identityIndex kemIndex query).run state =
      (PqxdhRegistrationSchedule.callbacks setup codec query).run state.2 := by
  cases query with
  | inl query =>
      simp only [annotated, onPool_run, Functor.map_map]
      change (fun result => (result.1, state.2)) <$>
        (PqxdhRegistrationJointPreparation.annotated setup codec identityIndex kemIndex query).run state.1 = _
      have equality := congrArg (fun work => (fun reply => (reply, state.2)) <$> work)
        (PqxdhRegistrationJointPreparation.annotated_query_erase setup codec identityIndex kemIndex query state.1)
      simp only [Functor.map_map, PqxdhRegistrationSchedule.callbacks, nativeCoins, StateT.run] at equality ⊢
      exact equality
  | inr query =>
      simp only [annotated, onNative_run, PqxdhRegistrationSchedule.callbacks, Functor.map_map]
      exact id_map _

/-- Every adaptive original native program retains the same optional results and complete shared state after dropping only the private analysis pools. -/
theorem annotated_program_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (program : OracleComp (NativeSpec KemSK Response) Result) (state : State KemSK) :
    (fun result => (result.1, result.2.2)) <$>
      (simulateQ (annotated setup codec identityIndex kemIndex) program).run state =
        (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec) program).run state.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simpa only [bind_map_left] using congrArg
        (fun work => work >>= fun reply =>
          (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec) (next reply.1)).run reply.2)
        (annotated_query_erase setup codec identityIndex kemIndex query state)

/-- Projecting the indexed owner's whole execution recovers the literal native owner with only its private representation mapped. -/
theorem owner_original (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys) :
    (fun result => (result.1, result.2.2)) <$>
      (simulateQ (callbacks setup codec)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw (encode setup identityIndex kemIndex owner))).run state =
      (fun result => ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) <$>
        (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
          (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state.2 := by
  rw [owner_source setup codec identityIndex kemIndex owner raw state identityOwned kemOwned]
  have erased := congrArg (fun work =>
    (fun result => ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) <$> work)
    (annotated_program_erase setup codec identityIndex kemIndex
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner) state)
  simpa only [Functor.map_map] using erased

/-- A present public owner slot executes the same annotated native owner and reinstalls precisely its returned state, preserving every other owner and both actual shared caches. -/
theorem finish_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ownerAddress identityIndex kemIndex : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK) (pool : Pool KemSK)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : state.owners[ownerAddress]? = some owner) :
    (PqxdhRegistrationSchedule.finish setup codec ownerAddress raw).run state =
      (fun result => (result.1.1,
        ({ shared := result.2.2, owners := state.owners.set ownerAddress result.1.2 } : PqxdhRegistrationSchedule.State KemSK))) <$>
      (simulateQ (annotated setup codec identityIndex kemIndex)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run (pool, state.shared) := by
  rw [show (PqxdhRegistrationSchedule.finish setup codec ownerAddress raw).run state =
    PqxdhRegistrationSchedule.finish setup codec ownerAddress raw state from rfl,
    PqxdhRegistrationSchedule.finish_source setup codec ownerAddress raw state owner found]
  rw [← annotated_program_erase setup codec identityIndex kemIndex
    (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner) (pool, state.shared), Functor.map_map]

/-- Any full source continuation receives the exact public reply, all reinstalled owners and complete shared state from the same annotated execution. -/
theorem finish_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ownerAddress identityIndex kemIndex : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK) (pool : Pool KemSK)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : state.owners[ownerAddress]? = some owner)
    (next : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State KemSK → ProbComp Result) :
    ((PqxdhRegistrationSchedule.finish setup codec ownerAddress raw).run state >>= next) =
      ((simulateQ (annotated setup codec identityIndex kemIndex)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run (pool, state.shared) >>= fun result =>
          next (result.1.1, { shared := result.2.2, owners := state.owners.set ownerAddress result.1.2 })) := by
  rw [finish_source setup codec ownerAddress identityIndex kemIndex raw state pool owner found, bind_map_left]

/-- The indexed client equality retains any continuation on its complete mapped owner, private service pools and native shared poststate. -/
theorem owner_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys)
    (next : (Option Pqxdh.Bytes × PqxdhRegistrationJointBundle.Owner) × State KemSK → ProbComp Result) :
    ((simulateQ (callbacks setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw (encode setup identityIndex kemIndex owner))).run state >>= next) =
      ((simulateQ (annotated setup codec identityIndex kemIndex)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state >>= fun result =>
          next ((result.1.1, encode setup identityIndex kemIndex result.1.2), result.2)) := by
  rw [owner_source setup codec identityIndex kemIndex owner raw state identityOwned kemOwned, bind_map_left]

/-- Native preparation and tail callbacks preserve every private service slot; only actual service histories and primitive caches may change. -/
theorem annotated_query_slots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (query : (NativeSpec KemSK Response).Domain) (state : State KemSK)
    (result : (NativeSpec KemSK Response).Range query × State KemSK)
    (supported : result ∈ support ((annotated setup codec identityIndex kemIndex query).run state)) :
    result.2.1.1.seeds = state.1.1.seeds ∧ result.2.1.2.keys = state.1.2.keys := by
  cases query with
  | inl query =>
      simp only [annotated, onPool_run, support_map, Set.mem_image] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      exact PqxdhRegistrationJointPreparation.annotated_query_slots setup codec identityIndex kemIndex query state.1 reply reached
  | inr query =>
      simp only [annotated, onNative_run, support_map, Set.mem_image] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      exact ⟨rfl, rfl⟩

/-- Every adaptive annotated native program preserves the complete private slot lists, including failure paths and arbitrary original tail effects. -/
theorem annotated_program_slots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (program : OracleComp (NativeSpec KemSK Response) Result) (state : State KemSK)
    (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (annotated setup codec identityIndex kemIndex) program).run state)) :
    result.2.1.1.seeds = state.1.1.seeds ∧ result.2.1.2.keys = state.1.2.keys := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, rest⟩ := supported
      have head := annotated_query_slots setup codec identityIndex kemIndex query state middle first
      have tail := ih middle.1 middle.2 result rest
      exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩

/-- Annotation preserves every selective bound on the underlying uniform interface for any adaptive native program; no original computation is removed from the bill. -/
theorem annotated_program_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (program : OracleComp (NativeSpec KemSK Response) Result) (state : State KemSK)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (annotated setup codec identityIndex kemIndex) program).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ (PqxdhRegistrationSchedule.callbacks setup codec) program).run state.2).IsQueryBoundP predicate budget := by
  rw [← annotated_program_erase setup codec identityIndex kemIndex program state, isQueryBoundP_map_iff]

/-- The actual indexed whole owner inherits the complete original uniform budget, including all KEM/base work and every root/hash cache sample before rejection. -/
theorem owner_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (raw : Pqxdh.Bytes) (state : State KemSK)
    (identityOwned : state.1.1.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      state.1.2.keys[kemIndex]? = some keys) :
    ((simulateQ (callbacks setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw (encode setup identityIndex kemIndex owner))).run state).IsTotalQueryBound
      (69 * max 64 (caps.decapsUniform + caps.baseUniform * caps.decapsBase)) := by
  rw [owner_source setup codec identityIndex kemIndex owner raw state identityOwned kemOwned,
    IsTotalQueryBound, isQueryBound_map_iff]
  exact (isQueryBoundP_true_iff _ _).mp
    ((annotated_program_queries setup codec identityIndex kemIndex
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner) state (fun _ => True) _).mpr
        (PqxdhRegistrationSchedule.owner_uniform setup codec caps bounded raw owner state.2).isQueryBoundP)

end BeaconcryptCore.Computational.PqxdhRegistrationJointFinish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.finish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.finish_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.pool_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.pool_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.native_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.native_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.owner_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.annotated_query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.annotated_query_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.annotated_program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.annotated_program_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.owner_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.owner_original

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.finish_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.finish_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.owner_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.owner_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.annotated_query_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.annotated_query_slots

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.annotated_program_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.annotated_program_slots

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.annotated_program_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.annotated_program_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.owner_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinish.owner_uniform
