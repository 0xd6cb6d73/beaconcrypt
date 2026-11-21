-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawGuardedJoin
import BeaconcryptCore.Computational.PqxdhDeploymentIdealCut

/-! Before the selected accept, the guarded native interpreter projects to an actual pool prefix. Registration uses its source codec, established records use their independent native codec, and native size refusal stutters on the entire state. The accept ordinal, source backend and seed table follow the original concrete registration prefix. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CborRawNativeCut

open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentBackend (XState RegImpl handlerWith onBase)
open PqxdhDeploymentIdealSteps (IdealBk TableState idealReg)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (PreCut bump withAccepts scanCE scanCE_pure scanCE_accept_zero
  scanCE_accept_succ scanCE_other onBase_base)
open CborRecordNativeAdmission (nativeShell)
open CborRawGuardedJoin (refusal nativeHandler)
variable {ι KemSK Reader Response RecordReader RecordResponse X Bk : Type} {baseSpec : OracleSpec ι} {n : Nat}

section Handlers
variable (setup : Setup baseSpec KemSK) (sourceCodec : Codec Reader Response)
  (recordCodec : Codec RecordReader RecordResponse) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)

noncomputable def poolBase (seed : PqxdhJointIdentity.IdentitySeed)
    (pool : List (PqxdhLiveKemReservation.Pair KemSK)) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) := fun query =>
  if CborSplitCompiler.recordCommand query then PqxdhDeploymentNative.handler setup recordCodec checks route seed query
  else PqxdhDeploymentIdealPool.deploymentPool setup sourceCodec checks route seed pool query

noncomputable def poolHandler (seed : PqxdhJointIdentity.IdentitySeed)
    (pool : List (PqxdhLiveKemReservation.Pair KemSK)) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) := fun query state =>
  match refusal (n := n) query (nativeShell state) with
  | some reply => pure (reply, state)
  | none => (poolBase setup sourceCodec recordCodec checks route seed pool query).run state

theorem nonrecord_handler (reg : RegImpl KemSK Bk n) (query : Spec.Domain)
    (other : CborSplitCompiler.recordCommand query = false) :
    handlerWith setup recordCodec route reg query = handlerWith setup sourceCodec route reg query := by
  rcases query with coin | command
  · rfl
  · cases command <;> first | rfl | simp [CborSplitCompiler.recordCommand] at other

theorem record_handler (seed : PqxdhJointIdentity.IdentitySeed) (reg : RegImpl KemSK Bk n) (query : Spec.Domain)
    (record : CborSplitCompiler.recordCommand query = true) :
    handlerWith setup recordCodec route reg query =
      onBase (PqxdhDeploymentNative.handler setup recordCodec checks route seed query) := by
  rcases query with coin | command
  · simp [CborSplitCompiler.recordCommand] at record
  · cases command <;> first | rfl | simp [CborSplitCompiler.recordCommand] at record

theorem record_bump (query : Spec.Domain) (backend : IdealBk TableState)
    (record : CborSplitCompiler.recordCommand query = true) : bump query backend = backend := by
  rcases query with coin | command
  · rfl
  · cases command <;> first | rfl | simp [CborSplitCompiler.recordCommand] at record

theorem refusal_bump (query : Spec.Domain) (shell : CborRecordWorldClient.Shell)
    (reply : Spec.Range query) (backend : IdealBk TableState)
    (refused : refusal (n := n) query shell = some reply) : bump query backend = backend := by
  rcases query with coin | command
  · rfl
  · cases command with
    | accept raw =>
        change (none : Option (Option Nat)) = some reply at refused
        cases refused
    | _ => rfl

variable {count : Nat} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

theorem preStep (query : Spec.Domain) (state : XState KemSK (IdealBk TableState) 2) (pre : PreCut state)
    (notSelected : ∀ raw, query = .inr (.accept raw) → state.backend.2.2.accepts ≠ t.accept) :
    Prod.map id XState.base <$>
        (nativeHandler setup recordCodec route (idealReg setup sourceCodec route checks t p created) query).run state =
      (poolHandler (n := 2) setup sourceCodec recordCodec checks route created.seed (p.pool t) query).run state.base ∧
      ∀ result ∈ support
          ((nativeHandler setup recordCodec route (idealReg setup sourceCodec route checks t p created) query).run state),
        result.2.backend = bump query state.backend ∧ result.2.seeds = state.seeds := by
  cases refused : refusal (n := 2) query (nativeShell state.base) with
  | some reply =>
      refine ⟨by simp only [nativeHandler, poolHandler, StateT.run, refused, map_pure, Prod.map_apply, id_eq], ?_⟩
      intro result supported
      simp only [nativeHandler, StateT.run, refused, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨(refusal_bump query (nativeShell state.base) reply state.backend refused).symm, rfl⟩
  | none =>
      have unguarded : Prod.map id XState.base <$>
          (handlerWith setup recordCodec route (idealReg setup sourceCodec route checks t p created) query).run state =
            (poolBase setup sourceCodec recordCodec checks route created.seed (p.pool t) query).run state.base ∧
          ∀ result ∈ support
              ((handlerWith setup recordCodec route (idealReg setup sourceCodec route checks t p created) query).run state),
            result.2.backend = bump query state.backend ∧ result.2.seeds = state.seeds := by
        cases record : CborSplitCompiler.recordCommand query with
        | false =>
            simpa only [nonrecord_handler setup sourceCodec recordCodec route _ query record,
              poolBase, record, Bool.false_eq_true, ite_false] using
              PqxdhDeploymentIdealCut.preStep setup sourceCodec route checks t p created query state pre notSelected
        | true =>
            rw [record_handler setup recordCodec checks route created.seed _ query record]
            simpa only [poolBase, record, ite_true, record_bump query state.backend record] using
              onBase_base (PqxdhDeploymentNative.handler setup recordCodec checks route created.seed query) state
      simpa only [nativeHandler, poolHandler, StateT.run, refused] using unguarded

theorem preScan (work : OracleComp Spec X) (index : ℕ) (x : XState KemSK (IdealBk TableState) 2) (pre : PreCut x)
    (room : x.backend.2.2.accepts + index ≤ t.accept) :
    Prod.map id XState.base <$>
        (simulateQ (nativeHandler setup recordCodec route (idealReg setup sourceCodec route checks t p created))
          (scanCE work index)).run x =
      (simulateQ (poolHandler (n := 2) setup sourceCodec recordCodec checks route created.seed (p.pool t)) (scanCE work index)).run x.base ∧
      ∀ result ∈ support ((simulateQ (nativeHandler setup recordCodec route (idealReg setup sourceCodec route checks t p created))
          (scanCE work index)).run x),
        ∃ accepts, result.2.backend = withAccepts x.backend accepts ∧ result.2.seeds = x.seeds ∧
          ∀ raw next, result.1 = .pending raw next → accepts = x.backend.2.2.accepts + index := by
  induction work using OracleComp.inductionOn generalizing index x with
  | pure value =>
      rw [scanCE_pure]
      refine ⟨by simp, ?_⟩
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨x.backend.2.2.accepts, rfl, rfl, fun _ _ impossible => by cases impossible⟩
  | query_bind query next ih =>
      by_cases accept : PqxdhDeploymentCompileBudget.commandKind query = 3
      · rcases query with coin | command
        · exact absurd accept (by simp [PqxdhDeploymentCompileBudget.commandKind])
        · cases command with
          | accept raw =>
              cases index with
              | zero =>
                  rw [scanCE_accept_zero]
                  refine ⟨by simp, ?_⟩
                  intro result member
                  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
                  subst member
                  exact ⟨x.backend.2.2.accepts, rfl, rfl, fun _ _ _ => rfl⟩
              | succ index =>
                  have other : x.backend.2.2.accepts ≠ t.accept := by omega
                  have step := preStep setup sourceCodec recordCodec checks route t p created (.inr (.accept raw)) x pre
                    (fun _ same => by cases same; exact other)
                  rw [scanCE_accept_succ]
                  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
                  refine ⟨?_, ?_⟩
                  · rw [map_bind, ← step.1, bind_map_left]
                    refine bind_congr_of_forall_mem_support _ fun reached member => ?_
                    obtain ⟨backend, seeds⟩ := step.2 reached member
                    have reachedPre : PreCut reached.2 := by
                      simp only [PreCut, backend, bump]
                      exact pre
                    have reachedRoom : reached.2.backend.2.2.accepts + index ≤ t.accept := by
                      simp only [backend, bump]
                      omega
                    exact (ih reached.1 index reached.2 reachedPre reachedRoom).1
                  · intro result member
                    rw [mem_support_bind_iff] at member
                    obtain ⟨reached, reachedMember, member⟩ := member
                    obtain ⟨backend, seeds⟩ := step.2 reached reachedMember
                    have reachedPre : PreCut reached.2 := by
                      simp only [PreCut, backend, bump]
                      exact pre
                    have reachedRoom : reached.2.backend.2.2.accepts + index ≤ t.accept := by
                      simp only [backend, bump]
                      omega
                    obtain ⟨accepts, resultBackend, resultSeeds, pending⟩ :=
                      (ih reached.1 index reached.2 reachedPre reachedRoom).2 result member
                    refine ⟨accepts, ?_, resultSeeds.trans seeds, fun raw' next' cut => ?_⟩
                    · rw [resultBackend, backend]
                      rfl
                    · rw [pending raw' next' cut, backend]
                      simp only [bump]
                      omega
          | _ => exact absurd accept (by simp [PqxdhDeploymentCompileBudget.commandKind])
      · have step := preStep setup sourceCodec recordCodec checks route t p created query x pre
          (fun raw same => by subst same; exact absurd rfl accept)
        have kept : bump query x.backend = x.backend := by
          rcases query with coin | command
          · rfl
          · cases command with
            | accept raw => exact absurd rfl accept
            | _ => rfl
        rw [scanCE_other query accept]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        refine ⟨?_, ?_⟩
        · rw [map_bind, ← step.1, bind_map_left]
          refine bind_congr_of_forall_mem_support _ fun reached member => ?_
          obtain ⟨backend, seeds⟩ := step.2 reached member
          rw [kept] at backend
          have reachedPre : PreCut reached.2 := by
            simp only [PreCut, backend]
            exact pre
          exact (ih reached.1 index reached.2 reachedPre (by rw [backend]; exact room)).1
        · intro result member
          rw [mem_support_bind_iff] at member
          obtain ⟨reached, reachedMember, member⟩ := member
          obtain ⟨backend, seeds⟩ := step.2 reached reachedMember
          rw [kept] at backend
          have reachedPre : PreCut reached.2 := by
            simp only [PreCut, backend]
            exact pre
          obtain ⟨accepts, resultBackend, resultSeeds, pending⟩ :=
            (ih reached.1 index reached.2 reachedPre (by rw [backend]; exact room)).2 result member
          exact ⟨accepts, by rw [resultBackend, backend], resultSeeds.trans seeds,
            fun raw next cut => by rw [pending raw next cut, backend]⟩


end Handlers
end BeaconcryptCore.Computational.CborRawNativeCut

/-- info: 'BeaconcryptCore.Computational.CborRawNativeCut.nonrecord_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativeCut.nonrecord_handler
/-- info: 'BeaconcryptCore.Computational.CborRawNativeCut.record_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativeCut.record_handler
/-- info: 'BeaconcryptCore.Computational.CborRawNativeCut.record_bump' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativeCut.record_bump
/-- info: 'BeaconcryptCore.Computational.CborRawNativeCut.refusal_bump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativeCut.refusal_bump
/-- info: 'BeaconcryptCore.Computational.CborRawNativeCut.preStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativeCut.preStep

/-- info: 'BeaconcryptCore.Computational.CborRawNativeCut.preScan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativeCut.preScan
