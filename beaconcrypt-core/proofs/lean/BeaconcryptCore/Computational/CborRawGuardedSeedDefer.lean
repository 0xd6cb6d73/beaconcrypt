-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawGuardedSeedMove

/-! The first-touch hidden seeds can be deferred to their actual installs under native raw admission. Refused sends preserve the complete state, ordinary fixed steps retain the private allocator/seed invariant, and cursor admission is independent of seed-cache completion. The concrete ideal instance discharges these facts from the existing real slot services. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawGuardedSeedDefer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhRecordLiftInterface (EnvQuery Slot)
open PqxdhDeploymentBackend (XState RegImpl seedLens)
open PqxdhDeploymentIdealDefer (PointedSeeds completeList)
open PqxdhDeploymentSeedSplit (seedFree seedFree_set)
open LazyOracleDiscard (Commutes LawEq)
variable {ι KemSK Reader Response Bk Result : Type} {baseSpec : OracleSpec ι} {n : Nat}
section Defer
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

noncomputable def pointed {inv : XState KemSK Bk n → Prop} (pair : PointedSeeds inv) :
    (query : Spec.Domain) → StateT (XState KemSK Bk n) ProbComp (Spec.Range query × List (Slot n))
  | .inr (.create pin keyId) => pair.pointed ⟨.create pin keyId, trivial⟩
  | .inr (.bundle owner) => pair.pointed ⟨.bundle owner, trivial⟩
  | .inr (.accept raw) => pair.pointed ⟨.accept raw, trivial⟩
  | .inr (.build session payload) => pair.pointed ⟨.build session payload, trivial⟩
  | .inr (.finish owner raw) => pair.pointed ⟨.finish owner raw, trivial⟩
  | .inr (.hmac key message) => pair.pointed ⟨.hmac key message, trivial⟩
  | query => (·, []) <$> CborRawGuardedJoin.nativeHandler setup codec route pair.reg query

private theorem pointed_env {inv : XState KemSK Bk n → Prop} (pair : PointedSeeds inv) (query : EnvQuery) :
    pointed setup codec route pair (.inr query.val) = pair.pointed query := by
  rcases query with ⟨command, valid⟩
  cases command
  all_goals first | rfl | exact absurd valid id

private theorem pointed_fixed {inv : XState KemSK Bk n → Prop} (pair : PointedSeeds inv) (query : Spec.Domain)
    (notEnv : ∀ command : EnvQuery, query ≠ .inr command.val) :
    pointed setup codec route pair query = (·, []) <$> CborRawGuardedJoin.nativeHandler setup codec route pair.reg query := by
  rcases query with coin | command
  · rfl
  · cases command
    case create pin keyId => exact absurd rfl (notEnv ⟨.create pin keyId, trivial⟩)
    case bundle owner => exact absurd rfl (notEnv ⟨.bundle owner, trivial⟩)
    case accept raw => exact absurd rfl (notEnv ⟨.accept raw, trivial⟩)
    case build session payload => exact absurd rfl (notEnv ⟨.build session payload, trivial⟩)
    case finish owner raw => exact absurd rfl (notEnv ⟨.finish owner raw, trivial⟩)
    case hmac key message => exact absurd rfl (notEnv ⟨.hmac key message, trivial⟩)
    all_goals rfl

private theorem fixed_reg (left right : RegImpl KemSK Bk n) (query : Spec.Domain)
    (notEnv : ∀ command : EnvQuery, query ≠ .inr command.val) :
    CborRawGuardedJoin.nativeHandler setup codec route left query =
      CborRawGuardedJoin.nativeHandler setup codec route right query := by
  rcases query with coin | command
  · rfl
  · cases command
    case create pin keyId => exact absurd rfl (notEnv ⟨.create pin keyId, trivial⟩)
    case bundle owner => exact absurd rfl (notEnv ⟨.bundle owner, trivial⟩)
    case accept raw => exact absurd rfl (notEnv ⟨.accept raw, trivial⟩)
    case build session payload => exact absurd rfl (notEnv ⟨.build session payload, trivial⟩)
    case finish owner raw => exact absurd rfl (notEnv ⟨.finish owner raw, trivial⟩)
    case hmac key message => exact absurd rfl (notEnv ⟨.hmac key message, trivial⟩)
    all_goals rfl

private theorem erased {inv : XState KemSK Bk n → Prop} (pair : PointedSeeds inv) :
    (fun query => Prod.fst <$> pointed setup codec route pair query : QueryImpl Spec _) =
      CborRawGuardedJoin.nativeHandler setup codec route pair.erased := by
  funext query
  by_cases registration : ∃ command : EnvQuery, query = .inr command.val
  · obtain ⟨command, rfl⟩ := registration
    rw [pointed_env, CborRawGuardedRepresentation.native_env]
    rfl
  · rw [pointed_fixed setup codec route pair query (fun command same => registration ⟨command, same⟩), Functor.map_map]
    simpa only [id_map'] using fixed_reg setup codec route pair.reg pair.erased query
      (fun command same => registration ⟨command, same⟩)

private theorem factor {inv : XState KemSK Bk n → Prop} (pair : PointedSeeds inv) (query : Spec.Domain)
    (state : XState KemSK Bk n) (holds : inv state) :
    LawEq ((CborRawGuardedJoin.nativeHandler setup codec route pair.reg query).run state)
      ((pointed setup codec route pair query).run state >>= fun value =>
        (value.1.1, ·) <$> completeList seedLens value.1.2 value.2) := by
  by_cases registration : ∃ command : EnvQuery, query = .inr command.val
  · obtain ⟨command, rfl⟩ := registration
    rw [CborRawGuardedRepresentation.native_env, pointed_env]
    exact pair.factor command state holds
  · rw [pointed_fixed setup codec route pair query (fun command same => registration ⟨command, same⟩)]
    apply LawEq.of_eq
    simp only [StateT.run_map, bind_map_left, completeList, map_pure, Prod.mk.eta, bind_pure]

private theorem fixed_commutes (reg : RegImpl KemSK Bk n) (query : Spec.Domain)
    (notEnv : ∀ command : EnvQuery, query ≠ .inr command.val) :
    Commutes seedLens (CborRawGuardedJoin.nativeHandler setup codec route reg query) := by
  let choose : Option (Spec.Range query) → StateT (XState KemSK Bk n) ProbComp (Spec.Range query) := fun value =>
    match value with
    | some reply => pure reply
    | none => PqxdhDeploymentBackend.handlerWith setup codec route reg query
  apply PqxdhDeploymentBackend.commutes_dispatch seedLens _
    (fun state => CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state.base))
    (fun _ _ => rfl) choose
  · intro state
    cases refused : CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state.base) <;>
      simp only [CborRawGuardedJoin.nativeHandler, StateT.run, refused, choose]; rfl
  · intro value
    cases value with
    | some reply => exact LazyOracleDiscard.commutes_pure seedLens reply
    | none => exact PqxdhDeploymentBackend.fixed_commute_seed setup codec route reg query notEnv

private theorem oblivious {inv : XState KemSK Bk n → Prop} (pair : PointedSeeds inv) (query : Spec.Domain) :
    Commutes seedLens (Prod.fst <$> pointed setup codec route pair query) := by
  by_cases registration : ∃ command : EnvQuery, query = .inr command.val
  · obtain ⟨command, rfl⟩ := registration
    rw [pointed_env]
    exact pair.oblivious command
  · rw [pointed_fixed setup codec route pair query (fun command same => registration ⟨command, same⟩), Functor.map_map]
    simpa only [id_map'] using fixed_commutes setup codec route pair.reg query
      (fun command same => registration ⟨command, same⟩)

/-- Every adaptive guarded native client admits the same concrete hidden-seed deferral under the stated internal allocator invariant. -/
theorem defer_run (inv : XState KemSK Bk n → Prop) (pair : PointedSeeds inv)
    (fixedKeeps : ∀ query, (∀ command : EnvQuery, query ≠ .inr command.val) → ∀ state, inv state →
      ∀ value ∈ support ((CborRawGuardedJoin.nativeHandler setup codec route pair.reg query).run state), inv value.2)
    (work : OracleComp Spec Result) (state : XState KemSK Bk n) (holds : inv state) :
    LawEq (Prod.map id seedFree <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup codec route pair.reg) work).run state)
      (Prod.map id seedFree <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup codec route pair.erased) work).run state) := by
  have result := PqxdhDeploymentIdealDefer.discard_erase_list seedLens inv
    (CborRawGuardedJoin.nativeHandler setup codec route pair.reg) (pointed setup codec route pair)
    (factor setup codec route pair) ?kept (oblivious setup codec route pair)
    (fun value : Result × XState KemSK Bk n => pure (value.1, seedFree value.2))
    (LazyOracleDiscard.blind_proj seedLens seedFree seedFree_set) work state holds
  case kept =>
    intro query current valid value supported
    by_cases registration : ∃ command : EnvQuery, query = .inr command.val
    · obtain ⟨command, rfl⟩ := registration
      rw [pointed_env] at supported
      exact pair.keeps command current valid value supported
    · rw [pointed_fixed setup codec route pair query (fun command same => registration ⟨command, same⟩),
        StateT.run_map, bind_map_left] at supported
      simp only [completeList, map_pure, Prod.mk.eta, bind_pure] at supported
      exact fixedKeeps query (fun command same => registration ⟨command, same⟩) current valid value supported
  rw [erased] at result
  simpa only [map_eq_bind_pure_comp, Function.comp_def, Prod.map, id_eq] using result

end Defer
section Ideal
open PqxdhDeploymentIdealParams (Target Params)
variable {SourceReader SourceResponse : Type}

/-- Actual eager-to-lazy hidden-seed deferral under independent codecs and native admission, from the concrete valid initial allocator. -/
theorem ideal_defer (setup : Setup baseSpec KemSK) (recordCodec : Codec Reader Response)
    (sourceCodec : Codec SourceReader SourceResponse) (route : RawCtxServerRouting.SenderDecoder) (checks : Checks)
    {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Result) :
    LawEq (Prod.map id seedFree <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup recordCodec route
          (PqxdhDeploymentIdealKernel.idealSplitEager setup sourceCodec route checks target parameters created)) work).run
          (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created)))
      (Prod.map id seedFree <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup recordCodec route
          (PqxdhDeploymentIdealDefer.idealSplit setup sourceCodec route checks target parameters created)) work).run
          (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created))) := by
  have result := defer_run setup recordCodec route PqxdhDeploymentIdealDefer.InvX
    (PqxdhDeploymentIdealDefer.splitSeeds setup sourceCodec route checks target parameters created) ?fixed work
    (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created))
    (PqxdhDeploymentIdealDefer.initial_invX created)
  case fixed =>
    intro query notEnv state valid value supported
    simp only [CborRawGuardedJoin.nativeHandler, StateT.run] at supported
    cases refused : CborRawGuardedJoin.refusal (n := 2) query (CborRecordNativeAdmission.nativeShell state.base) with
    | some reply =>
        rw [refused, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact valid
    | none =>
        rw [refused] at supported
        exact PqxdhDeploymentIdealDefer.fixed_invX setup recordCodec route _ query notEnv state valid value supported
  have original : (PqxdhDeploymentIdealDefer.splitSeeds setup sourceCodec route checks target parameters created).reg =
      PqxdhDeploymentIdealKernel.idealSplitEager setup sourceCodec route checks target parameters created := rfl
  simpa only [original, PqxdhDeploymentIdealDefer.splitSeeds_erased] using result

end Ideal
end BeaconcryptCore.Computational.CborRawGuardedSeedDefer

/-- info: 'BeaconcryptCore.Computational.CborRawGuardedSeedDefer.defer_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedSeedDefer.defer_run
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedSeedDefer.ideal_defer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedSeedDefer.ideal_defer
