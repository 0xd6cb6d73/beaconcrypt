-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStageTraceCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource
/-! The public all-attempt bundle cut reaches the exact first-issued callback in the original complete private source execution. Only the analysis journal and an exact operational counter law are used; no message freshness, owner eligibility or security event is assumed. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativeIdentityCensorBundlePrefix (Cut stop resume)
variable {A S : Type}

private def cost : TypedSpec.Domain → Nat
  | .inr (.bundle _) => 1
  | _ => 0

private noncomputable def counted (implementation : QueryImpl TypedSpec (StateT S ProbComp)) :
    QueryImpl TypedSpec (StateT (S × Nat) ProbComp) := fun query before =>
  (fun result => (result.1,(result.2,before.2+cost query))) <$> (implementation query).run before.1

private def Status (position : Nat) : Cut A → Nat → Prop
  | .returned _, cursor => cursor ≤ position
  | .bundle _ _, cursor => cursor = position

private theorem stop_pure (position cursor : Nat) (value : A) : stop position (pure value) cursor = pure (.returned value) := rfl
private theorem stop_step (position cursor : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) :
    stop position (TypedSpec.query query >>= next) cursor =
      (match query with
      | .inr (.bundle value) =>
          if cursor = position then pure (.bundle value next)
          else do let reply ← TypedSpec.query (.inr (.bundle value)); stop position (next reply) (cursor+1)
      | query => do let reply ← TypedSpec.query query; stop position (next reply) cursor) := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

/-- A returned bundle cut has exactly the original counted ordinal; a fully returned client has not passed it. -/
private theorem progress (position cursor : Nat) (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (work : OracleComp TypedSpec A) (before : S) (within : cursor ≤ position)
    (result : Cut A × (S × Nat))
    (supported : result ∈ support ((simulateQ (counted implementation) (stop position work cursor)).run (before,cursor))) :
    Status position result.1 result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before cursor result with
  | pure value =>
      simp only [stop_pure,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact within
  | query_bind query next ih =>
      have forward (bump : Nat) (charged : cost query = bump) (room : cursor+bump ≤ position)
          (reached : result ∈ support ((simulateQ (counted implementation)
            (TypedSpec.query query >>= fun reply => stop position (next reply) (cursor+bump))).run (before,cursor))) :
          Status position result.1 result.2.2 := by
        rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at reached
        obtain ⟨middle,called,continued⟩ := reached
        simp only [counted,StateT.run,support_map] at called
        obtain ⟨actual,_called,rfl⟩ := called
        exact ih actual.1 (cursor+bump) actual.2 room result (by simpa only [charged] using continued)
      rw [stop_step] at supported
      cases query with
      | inl coin => exact forward 0 rfl (by omega) supported
      | inr command =>
          cases command
          case bundle value =>
            by_cases chosen : cursor = position
            · simp only [chosen,ite_true,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
              cases supported
              rfl
            · simp only [chosen,ite_false] at supported
              exact forward 1 rfl (by omega) supported
          all_goals exact forward 0 rfl (by omega) supported

/-- Forgetting the counter preserves the complete original private source execution and its exact poststate. -/
private theorem erase (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (before : S × Nat) :
    Prod.map id Prod.fst <$> (simulateQ (counted implementation) work).run before =
      (simulateQ implementation work).run before.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [counted,StateT.run,Functor.map_map,Prod.map,id_eq]
  exact id_map _


private def count (calls : List (Call TypedSpec S)) : Nat := (calls.map fun call => cost call.query).sum

private theorem count_step (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (query : TypedSpec.Domain) (before : (S × List (Call TypedSpec S)) × Nat)
    (prior : before.2 = count before.1.2)
    (result : TypedSpec.Range query × ((S × List (Call TypedSpec S)) × Nat))
    (supported : result ∈ support ((counted (RegistrationNativeStageTrace.handler implementation) query).run before)) :
    result.2.2 = count result.2.1.2 := by
  simp only [counted,RegistrationNativeStageTrace.handler,StateT.run,Functor.map_map,support_map] at supported
  obtain ⟨actual,_called,rfl⟩ := supported
  rw [prior]
  simp [count]

/-- The analysis counter is literally the journal's number of parsed position attempts in the same supported execution. -/
private theorem counted_trace (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (before : (S × List (Call TypedSpec S)) × Nat) (prior : before.2 = count before.1.2)
    (result : A × ((S × List (Call TypedSpec S)) × Nat))
    (supported : result ∈ support ((simulateQ (counted (RegistrationNativeStageTrace.handler implementation)) work).run before)) :
    result.2.2 = count result.2.1.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle _ (fun current => current.2 = count current.1.2)
    (count_step implementation) work before prior result supported

/-- The original source journal at the stopped prefix has exactly the same public ordinal status, with no caller counter or chronology premise. -/
private theorem prefix_status (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (position : Nat)
    (work : OracleComp TypedSpec A) (before : S)
    (result : Cut A × (S × List (Call TypedSpec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation)
      (stop position work 0)).run (before,[]))) :
    Status position result.1 (count result.2.2) := by
  rw [←erase
    (RegistrationNativeStageTrace.handler implementation) _ ((before,[]),0),support_map] at supported
  obtain ⟨full,reached,same⟩ := supported
  cases same
  have numeric := progress position 0
    (RegistrationNativeStageTrace.handler implementation) work (before,[]) (Nat.zero_le _) full reached
  have recorded := counted_trace implementation (stop position work 0)
    ((before,[]),0) rfl full reached
  change Status position full.1 (count full.2.1.2)
  rw [←recorded]
  exact numeric


private def bundles (calls : List (Call TypedSpec S)) : List (Call TypedSpec S) :=
  calls.filter fun call => match call.query with
    | .inr (.bundle _) => true
    | _ => false

private theorem bundles_length (calls : List (Call TypedSpec S)) : (bundles calls).length = count calls := by
  induction calls with
  | nil => rfl
  | cons call rest ih =>
    cases query : call.query with
    | inl coin => simp_all [bundles,count,cost]
    | inr command =>
      cases command <;> simp_all [bundles,count,cost]
      omega

private theorem bundles_at (leading trailing : List (Call TypedSpec S)) (call : Call TypedSpec S)
    (index : Nat) (queryEq : call.query = .inr (.bundle index)) :
    (bundles (leading ++ call :: trailing))[count leading]? = some call := by
  have appended : bundles (leading ++ call :: trailing) = bundles leading ++ call :: bundles trailing := by
    simp [bundles,queryEq]
  rw [appended,←bundles_length leading,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
  rfl

private theorem resumed_first (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec S)) (result : A × (S × List (Call TypedSpec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation)
      (resume (.bundle index next))).run (before,leading))) :
    ∃ call trailing, result.2.2 = leading ++ call :: trailing ∧
      call.query = .inr (.bundle index) ∧ call.before = before ∧
      RegistrationNativeStageTrace.Executed implementation call ∧ Path implementation call.after trailing result.2.1 := by
  rw [resume,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩ := supported
  simp only [RegistrationNativeStageTrace.handler,StateT.run,support_map] at called
  obtain ⟨actual,executed,rfl⟩ := called
  obtain ⟨trailing,same,following⟩ := RegistrationNativeIdentityUnissuedCutTrace.extension implementation (next actual.1) actual.2 _ result continued
  refine ⟨⟨.inr (.bundle index),before,actual.1,actual.2⟩,trailing,?_,rfl,rfl,executed,following⟩
  rw [same,List.append_assoc]
  rfl

/-- The counter law is an operational per-query equality, including rejected and failed bundle attempts. -/
def ClockLaw (clock : S → Nat) (implementation : QueryImpl TypedSpec (StateT S ProbComp)) : Prop :=
  ∀ query before (result : TypedSpec.Range query × S), result ∈ support ((implementation query).run before) →
    clock result.2 = clock before + cost query

private theorem path_clock (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (clock : S → Nat) (law : ClockLaw clock implementation)
    {before after : S} {calls : List (Call TypedSpec S)} (actual : Path implementation before calls after) :
    clock after = clock before + count calls := by
  induction actual with
  | nil => simp [count]
  | cons call called rest last following ih =>
    have step := law call.query call.before (call.reply,call.after) called
    rw [ih,step]
    simp only [count,List.map_cons,List.sum_cons]
    omega

private noncomputable def coupled (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (position : Nat) (work : OracleComp TypedSpec A) (before : S) :
    ProbComp ((Cut A × (S × List (Call TypedSpec S))) × (A × (S × List (Call TypedSpec S)))) := do
  let cut ← (simulateQ (RegistrationNativeStageTrace.handler implementation) (stop position work 0)).run (before,[])
  let result ← (simulateQ (RegistrationNativeStageTrace.handler implementation) (resume cut.1)).run cut.2
  pure (cut,result)

private theorem full_marginal (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (position : Nat) (work : OracleComp TypedSpec A) (before : S) :
    Prod.snd <$> coupled implementation position work before =
      (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,[]) := by
  simp only [coupled,map_bind,map_pure,bind_pure]
  exact (RegistrationNativeIdentityCensorBundlePrefix.execution position 0
    (RegistrationNativeStageTrace.handler implementation) work (before,[])).symm


/-- In the same prefix/resumption coupling, the original receipt identifies THIS cut, rather than merely some supported cutoff. This pointwise form is suitable for probability transport through the original full execution. -/
theorem at_cut (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (clock : S → Nat) (law : ClockLaw clock implementation)
    (position : Nat) (work : OracleComp TypedSpec A) (before : S) (initial : clock before = 0)
    (cut : Cut A × (S × List (Call TypedSpec S)))
    (cutReached : cut ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) (stop position work 0)).run (before,[])))
    (result : A × (S × List (Call TypedSpec S)))
    (continued : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) (resume cut.1)).run cut.2))
    (call : Call TypedSpec S) (member : call ∈ result.2.2)
    (index : Nat) (queryEq : call.query = .inr (.bundle index)) (ordinal : clock call.before = position) :
    ∃ next, cut.1 = Cut.bundle index next ∧ cut.2.1 = call.before := by
  have supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,[])) := by
    rw [RegistrationNativeIdentityCensorBundlePrefix.execution position 0 (RegistrationNativeStageTrace.handler implementation) work (before,[])]
    rw [mem_support_bind_iff]
    exact ⟨cut,cutReached,continued⟩
  have actual := RegistrationNativeStageTrace.path implementation work before result supported
  obtain ⟨leading,trailing,split,prior,_called,_following⟩ := actual.member call member
  have ticks := path_clock implementation clock law prior
  have nth : (bundles result.2.2)[position]? = some call := by
    have counted : count leading = position := by omega
    rw [split,←counted]
    exact bundles_at leading trailing call index queryEq
  have status := prefix_status implementation position work before cut cutReached
  rcases cut with ⟨cut,current,calls⟩
  cases cut with
  | returned value =>
    simp only [resume,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
    cases continued
    have length : (bundles calls).length ≤ position := by
      rw [bundles_length]
      exact status
    rw [List.getElem?_eq_none (by omega)] at nth
    cases nth
  | bundle selected next =>
    obtain ⟨chosen,trailing,sameLog,chosenQuery,chosenBefore,_executed,_following⟩ :=
      resumed_first implementation selected next current calls result continued
    have chosenNth : (bundles result.2.2)[position]? = some chosen := by
      rw [sameLog,←status]
      exact bundles_at calls trailing chosen selected chosenQuery
    have chosenSame : chosen = call := Option.some.inj (chosenNth.symm.trans nth)
    subst chosen
    have sameIndex : selected = index := by
      simpa only [Sum.inr.injEq,RegistrationNativeRawAdapter.Command.bundle.injEq] using chosenQuery.symm.trans queryEq
    subst selected
    exact ⟨next,rfl,chosenBefore.symm⟩

private theorem count_cons (head : Call TypedSpec S) (tail : List (Call TypedSpec S)) :
    count (head::tail)=cost head.query+count tail := by
  simp only [count,List.map_cons,List.sum_cons]

private theorem same_prefix (left right : List (Call TypedSpec S)) (call other : Call TypedSpec S)
    (tail rest : List (Call TypedSpec S)) (same : left++call::tail=right++other::rest)
    (equal : count left=count right) (positive : cost call.query=1) (otherPositive : cost other.query=1) : left=right := by
  induction left generalizing right with
  | nil=>
    cases right with
    | nil=>rfl
    | cons head later=>
      have headEq : call=head := (List.cons.inj same).1
      have charged : cost head.query=1 := headEq ▸ positive
      change 0=count (head::later) at equal
      rw [count_cons,charged] at equal
      omega
  | cons head later ih=>
    cases right with
    | nil=>
      have headEq : head=other := (List.cons.inj same).1
      have charged : cost head.query=1 := headEq ▸ otherPositive
      change count (head::later)=0 at equal
      rw [count_cons,charged] at equal
      omega
    | cons first following=>
      obtain ⟨headEq,tailEq⟩ := List.cons.inj same
      subst first
      rw [count_cons,count_cons] at equal
      rw [ih following tailEq (Nat.add_left_cancel equal)]

/-- The same selected all-attempt cutoff retains the exact original chronological journal prefix, including every non-bundle callback. No private-state injectivity is used. -/
theorem at_cut_journal (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (clock : S → Nat) (law : ClockLaw clock implementation)
    (position : Nat) (work : OracleComp TypedSpec A) (before : S) (initial : clock before=0)
    (cut : Cut A × (S × List (Call TypedSpec S)))
    (cutReached : cut∈support ((simulateQ (RegistrationNativeStageTrace.handler implementation) (stop position work 0)).run (before,[])))
    (result : A × (S × List (Call TypedSpec S)))
    (continued : result∈support ((simulateQ (RegistrationNativeStageTrace.handler implementation) (resume cut.1)).run cut.2))
    (leading trailing : List (Call TypedSpec S)) (call : Call TypedSpec S)
    (split : result.2.2=leading++call::trailing) (index : Nat)
    (queryEq : call.query=.inr (.bundle index)) (ordinal : clock call.before=position) :
    ∃next,cut.1=Cut.bundle index next ∧ cut.2.1=call.before ∧ cut.2.2=leading := by
  have member : call∈result.2.2 := by rw [split];simp only [List.mem_append,List.mem_cons_self,or_true]
  obtain ⟨next,kind,atState⟩ := at_cut implementation clock law position work before initial cut cutReached result continued call member index queryEq ordinal
  have supported : result∈support ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,[])) := by
    rw [RegistrationNativeIdentityCensorBundlePrefix.execution position 0 (RegistrationNativeStageTrace.handler implementation) work (before,[]),mem_support_bind_iff]
    exact ⟨cut,cutReached,continued⟩
  have actual := RegistrationNativeStageTrace.path implementation work before result supported
  rw [split] at actual
  obtain ⟨prior,_called,_following⟩ := RegistrationNativeStageTraceCut.split implementation leading trailing call actual
  have ticks := path_clock implementation clock law prior
  have countLeading : count leading=position := by omega
  have status := prefix_status implementation position work before cut cutReached
  rw [kind] at status
  have resumed := continued
  rw [kind] at resumed
  obtain ⟨chosen,rest,sameLog,chosenQuery,_chosenBefore,_executed,_later⟩ := resumed_first implementation index next cut.2.1 cut.2.2 result resumed
  have prefixEq : leading=cut.2.2 := same_prefix leading cut.2.2 call chosen trailing rest (split.symm.trans sameLog)
    (countLeading.trans status.symm) (by rw [queryEq];rfl) (by rw [chosenQuery];rfl)
  exact ⟨next,kind,atState,prefixEq.symm⟩

/-- A bundle in the original full journal has a supported cutoff at its exact before-state and the same original continuation. Failed bundle attempts contribute to its public ordinal. The complete original final result and journal remain supported after resumption. -/
theorem original (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (clock : S → Nat) (law : ClockLaw clock implementation)
    (work : OracleComp TypedSpec A) (before : S) (initial : clock before = 0)
    (result : A × (S × List (Call TypedSpec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,[])))
    (call : Call TypedSpec S) (member : call ∈ result.2.2)
    (index position : Nat) (queryEq : call.query = .inr (.bundle index)) (ordinal : clock call.before = position) :
    ∃ next leading,
      (Cut.bundle index next,(call.before,leading)) ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation)
        (stop position work 0)).run (before,[])) ∧
      result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation)
        (resume (Cut.bundle index next))).run (call.before,leading)) := by
  have actual := RegistrationNativeStageTrace.path implementation work before result supported
  obtain ⟨leading,trailing,split,prior,_called,_following⟩ := actual.member call member
  have ticks := path_clock implementation clock law prior
  have nth : (bundles result.2.2)[position]? = some call := by
    have counted : count leading = position := by omega
    rw [split,←counted]
    exact bundles_at leading trailing call index queryEq
  rw [←full_marginal implementation position work before,support_map] at supported
  obtain ⟨paired,reached,same⟩ := supported
  simp only [coupled,mem_support_bind_iff,mem_support_pure_iff] at reached
  obtain ⟨cut,cutReached,final,continued,rfl⟩ := reached
  change final = result at same
  subst final
  have status := prefix_status implementation position work before cut cutReached
  rcases cut with ⟨cut,current,calls⟩
  cases cut with
  | returned value =>
    simp only [resume,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
    cases continued
    have length : (bundles calls).length ≤ position := by
      rw [bundles_length]
      exact status
    rw [List.getElem?_eq_none (by omega)] at nth
    cases nth
  | bundle selected next =>
    obtain ⟨chosen,trailing,sameLog,chosenQuery,chosenBefore,_executed,_following⟩ :=
      resumed_first implementation selected next current calls result continued
    have chosenNth : (bundles result.2.2)[position]? = some chosen := by
      rw [sameLog,←status]
      exact bundles_at calls trailing chosen selected chosenQuery
    have chosenSame : chosen = call := Option.some.inj (chosenNth.symm.trans nth)
    subst chosen
    have sameIndex : selected = index := by
      simpa only [Sum.inr.injEq,RegistrationNativeRawAdapter.Command.bundle.injEq] using chosenQuery.symm.trans queryEq
    subst selected
    subst current
    exact ⟨next,calls,cutReached,continued⟩

/-- In the literal CTX source with its all-attempt signing trace, the operational counter law is derived internally. The original receipt's same-state public cut includes every failed bundle and preserves the original suffix. -/
theorem signed (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (work : OracleComp TypedSpec A)
    (before : (S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State)
    (initial : before.1.2.nextBundle = 0)
    (result : A × (((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State) ×
      List (Call TypedSpec ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State))))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
      (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)) work).run (before,[])))
    (call : Call TypedSpec ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State))
    (member : call ∈ result.2.2) (index position : Nat)
    (queryEq : call.query = .inr (.bundle index)) (ordinal : call.before.1.2.nextBundle = position) :
    ∃ next leading,
      (Cut.bundle index next,(call.before,leading)) ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
        (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)) (stop position work 0)).run (before,[])) ∧
      result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
        (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend))
        (resume (Cut.bundle index next))).run (call.before,leading)) := by
  apply original (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)
    (fun current => current.1.2.nextBundle) _ work before initial result supported call member index position queryEq ordinal
  intro query current returned reached
  rw [RegistrationNativePlatformIdentityCtxSigningSource.typedHandler,QueryImpl.Stateful.link_impl_apply_run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  have counted := RegistrationNativePlatformIdentityCtxSigningTrace.query_counter frontend query current.1 inner.1
    (by
      apply support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation joint) _ current.2
      rw [StateT.run'_eq,support_map]
      exact ⟨inner,called,rfl⟩)
  change inner.1.2.2.nextBundle = current.1.2.nextBundle + cost query
  cases query with
  | inl coin => exact counted
  | inr command => cases command <;> exact counted

/-- The same pointwise coupling receipt for the actual CTX signing source derives its all-attempt counter law internally. No desired event correspondence or selected-history premise is supplied. -/
theorem signed_at_cut (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (position : Nat) (work : OracleComp TypedSpec A)
    (before : (S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State)
    (initial : before.1.2.nextBundle = 0)
    (cut : Cut A × (((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State) ×
      List (Call TypedSpec ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State))))
    (cutReached : cut ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
      (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)) (stop position work 0)).run (before,[])))
    (result : A × (((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State) ×
      List (Call TypedSpec ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State))))
    (continued : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
      (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)) (resume cut.1)).run cut.2))
    (call : Call TypedSpec ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State))
    (member : call ∈ result.2.2) (index : Nat)
    (queryEq : call.query = .inr (.bundle index)) (ordinal : call.before.1.2.nextBundle = position) :
    ∃ next, cut.1 = Cut.bundle index next ∧ cut.2.1 = call.before := by
  apply at_cut (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)
    (fun current => current.1.2.nextBundle) _ position work before initial cut cutReached result continued call member index queryEq ordinal
  intro query current returned reached
  rw [RegistrationNativePlatformIdentityCtxSigningSource.typedHandler,QueryImpl.Stateful.link_impl_apply_run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  have counted := RegistrationNativePlatformIdentityCtxSigningTrace.query_counter frontend query current.1 inner.1
    (by
      apply support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation joint) _ current.2
      rw [StateT.run'_eq,support_map]
      exact ⟨inner,called,rfl⟩)
  change inner.1.2.2.nextBundle = current.1.2.nextBundle + cost query
  cases query with
  | inl coin => exact counted
  | inr command => cases command <;> exact counted

/-- The same pointwise coupling receipt for the actual CTX signing source derives its all-attempt counter law internally. No desired event correspondence or selected-history premise is supplied. -/
theorem signed_at_cut_journal (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (position : Nat) (work : OracleComp TypedSpec A)
    (before : (S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State)
    (initial : before.1.2.nextBundle = 0)
    (cut : Cut A × (((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State) ×
      List (Call TypedSpec ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State))))
    (cutReached : cut ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
      (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)) (stop position work 0)).run (before,[])))
    (result : A × (((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State) ×
      List (Call TypedSpec ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State))))
    (continued : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
      (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)) (resume cut.1)).run cut.2))
    (call : Call TypedSpec ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State))
    (leading trailing : List (Call TypedSpec ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State)))
    (split : result.2.2=leading++call::trailing) (index : Nat)
    (queryEq : call.query = .inr (.bundle index)) (ordinal : call.before.1.2.nextBundle = position) :
    ∃ next, cut.1 = Cut.bundle index next ∧ cut.2.1 = call.before ∧ cut.2.2=leading := by
  apply at_cut_journal (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend)
    (fun current => current.1.2.nextBundle) _ position work before initial cut cutReached result continued leading trailing call split index queryEq ordinal
  intro query current returned reached
  rw [RegistrationNativePlatformIdentityCtxSigningSource.typedHandler,QueryImpl.Stateful.link_impl_apply_run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  have counted := RegistrationNativePlatformIdentityCtxSigningTrace.query_counter frontend query current.1 inner.1
    (by
      apply support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation joint) _ current.2
      rw [StateT.run'_eq,support_map]
      exact ⟨inner,called,rfl⟩)
  change inner.1.2.2.nextBundle = current.1.2.nextBundle + cost query
  cases query with
  | inl coin => exact counted
  | inr command => cases command <;> exact counted

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.signed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.at_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.at_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.signed_at_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.signed_at_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.at_cut_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.at_cut_journal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.signed_at_cut_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt.signed_at_cut_journal
