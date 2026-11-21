-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleRetainedJournal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold
import BeaconcryptCore.Computational.LazyOracleDiscard
/-! A public before-b split and the whole before-a traversal retain the same positive bundle receipt. Unused failed guesses are integrated out by losslessness. The chosen callback may carry a joint private selector receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeIdentityCensorBundlePrefix (Cut stop)
open RegistrationNativeIdentityCensorPacketClient (Found)
open LazyOracleDiscard (LawEq)
variable {S View A B : Type}
variable (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (observe : S → View)
variable (target : S → Option Pqxdh.Bytes)
variable (published : (query : TypedSpec.Domain) → TypedSpec.Range query → S → Bool)
variable (sample : (index : Nat) → S → ProbComp (B × (TypedSpec.Range (.inr (.bundle index)) × S)))
abbrev Mark (A S View : Type) := Cut A × (S × List (Call TypedSpec View))
abbrev Receipt (A S View B : Type) := Mark A S View × B × (RustM (Option Pqxdh.Bytes) × S) × Found
abbrev count (leading : List (Call TypedSpec View)) := RegistrationNativeIdentityCensorVisitorFold.count leading
private def charge (query : TypedSpec.Domain) : Nat := if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0
private theorem count_next (leading : List (Call TypedSpec View)) (query : TypedSpec.Domain) (before after : View) (reply : TypedSpec.Range query) :
    count (leading++[⟨query,before,reply,after⟩])=count leading+charge query := by
  simp only [count,RegistrationNativeIdentityCensorVisitorFold.count,RegistrationNativeIdentityUnissuedCutTrace.count,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  congr 1
  cases query with
  | inl coin=>rfl
  | inr command=>cases command <;> rfl

noncomputable def positive (accept index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec View)) : ProbComp (Option (Receipt A S View B)) := do
  let result ← sample index before
  if published (.inr (.bundle index)) result.2.1 result.2.2 then pure none else
    (fun found=>found.map (fun found=>((Cut.bundle index next,(before,leading)),result.1,result.2,found))) <$>
      RegistrationNativeIdentityCensorVisitorJournal.visit implementation target published accept (next result.2.1) result.2.2 (count leading)

noncomputable def split (position accept : Nat) (work : OracleComp TypedSpec A) (before : S)
    (leading : List (Call TypedSpec View)) (cursor : Nat) : ProbComp (Option (Receipt A S View B)) := do
  let mark ← (simulateQ (RegistrationNativeObservedStageTrace.handler observe implementation) (stop position work cursor)).run (before,leading)
  match mark.1 with
  | .returned _=>pure none
  | .bundle index next=>positive implementation target published sample accept index next mark.2.1 mark.2.2

noncomputable def collect (position accept : Nat) (work : OracleComp TypedSpec A) :
    S → List (Call TypedSpec View) → Nat → ProbComp (Option (Receipt A S View B)) :=
  work.recOn (fun _ _before _leading _cursor=>pure none)
    (fun query next continued before leading cursor=>
      match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query (count leading) with
      | some _packet=>pure none
      | none=>match query with
        | .inr (.bundle index)=>if cursor=position then positive implementation target published sample accept index next before leading else do
            let result←(implementation (.inr (.bundle index))).run before
            continued result.1 result.2 (leading++[⟨.inr (.bundle index),observe before,result.1,observe result.2⟩]) (cursor+1)
        | query=>do
            let result←(implementation query).run before
            continued result.1 result.2 (leading++[⟨query,observe before,result.1,observe result.2⟩]) cursor)

private theorem stop_step (position cursor : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) :
    stop position (TypedSpec.query query >>= next) cursor =
      (match query with
      | .inr (.bundle index)=>if cursor=position then pure (.bundle index next) else do
          let reply←TypedSpec.query (.inr (.bundle index));stop position (next reply) (cursor+1)
      | query=>do let reply←TypedSpec.query query;stop position (next reply) cursor) := by
  cases query with
  | inl coin=>rfl
  | inr command=>cases command <;> rfl

private theorem split_pure (position accept cursor : Nat) (value : A) (before : S) (leading : List (Call TypedSpec View)) :
    split implementation observe target published sample position accept (pure value) before leading cursor=pure none := rfl

private theorem bind_apply {X Y T : Type} (work : StateT T ProbComp X) (next : X → StateT T ProbComp Y) (before : T) :
    (work >>=next) before=(do let result←work before;next result.1 result.2) := rfl

private theorem split_step (position accept cursor : Nat) (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec View)) :
    split implementation observe target published sample position accept (TypedSpec.query query >>=next) before leading cursor=
      (match query with
      | .inr (.bundle index)=>if cursor=position then positive implementation target published sample accept index next before leading else do
          let result←(implementation (.inr (.bundle index))).run before
          split implementation observe target published sample position accept (next result.1) result.2
            (leading++[⟨.inr (.bundle index),observe before,result.1,observe result.2⟩]) (cursor+1)
      | query=>do
          let result←(implementation query).run before
          split implementation observe target published sample position accept (next result.1) result.2
            (leading++[⟨query,observe before,result.1,observe result.2⟩]) cursor) := by
  unfold split
  rw [stop_step]
  cases query with
  | inl coin=>simp only [simulateQ_bind,simulateQ_spec_query,StateT.run,bind_apply,RegistrationNativeObservedStageTrace.handler,bind_map_left,bind_assoc]
  | inr command=>
    cases command
    case bundle index=>
      by_cases chosen : cursor=position
      · simp only [chosen,ite_true,simulateQ_pure,StateT.run_pure,pure_bind]
      · simp only [chosen,ite_false,simulateQ_bind,simulateQ_spec_query,StateT.run,bind_apply,RegistrationNativeObservedStageTrace.handler,bind_map_left,bind_assoc]
    all_goals simp only [simulateQ_bind,simulateQ_spec_query,StateT.run,bind_apply,RegistrationNativeObservedStageTrace.handler,bind_map_left,bind_assoc]

private theorem visit_late (accept cursor : Nat) (work : OracleComp TypedSpec A) (before : S) (late : accept<cursor) :
    LawEq (RegistrationNativeIdentityCensorVisitorJournal.visit implementation target published accept work before cursor) (pure none) := by
  induction work using OracleComp.inductionOn generalizing before cursor with
  | pure value=>exact .refl _
  | query_bind query next ih=>
    have missing : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor=none := by
      cases query with
      | inl coin=>rfl
      | inr command=>cases command with
        | accept packet=>simp only [RegistrationNativeIdentityCensorAdaptivePostselection.attempt,show cursor≠accept by omega,ite_false]
        | _=>rfl
    change LawEq (match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor with
      | some packet=>pure ((target before).map (fun message=>(message,packet)))
      | none=>do
          let result←(implementation query).run before
          if published query result.1 result.2 then pure none else
            RegistrationNativeIdentityCensorVisitorJournal.visit implementation target published accept (next result.1) result.2 (cursor+charge query)) (pure none)
    rw [missing]
    refine (LawEq.bind (.refl _) (fun result=>?_)).trans (LazyOracleDiscard.lawEq_drop _ (pure none))
    split
    · exact .refl _
    · exact ih result.1 _ result.2 (by omega)

private theorem positive_late (accept index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec View)) (late : accept<count leading) :
    LawEq (positive implementation target published sample accept index next before leading) (pure none) := by
  unfold positive
  refine (LawEq.bind (.refl _) (fun result=>?_)).trans (LazyOracleDiscard.lawEq_drop _ (pure none))
  split
  · exact .refl _
  · have law := (visit_late implementation target published accept (count leading) (next result.2.1) result.2.2 late).map
        (fun found=>found.map (fun found=>((Cut.bundle index next,(before,leading)),result.1,result.2,found)))
    simpa only [map_pure,Option.map_none] using law

private theorem split_late (position accept cursor : Nat) (work : OracleComp TypedSpec A) (before : S)
    (leading : List (Call TypedSpec View)) (late : accept<count leading) :
    LawEq (split implementation observe target published sample position accept work before leading cursor) (pure none) := by
  induction work using OracleComp.inductionOn generalizing before leading cursor with
  | pure value=>rw [split_pure];exact .refl _
  | query_bind query next ih=>
    rw [split_step]
    have continued : ∀ result : TypedSpec.Range query × S, ∀ nextCursor,
        LawEq (split implementation observe target published sample position accept (next result.1) result.2
          (leading++[⟨query,observe before,result.1,observe result.2⟩]) nextCursor) (pure none) := by
      intro result nextCursor
      apply ih
      rw [count_next]
      omega
    cases query with
    | inl coin=>exact (LawEq.bind (.refl _) (fun result=>continued result _)).trans (LazyOracleDiscard.lawEq_drop _ (pure none))
    | inr command=>
      cases command <;> first
      | exact (LawEq.bind (.refl _) (fun result=>continued result _)).trans (LazyOracleDiscard.lawEq_drop _ (pure none))
      | by_cases chosen : cursor=position
        · simp only [chosen,ite_true]
          exact positive_late implementation target published sample accept _ _ before leading late
        · simp only [chosen,ite_false]
          exact (LawEq.bind (.refl _) (fun result=>continued result _)).trans (LazyOracleDiscard.lawEq_drop _ (pure none))


/-- The exact original next continuation is retained by the before-accept recorder. -/
theorem collect_step (position accept cursor : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : S) (leading : List (Call TypedSpec View)) :
    collect implementation observe target published sample position accept (TypedSpec.query query >>=next) before leading cursor=
      (match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query (count leading) with
      | some _packet=>pure none
      | none=>match query,next with
        | .inr (.bundle index),next=>if cursor=position then positive implementation target published sample accept index next before leading else do
            let result←(implementation (.inr (.bundle index))).run before
            collect implementation observe target published sample position accept (next result.1) result.2
              (leading++[⟨.inr (.bundle index),observe before,result.1,observe result.2⟩]) (cursor+1)
        | query,next=>do
            let result←(implementation query).run before
            collect implementation observe target published sample position accept (next result.1) result.2
              (leading++[⟨query,observe before,result.1,observe result.2⟩]) cursor) := by
  cases query with
  | inl coin=>rfl
  | inr command=>cases command <;> rfl

private theorem law_bind_supported {X Y : Type} (draw : ProbComp X) {left right : X → ProbComp Y}
    (same : ∀ value∈support draw,LawEq (left value) (right value)) : LawEq (draw >>=left) (draw >>=right) := by
  intro T _ next
  simp only [bind_assoc]
  exact evalDist_bind_congr_of_support draw _ _ (fun value reached=>same value reached T next)

/-- Operational callback facts suffice for the exact whole-traversal law. No success, freshness or candidate conclusion is a hypothesis. -/
theorem source (ordinal : S → Nat) (position accept : Nat)
    (unarmed : ∀ (query : TypedSpec.Domain) (before : S), target before=none →
      (∀ index,query=.inr (.bundle index) → ordinal before≠position) →
      ∀ result∈support ((implementation query).run before),
        ordinal result.2=ordinal before+(if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query then 1 else 0) ∧ target result.2=none)
    (work : OracleComp TypedSpec A) (before : S) (leading : List (Call TypedSpec View)) (cursor : Nat)
    (counter : ordinal before=cursor) (missing : target before=none) :
    LawEq (split implementation observe target published sample position accept work before leading cursor)
      (collect implementation observe target published sample position accept work before leading cursor) := by
  induction work using OracleComp.inductionOn generalizing before leading cursor with
  | pure value=>rw [split_pure];exact .refl _
  | query_bind query next ih=>
    rw [split_step]
    rw [collect_step]
    cases attempted : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query (count leading) with
    | some packet=>
      cases query with
      | inl coin=>cases attempted
      | inr command=>
        cases command <;> try cases attempted
        rename_i submitted
        have chosen : count leading=accept := by
          by_contra different
          simp only [RegistrationNativeIdentityCensorAdaptivePostselection.attempt,different,ite_false] at attempted
          cases attempted
        refine (LawEq.bind (.refl _) (fun result=>?_)).trans (LazyOracleDiscard.lawEq_drop _ (pure none))
        apply split_late
        rw [count_next,chosen]
        change accept<accept+1
        omega
    | none=>
      have continued (different : ∀ index,query=.inr (.bundle index) → cursor≠position) (nextCursor : Nat)
          (nextCount : nextCursor=cursor+(if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query then 1 else 0)) :
          LawEq (do
            let result←(implementation query).run before
            split implementation observe target published sample position accept (next result.1) result.2
              (leading++[⟨query,observe before,result.1,observe result.2⟩]) nextCursor)
          (do
            let result←(implementation query).run before
            collect implementation observe target published sample position accept (next result.1) result.2
              (leading++[⟨query,observe before,result.1,observe result.2⟩]) nextCursor) := by
        apply law_bind_supported
        intro result reached
        have retained := unarmed query before missing (fun index same=>by rw [counter];exact different index same) result reached
        exact ih result.1 result.2 _ nextCursor (by rw [retained.1,counter,←nextCount]) retained.2
      cases query with
      | inl coin=>exact continued (by intro index impossible;cases impossible) cursor (by rfl)
      | inr command=>
        cases command <;> first
        | exact continued (by intro index impossible;cases impossible) cursor (by rfl)
        | by_cases selected : cursor=position
          · simp only [selected,ite_true];exact .refl _
          · simp only [selected,ite_false]
            exact continued (fun _ _=>selected) (cursor+1) (by rfl)

abbrev PlainReceipt (A S View : Type) := Mark A S View × (RustM (Option Pqxdh.Bytes) × S) × Found

def forget (result : Option (Receipt A S View B)) : Option (PlainReceipt A S View) :=
  result.map (fun result=>(result.1,result.2.2.1,result.2.2.2))

noncomputable def positivePlain (accept index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec View)) : ProbComp (Option (PlainReceipt A S View)) := do
  let result←(implementation (.inr (.bundle index))).run before
  if published (.inr (.bundle index)) result.1 result.2 then pure none else
    (fun found=>found.map (fun found=>((Cut.bundle index next,(before,leading)),result,found))) <$>
      RegistrationNativeIdentityCensorVisitorJournal.visit implementation target published accept (next result.1) result.2 (count leading)

/-- Forgetting only the joint chosen-callback receipt yields the literal same reply/full-poststate observation. -/
theorem positive_erasure
    (marginal : ∀ index before,Prod.snd <$>sample index before=(implementation (.inr (.bundle index))).run before)
    (accept index : Nat) (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec View)) :
    forget <$>positive implementation target published sample accept index next before leading=
      positivePlain implementation target published accept index next before leading := by
  unfold positive positivePlain
  rw [←marginal index before,bind_map_left,map_bind]
  apply bind_congr
  intro result
  split
  · simp only [map_pure,forget,Option.map_none]
  · simp only [Functor.map_map,forget,Option.map_map]
    rfl

noncomputable def splitPlain (position accept : Nat) (work : OracleComp TypedSpec A) (before : S)
    (leading : List (Call TypedSpec View)) (cursor : Nat) : ProbComp (Option (PlainReceipt A S View)) := do
  let mark←(simulateQ (RegistrationNativeObservedStageTrace.handler observe implementation) (stop position work cursor)).run (before,leading)
  match mark.1 with
  | .returned _=>pure none
  | .bundle index next=>positivePlain implementation target published accept index next mark.2.1 mark.2.2

/-- A joint selected-callback sampler preserves the complete original public split distribution. -/
theorem split_erasure
    (marginal : ∀ index before,Prod.snd <$>sample index before=(implementation (.inr (.bundle index))).run before)
    (position accept : Nat) (work : OracleComp TypedSpec A) (before : S) (leading : List (Call TypedSpec View)) (cursor : Nat) :
    forget <$>split implementation observe target published sample position accept work before leading cursor=
      splitPlain implementation observe target published position accept work before leading cursor := by
  unfold split splitPlain
  rw [map_bind]
  apply bind_congr
  intro mark
  cases mark.1 with
  | returned value=>simp only [map_pure,forget,Option.map_none]
  | bundle index next=>exact positive_erasure implementation target published sample marginal accept index next mark.2.1 mark.2.2

section Current
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}
local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource

/-- The current concrete marked callback discharges the complete operational invariant of the whole-traversal law. Every private source coordinate and original continuation is retained. -/
theorem current_source (joint : PqxdhJointIdentity.Primitives) (selected position accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool) (frontend : QueryImpl TypedSpec Main)
    (sample : (index : Nat) → FullState → ProbComp (B × (TypedSpec.Range (.inr (.bundle index)) × FullState)))
    (work : OracleComp TypedSpec A) (before : FullState)
    (leading : List (Call TypedSpec (RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform mlSource)))
    (cursor : Nat) (counter : before.1.2.bundles=cursor) (missing : before.1.2.target=none) :
    LawEq (split (RegistrationNativeIdentityCensorBundlePrefix.marked joint selected position placeholder masked frontend)
      RegistrationNativeIdentityCensorActualHashSource.project (fun state=>state.1.2.target)
      RegistrationNativeIdentityCensorAdaptivePostselection.published sample position accept work before leading cursor)
    (collect (RegistrationNativeIdentityCensorBundlePrefix.marked joint selected position placeholder masked frontend)
      RegistrationNativeIdentityCensorActualHashSource.project (fun state=>state.1.2.target)
      RegistrationNativeIdentityCensorAdaptivePostselection.published sample position accept work before leading cursor) := by
  apply source _ _ _ _ _ (fun state=>state.1.2.bundles) position accept _ work before leading cursor counter missing
  intro query before held different result reached
  have control := RegistrationNativeIdentityCensorBundlePrefix.unarmed_step joint selected position placeholder masked frontend query before held different result reached
  exact ⟨control.1,control.2.1⟩
end Current

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt.collect_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt.collect_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt.positive_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt.positive_erasure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt.split_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt.split_erasure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt.current_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt.current_source
