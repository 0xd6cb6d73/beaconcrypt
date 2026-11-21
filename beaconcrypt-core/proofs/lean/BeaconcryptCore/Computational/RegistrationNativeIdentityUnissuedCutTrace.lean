-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutCounter
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
/-! The public accept counter is the exact same execution's chronological typed-call count. Existing callback states and all original failures remain intact. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativeIdentityUnissuedCutCounter (cost counted)
variable {S A : Type}

def count (calls : List (Call TypedSpec S)) : Nat := (calls.map fun call => cost call.query).sum

/-- An arbitrary reached journal prefix retains its exact existing calls and one genuine path for every later callback. -/
theorem extension (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec S)) (result : A × (S × List (Call TypedSpec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,leading))) :
    ∃ trailing, result.2.2 = leading ++ trailing ∧ Path implementation before trailing result.2.1 := by
  induction work using OracleComp.inductionOn generalizing before leading result with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact ⟨[],(List.append_nil _).symm,.nil before⟩
  | query_bind query next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,called,continued⟩ := supported
      simp only [RegistrationNativeStageTrace.handler,StateT.run,support_map] at called
      obtain ⟨actual,executed,rfl⟩ := called
      obtain ⟨trailing,same,following⟩ := ih actual.1 actual.2 _ result continued
      refine ⟨⟨query,before,actual.1,actual.2⟩ :: trailing,?_,?_⟩
      · rw [same,List.append_assoc]
        rfl
      · exact Path.cons (implementation := implementation) ⟨query,before,actual.1,actual.2⟩ executed trailing result.2.1 following

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

/-- The analysis counter is literally the journal's number of parsed accept attempts in the same supported execution. -/
theorem counted_trace (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (before : (S × List (Call TypedSpec S)) × Nat) (prior : before.2 = count before.1.2)
    (result : A × ((S × List (Call TypedSpec S)) × Nat))
    (supported : result ∈ support ((simulateQ (counted (RegistrationNativeStageTrace.handler implementation)) work).run before)) :
    result.2.2 = count result.2.1.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle _ (fun current => current.2 = count current.1.2)
    (count_step implementation) work before prior result supported

/-- The original source journal at the stopped prefix has exactly the same public ordinal status, with no caller counter or chronology premise. -/
theorem prefix_status (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (accept : Nat)
    (work : OracleComp TypedSpec A) (before : S)
    (result : RegistrationNativeIdentityUnissuedAcceptCut.Cut A × (S × List (Call TypedSpec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation)
      (RegistrationNativeIdentityUnissuedAcceptCut.stop accept work 0)).run (before,[]))) :
    RegistrationNativeIdentityUnissuedCutCounter.Status accept result.1 (count result.2.2) := by
  rw [←RegistrationNativeIdentityUnissuedCutCounter.erase
    (RegistrationNativeStageTrace.handler implementation) _ ((before,[]),0),support_map] at supported
  obtain ⟨full,reached,same⟩ := supported
  cases same
  have numeric := RegistrationNativeIdentityUnissuedCutCounter.progress accept 0
    (RegistrationNativeStageTrace.handler implementation) work (before,[]) (Nat.zero_le _) full reached
  have recorded := counted_trace implementation (RegistrationNativeIdentityUnissuedAcceptCut.stop accept work 0)
    ((before,[]),0) rfl full reached
  change RegistrationNativeIdentityUnissuedCutCounter.Status accept full.1 (count full.2.1.2)
  rw [←recorded]
  exact numeric

/-- Resumption records the literal selected accept first, at the actual preceding source state, then keeps every original suffix callback. -/
theorem resumed_first (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (packet : beaconcrypt_core.registration.InitPacket)
    (next : TypedSpec.Range (.inr (.accept packet)) → OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec S)) (result : A × (S × List (Call TypedSpec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation)
      (RegistrationNativeIdentityUnissuedAcceptCut.resume (.accept packet next))).run (before,leading))) :
    ∃ call trailing, result.2.2 = leading ++ call :: trailing ∧
      call.query = .inr (.accept packet) ∧ call.before = before ∧
      RegistrationNativeStageTrace.Executed implementation call ∧ Path implementation call.after trailing result.2.1 := by
  rw [RegistrationNativeIdentityUnissuedAcceptCut.resume,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩ := supported
  simp only [RegistrationNativeStageTrace.handler,StateT.run,support_map] at called
  obtain ⟨actual,executed,rfl⟩ := called
  obtain ⟨trailing,same,following⟩ := extension implementation (next actual.1) actual.2 _ result continued
  refine ⟨⟨.inr (.accept packet),before,actual.1,actual.2⟩,trailing,?_,rfl,rfl,executed,following⟩
  rw [same,List.append_assoc]
  rfl

def accepted (calls : List (Call TypedSpec S)) : List (beaconcrypt_core.registration.InitPacket × S) :=
  calls.filterMap fun call => match call.query with
    | .inr (.accept packet) => some (packet,call.before)
    | _ => none

/-- The public ordinal counts all decoded accept calls, including every rejected reply. -/
theorem accepted_length (calls : List (Call TypedSpec S)) : (accepted calls).length = count calls := by
  induction calls with
  | nil => rfl
  | cons call rest ih =>
      cases query : call.query with
      | inl coin => simp_all [accepted,count,cost]
      | inr command =>
          cases command <;> simp_all [accepted,count,cost]
          omega

/-- The selected accepted-attempt entry is exactly the first accept after its counted prefix, retaining its actual before-state. -/
theorem accepted_at (leading trailing : List (Call TypedSpec S)) (packet : beaconcrypt_core.registration.InitPacket)
    (before after : S) (reply : TypedSpec.Range (.inr (.accept packet))) :
    (accepted (leading ++ (⟨.inr (.accept packet),before,reply,after⟩ : Call TypedSpec S) :: trailing))[count leading]? = some (packet,before) := by
  have appended : accepted (leading ++ (⟨.inr (.accept packet),before,reply,after⟩ : Call TypedSpec S) :: trailing) =
      accepted leading ++ (packet,before) :: accepted trailing := by
    simp [accepted]
  rw [appended,←accepted_length leading,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
  rfl

/-- The original ordinal in the resumed complete journal reads exactly the submitted packet and private state retained by that same cut. -/
theorem resumed_at (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (packet : beaconcrypt_core.registration.InitPacket)
    (next : TypedSpec.Range (.inr (.accept packet)) → OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec S)) (accept : Nat) (ordinal : count leading = accept)
    (result : A × (S × List (Call TypedSpec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation)
      (RegistrationNativeIdentityUnissuedAcceptCut.resume (.accept packet next))).run (before,leading))) :
    (accepted result.2.2)[accept]? = some (packet,before) := by
  obtain ⟨call,trailing,same,queryEq,beforeEq,_executed,_following⟩ :=
    resumed_first implementation packet next before leading result supported
  rcases call with ⟨query,current,reply,after⟩
  dsimp only at queryEq beforeEq same
  subst query
  subst current
  rw [same,←ordinal]
  exact accepted_at leading trailing packet before after reply

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.extension

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.counted_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.counted_trace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.prefix_status' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.prefix_status

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.resumed_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.resumed_first

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.accepted_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.accepted_length

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.accepted_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.accepted_at

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.resumed_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace.resumed_at
