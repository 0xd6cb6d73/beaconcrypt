-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind
/-! A source-derived constructor-kind receipt identifies the raw-demand slot observer with direct opaque effect annotation. Both observers forward the same source queries once. No material/key equality or private-state conclusion is assumed. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotAgreement
open PqxdhRecordLiftInterface (Slot)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePlatformPublicRecordSlots (State pendingUpdate snapshotUpdate)
variable {n : Nat} {KemSK A : Type}

def directUpdate (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query) (before : RegistrationNativePlatformRecordSlotGhost.State n) : RegistrationNativePlatformRecordSlotGhost.State n :=
  match query with
  | .inl (.inr (.inl (.inr (.inr effect)))) => RegistrationNativePlatformRecordSlotGhost.next (.inr (.inl effect)) reply before
  | _ => before

def direct : QueryImpl (Spec n KemSK) (StateT (RegistrationNativePlatformRecordSlotGhost.State n) (OracleComp (Spec n KemSK))) := fun query before =>
  (fun reply => (reply,directUpdate query reply before)) <$> (Spec n KemSK).query query

private theorem update_same (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query) (pending : Option (Slot n)) :
    RegistrationNativePlatformPublicRecordSlots.pendingUpdate query reply pending=RegistrationNativePlatformPublicSlotKind.update query reply pending := by
  rfl

/-- Matching constructor kinds makes the demand annotation the literal installation query's opaque origin, including failed replies. -/
theorem query_agrees (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (before : State n) (fits : RegistrationNativePlatformPublicSlotKind.Fits query ⟨before.pending,false⟩) :
    snapshotUpdate query reply before.pending before.snapshot=directUpdate query reply before.snapshot := by
  rcases query with (prepare | (demand | (publication | environment)) | kem) | record
  all_goals try rfl
  rcases environment with coin | request
  · rfl
  · cases request with
    | installServer keyId binding kernel =>
      change RegistrationNativePlatformPublicSlotKind.origin kernel=before.pending at fits
      cases reply with
      | false => rfl
      | true =>
        simp only [snapshotUpdate,directUpdate,RegistrationNativePlatformRecordSlotGhost.next,PqxdhRecordLiftOrigins.annotate,↓reduceIte]
        rw [← fits]
        cases kernel <;> rfl
    | installBeacon owner shell kernel =>
      change RegistrationNativePlatformPublicSlotKind.origin kernel=before.pending at fits
      cases reply with
      | false => rfl
      | true =>
        simp only [snapshotUpdate,directUpdate,RegistrationNativePlatformRecordSlotGhost.next,PqxdhRecordLiftOrigins.annotate,↓reduceIte]
        rw [← fits]
        cases kernel <;> rfl
    | _ => rfl

structure Joint (n : Nat) where
  pending : Option (Slot n)
  bad : Bool
  demanded : RegistrationNativePlatformRecordSlotGhost.State n
  effects : RegistrationNativePlatformRecordSlotGhost.State n

def kind (before : Joint n) : RegistrationNativePlatformPublicSlotKind.State n := ⟨before.pending,before.bad⟩
def demanded (before : Joint n) : RegistrationNativePlatformPublicRecordSlots.State n := ⟨before.pending,before.demanded⟩

noncomputable def step (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query) (before : Joint n) : Joint n :=
  ⟨RegistrationNativePlatformPublicSlotKind.update query reply before.pending,(RegistrationNativePlatformPublicSlotKind.step query reply (kind before)).bad,
    snapshotUpdate query reply before.pending before.demanded,directUpdate query reply before.effects⟩
noncomputable def handler : QueryImpl (Spec n KemSK) (StateT (Joint n) (OracleComp (Spec n KemSK))) := fun query before =>
  (fun reply => (reply,step query reply before)) <$> (Spec n KemSK).query query

private theorem query_kind (query : (Spec n KemSK).Domain) (before : Joint n) :
    Prod.map id kind <$> (handler query).run before=(RegistrationNativePlatformPublicSlotKind.handler query).run (kind before) := by
  simp only [handler,RegistrationNativePlatformPublicSlotKind.handler,StateT.run,Functor.map_map,Prod.map_def,id_eq,step,kind,RegistrationNativePlatformPublicSlotKind.step]

private theorem query_demanded (query : (Spec n KemSK).Domain) (before : Joint n) :
    Prod.map id demanded <$> (handler query).run before=(RegistrationNativePlatformPublicRecordSlots.handler query).run (demanded before) := by
  simp only [handler,RegistrationNativePlatformPublicRecordSlots.handler,StateT.run,Functor.map_map,Prod.map_def,id_eq,step,demanded,RegistrationNativePlatformPublicRecordSlots.step,update_same]

private theorem query_effects (query : (Spec n KemSK).Domain) (before : Joint n) :
    Prod.map id Joint.effects <$> (handler query).run before=(direct query).run before.effects := by
  simp only [handler,direct,StateT.run,Functor.map_map,Prod.map_def,id_eq,step]

def Holds (before : Joint n) : Prop := before.bad=false → before.demanded=before.effects

private theorem step_holds (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query) (before : Joint n)
    (prior : Holds before) : Holds (step query reply before) := by
  intro clean
  have bits : before.bad=false ∧ decide (RegistrationNativePlatformPublicSlotKind.Fits query (kind before))=true := by
    simpa only [step,RegistrationNativePlatformPublicSlotKind.step,kind,Bool.or_eq_false_iff,Bool.not_eq_false'] using clean
  have matching : RegistrationNativePlatformPublicSlotKind.Fits query ⟨before.pending,false⟩ := by
    simpa only [kind,bits.1] using (of_decide_eq_true bits.2)
  change snapshotUpdate query reply before.pending before.demanded=directUpdate query reply before.effects
  have matched := query_agrees query reply (demanded before) matching
  change snapshotUpdate query reply before.pending before.demanded=directUpdate query reply before.demanded at matched
  rw [matched,prior bits.1]

private theorem program_holds (work : OracleComp (Spec n KemSK) A) (before : Joint n) (prior : Holds before)
    (result : A × Joint n) (supported : result ∈ support ((simulateQ handler work).run before)) : Holds result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact prior
  | query_bind query continuation ih =>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    simp only [handler,StateT.run,support_map] at called
    obtain ⟨reply,_queried,same⟩ := called
    subst middle
    exact ih reply _ (step_holds query reply before prior) result continued

/-- A clean source kind monitor derives equality of complete demand/effect slot receipts on the same supported source execution. -/
theorem run_agrees (work : OracleComp (Spec n KemSK) A) (safe : RegistrationNativePlatformPublicSlotKind.Safe work) (before : RegistrationNativePlatformPublicRecordSlots.State n) :
    (fun result => (result.1,result.2.snapshot)) <$> RegistrationNativePlatformPublicRecordSlots.program work before =
      (simulateQ direct work).run before.snapshot := by
  let initial : Joint n := ⟨before.pending,false,before.snapshot,before.snapshot⟩
  have left := map_run_simulateQ_eq_of_query_map_eq handler RegistrationNativePlatformPublicRecordSlots.handler demanded query_demanded work initial
  have right := map_run_simulateQ_eq_of_query_map_eq handler direct Joint.effects query_effects work initial
  have kinds := map_run_simulateQ_eq_of_query_map_eq handler RegistrationNativePlatformPublicSlotKind.handler kind query_kind work initial
  have leftMapped := congrArg (Functor.map (fun result => (result.1,result.2.snapshot))) left
  change (fun result => (result.1,result.2.snapshot)) <$>
    (simulateQ RegistrationNativePlatformPublicRecordSlots.handler work).run (demanded initial) =
      (simulateQ direct work).run initial.effects
  rw [← leftMapped,← right]
  simp only [Functor.map_map,Prod.map_def,id_eq]
  rw [← bind_pure_comp,← bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result supported
  have kindReached : (result.1,kind result.2) ∈ support ((simulateQ RegistrationNativePlatformPublicSlotKind.handler work).run (kind initial)) := by
    rw [← kinds,support_map]
    exact ⟨result,supported,rfl⟩
  have clean := safe (kind initial) _ rfl kindReached
  have same := program_holds work initial (fun _ => rfl) result supported clean
  change pure (result.1,result.2.demanded)=pure (result.1,result.2.effects)
  rw [same]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotAgreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotAgreement.query_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotAgreement.query_agrees
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotAgreement.run_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotAgreement.run_agrees
