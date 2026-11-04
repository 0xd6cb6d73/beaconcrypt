-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut
/-! A fixed public callback ordinal extends only the original free client's result with its actual query/reply. No private source snapshot is read by the extension. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop
variable {Q S A : Type} {spec : OracleSpec Q}
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

inductive Cut (spec : OracleSpec Q) (A : Type) where
  | complete : A → Cut spec A
  | pending : (query : spec.Domain) → (spec.Range query → OracleComp spec A) → Cut spec A

structure PublicCall (spec : OracleSpec Q) where
  query : spec.Domain
  reply : spec.Range query

def publicCall (call : RegistrationNativeStageTrace.Call spec S) : PublicCall spec := ⟨call.query,call.reply⟩

noncomputable def stop (counted : spec.Domain → Prop) (work : OracleComp spec A) : Nat → OracleComp spec (Cut spec A) :=
  work.recOn (fun value _=>pure (.complete value))
    (fun query next recurse index=>if counted query then match index with
      | 0=>pure (.pending query next)
      | index+1=>do let reply←spec.query query;recurse reply index
      else do let reply←spec.query query;recurse reply index)

def resume : Cut spec A → OracleComp spec A
  | .complete value=>pure value
  | .pending query next=>spec.query query >>=next

def markedResume : Cut spec A → OracleComp spec (Option (PublicCall spec) × A)
  | .complete value=>pure (none,value)
  | .pending query next=>do
      let reply←spec.query query
      let result←next reply
      pure (some ⟨query,reply⟩,result)

private theorem stop_step (counted : spec.Domain → Prop) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec A) (index : Nat) :
    stop counted (spec.query query >>=next) index=(if counted query then match index with
      | 0=>pure (.pending query next)
      | index+1=>do let reply←spec.query query;stop counted (next reply) index
      else do let reply←spec.query query;stop counted (next reply) index) := rfl

/-- The public ordinal stop and literal original continuation recover the original free client exactly. -/
theorem factor (counted : spec.Domain → Prop) (work : OracleComp spec A) (index : Nat) :
    (stop counted work index >>=resume)=work := by
  induction work using OracleComp.inductionOn generalizing index with
  | pure value=>rfl
  | query_bind query next ih=>
    rw [stop_step]
    by_cases hit : counted query
    · cases index with
      | zero=>simp only [hit,ite_true,pure_bind,resume]
      | succ index=>simp only [hit,ite_true,bind_assoc,ih]
    · simp only [hit,ite_false,bind_assoc,ih]

/-- Erasing only the public current query/reply certificate changes no original callback or result. -/
theorem marked_erase (cut : Cut spec A) : Prod.snd <$>markedResume cut=resume cut := by
  cases cut with
  | complete value=>rfl
  | pending query next=>simp only [markedResume,resume,map_bind,map_pure,bind_pure]

/-- The result extension is a pure erasure of the original free program, without consulting a physical backend. -/
theorem client_erase (counted : spec.Domain → Prop) (work : OracleComp spec A) (index : Nat) :
    Prod.snd <$> (stop counted work index >>=markedResume)=work := by
  simp only [map_bind,marked_erase]
  exact factor counted work index

def attach (result : Cut spec A × S) : RegistrationNativePlatformOriginCallbackCut.Outcome spec S A :=
  match result.1 with
  | .complete value=>.inl (value,result.2)
  | .pending query next=>.inr ⟨query,next,result.2⟩

def arrange (result : (Option (PublicCall spec) × A) × S) : Option (PublicCall spec) × (A × S) :=
  (result.1.1,(result.1.2,result.2))

/-- Interpreting the public free stop is exactly the existing actual stateful callback scan with its same reached state. -/
theorem scan_source (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (index : Nat) (state : S) :
    attach <$> (simulateQ implementation (stop counted work index)).run state=
      RegistrationNativePlatformOriginCallbackCut.scan counted implementation work index state := by
  induction work using OracleComp.inductionOn generalizing index state with
  | pure value=>rfl
  | query_bind query next ih=>
    rw [stop_step,RegistrationNativePlatformOriginCallbackCut.scan_query]
    by_cases hit : counted query
    · cases index with
      | zero=>simp only [hit,ite_true,simulateQ_pure,StateT.run_pure,map_pure,attach]
      | succ index=>
        simp only [hit,ite_true,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
        exact bind_congr (fun result=>ih result.1 index result.2)
    · simp only [hit,ite_false,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
      exact bind_congr (fun result=>ih result.1 index result.2)

/-- The actual callback certificate projects to precisely the same public query/reply in the free extension. -/
theorem resume_source (implementation : QueryImpl spec (StateT S ProbComp)) (result : Cut spec A × S) :
    arrange <$> (simulateQ implementation (markedResume result.1)).run result.2=
      Prod.map (Option.map publicCall) id <$>
        RegistrationNativePlatformOriginCallbackCut.markedResume implementation (attach result) := by
  rcases result with ⟨cut,state⟩
  cases cut with
  | complete value=>rfl
  | pending query next=>
    simp only [markedResume,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,simulateQ_pure,StateT.run_pure,
      map_bind,map_pure,RegistrationNativePlatformOriginCallbackCut.markedResume,attach]
    rfl

/-- The complete free client extension and the same actual scanned callback/future have the identical public certificate, result and final source state. -/
theorem source (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (index : Nat) (state : S) :
    arrange <$> (simulateQ implementation (stop counted work index >>=markedResume)).run state=
      Prod.map (Option.map publicCall) id <$>
        (RegistrationNativePlatformOriginCallbackCut.scan counted implementation work index state >>=
          RegistrationNativePlatformOriginCallbackCut.markedResume implementation) := by
  rw [simulateQ_bind,StateT.run_bind,map_bind]
  simp_rw [resume_source]
  rw [←scan_source,bind_map_left,map_bind]
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.factor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.marked_erase' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.marked_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.client_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.client_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.scan_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.scan_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.resume_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.resume_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackFreeStop.source
