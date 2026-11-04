-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication
/-! The operational authentication observer consumes actual source callback boundaries. It snapshots the strict-before-open source signing history, then checks the actual returned source token or pending Beacon against that history when the callback closes. No native audit, receipt chosen from another execution or cache reconstructed from a model is read. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformPublicAdapterSourceEvents (Event Log Spec)
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformPublicAdapterSourceRuntime (Objects)
open RegistrationNativePlatformSdkReification (Backend)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable {n :Nat} {KemSK R P :Type} {source :RegistrationNativeMldsa.Source}

structure State (n :Nat) (KemSK R P :Type) where
  stages :List Stage
  pending :Option (Store n KemSK R P×List Stage)
  bad :Bool

def initial :State n KemSK R P:=⟨[],none,false⟩

noncomputable def closed (view :AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic :Std.Array U8 1952#usize) (pending :Option (Store n KemSK R P×List Stage))
    (query :Spec.Domain) (reply :RustM (Spec.Range query×Objects R)) (after :Backend n KemSK×P) :Bool :=by
  classical
  exact match pending,query,reply with
    | some (before,leading),.inl (.inr command),.ok (value,objects)=>
      decide (RegistrationNativePlatformPublicAdapterSourceAuthentication.Bad view serverPublic leading command before value
        (RegistrationNativePlatformPublicAdapterSourceRuntime.join objects after))
    | _,_,_=>false

noncomputable def step (view :AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic :Std.Array U8 1952#usize) (current :State n KemSK R P) :Event n KemSK R P→State n KemSK R P
  | .stage actual=>{current with stages:=current.stages++[actual]}
  | .opened _ before=>{current with pending:=some (before,current.stages)}
  | .closed query reply after=>{current with pending:=none,bad:=current.bad ||closed view serverPublic current.pending query reply after}

noncomputable def run (view :AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic :Std.Array U8 1952#usize) (current :State n KemSK R P) (events :Log n KemSK R P) :State n KemSK R P :=
  events.foldl (step view serverPublic) current

noncomputable def flag (view :AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic :Std.Array U8 1952#usize) (events :Log n KemSK R P) :Bool:=
  (run view serverPublic initial events).bad

theorem run_append (view :AdapterPublicWrapperState.MaterialView source KemSK) (serverPublic :Std.Array U8 1952#usize)
    (current :State n KemSK R P) (leading trailing :Log n KemSK R P) :
    run view serverPublic current (leading++trailing)=run view serverPublic (run view serverPublic current leading) trailing :=
  List.foldl_append

theorem run_stages (view :AdapterPublicWrapperState.MaterialView source KemSK) (serverPublic :Std.Array U8 1952#usize)
    (current :State n KemSK R P) (actual :List Stage) :
    run view serverPublic current (actual.map Event.stage)={current with stages:=current.stages++actual} :=by
  induction actual generalizing current with
  | nil=>simp only [List.map_nil,run,List.foldl_nil,List.append_nil]
  | cons head tail ih=>
    change run view serverPublic {current with stages:=current.stages++[head]} (tail.map Event.stage)=_
    rw [ih,List.append_assoc]
    rfl

/-- A closing verdict reads exactly the callback's actual before Store and strict earlier signing history. -/
theorem callback (view :AdapterPublicWrapperState.MaterialView source KemSK) (serverPublic :Std.Array U8 1952#usize)
    (current :State n KemSK R P) (query :Spec.Domain) (before :Store n KemSK R P) (actual :List Stage)
    (reply :RustM (Spec.Range query×Objects R)) (after :Backend n KemSK×P) :
    run view serverPublic current ([Event.opened query before]++actual.map Event.stage++[Event.closed query reply after])=
      ⟨current.stages++actual,none,current.bad ||closed view serverPublic (some (before,current.stages)) query reply after⟩ :=by
  rw [run_append,run_append]
  change step view serverPublic (run view serverPublic {current with pending:=some (before,current.stages)} (actual.map Event.stage))
    (.closed query reply after)=_
  rw [run_stages]
  rfl

theorem callback_bad (view :AdapterPublicWrapperState.MaterialView source KemSK) (serverPublic :Std.Array U8 1952#usize)
    (current :State n KemSK R P) (query :Spec.Domain) (before :Store n KemSK R P) (actual :List Stage)
    (reply :RustM (Spec.Range query×Objects R)) (after :Backend n KemSK×P) :
    (run view serverPublic current ([Event.opened query before]++actual.map Event.stage++[Event.closed query reply after])).bad=
      (current.bad ||closed view serverPublic (some (before,current.stages)) query reply after) :=
  congrArg State.bad (callback view serverPublic current query before actual reply after)

theorem closed_iff (view :AdapterPublicWrapperState.MaterialView source KemSK) (serverPublic :Std.Array U8 1952#usize)
    (before :Store n KemSK R P) (leading :List Stage) (command :RegistrationNativePlatformPublicAdapterInterface.Command)
    (reply :RegistrationNativePlatformPublicAdapterInterface.CommandSpec.Range command) (objects :Objects R) (after :Backend n KemSK×P) :
    closed view serverPublic (some (before,leading)) (.inl (.inr command)) (.ok (reply,objects)) after=true ↔
      RegistrationNativePlatformPublicAdapterSourceAuthentication.Bad view serverPublic leading command before reply
        (RegistrationNativePlatformPublicAdapterSourceRuntime.join objects after) :=by
  simp only [closed,decide_eq_true_eq]

/-- The observer's source history is the literal sequence of earlier reached source stages. -/
theorem history_run (view :AdapterPublicWrapperState.MaterialView source KemSK) (serverPublic :Std.Array U8 1952#usize)
    (current :State n KemSK R P) (events :Log n KemSK R P) :
    (run view serverPublic current events).stages=current.stages++RegistrationNativePlatformPublicAdapterSourceAuthentication.stages events :=by
  induction events generalizing current with
  | nil=>simp only [run,List.foldl_nil,RegistrationNativePlatformPublicAdapterSourceAuthentication.stages,List.filterMap_nil,List.append_nil]
  | cons head tail ih=>
    change (run view serverPublic (step view serverPublic current head) tail).stages=_
    rw [ih]
    cases head <;>simp only [step,RegistrationNativePlatformPublicAdapterSourceAuthentication.stages,List.filterMap_cons,List.append_assoc]
    rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.run_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.run_append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.run_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.run_stages
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.callback
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.callback_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.callback_bad
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.closed_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.closed_iff
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.history_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.history_run
