-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat
/-! The literal current native/full compiler has its exact free source and observed callback journal. Product association retains all state, while the live private physical backend remains outside the chosen analysis projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open PqxdhDeploymentInterface (Spec FullSpec FreshBounds)
open PqxdhServerAuthExperiment (Codec)
variable {n : Nat} {Platform Failure Reader Response Private A View : Type}

abbrev Inner (n : Nat) (Platform : Type) := (Platform × CborRecordWorldClient.Shell) × Control n
abbrev State (n : Nat) (Platform : Type) := PqxdhDeploymentSecrecy.Ledger × Inner n Platform

def join (result : ((A × Platform) × CborRecordWorldClient.Shell) × Control n) : A × Inner n Platform :=
  (result.1.1.1,((result.1.1.2,result.1.2),result.2))

noncomputable def fold (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT Platform (OracleComp (WorldSpec n)) A) : StateT (Inner n Platform) (OracleComp (ServiceSpec n)) A := fun before =>
  join <$> (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    ((simulateQ CborRecordWorldClient.handler (work.run before.1.1)).run before.1.2)).run before.2

private theorem fold_run (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT Platform (OracleComp (WorldSpec n)) A) (before : Inner n Platform) :
    (fold codec route work).run before=join <$>
      (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((simulateQ CborRecordWorldClient.handler (work.run before.1.1)).run before.1.2)).run before.2 := rfl

noncomputable def native (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl Spec (StateT (Inner n Platform) (OracleComp (ServiceSpec n))) := fun query =>
  fold codec route (RegistrationNativePlatformGatedRecordInterface.native env reserve query)

noncomputable def frontend (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKid : U64) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (State n Platform) (OracleComp (ServiceSpec n))) :=
  QueryImpl.Stateful.link (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds)
    (native env reserve codec route)

variable (env : Environment n Platform) (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKid : U64) (bounds : FreshBounds)
    (service : QueryImpl (ServiceSpec n) (StateT Private ProbComp))

/-- Closing the literal current native source retains every cursor/control and private coordinate. -/
theorem native_query (query : Spec.Domain) (before : Inner n Platform × Private) :
    (RegistrationNativePlatformGatedRecordFlat.native service env reserve codec route query).run before =
      (QueryImpl.Stateful.link (native env reserve codec route) service query).run before := by
  rw [QueryImpl.Stateful.link_impl_apply_run]
  let sourceWork := (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    ((simulateQ CborRecordWorldClient.handler
      ((RegistrationNativePlatformGatedRecordInterface.native env reserve query).run before.1.1.1)).run before.1.1.2)).run before.1.2
  change RegistrationNativePlatformGatedRecordFlat.join <$> (simulateQ service sourceWork).run before.2 =
    (fun result => (result.1.1,(result.1.2,result.2))) <$> (simulateQ service (join <$> sourceWork)).run before.2
  rw [simulateQ_map,StateT.run_map,Functor.map_map]
  rfl

private theorem native_equal : RegistrationNativePlatformGatedRecordFlat.native service env reserve codec route =
    QueryImpl.Stateful.link (native env reserve codec route) service := by
  funext query before
  exact native_query env reserve codec route service query before

def associate (before : PqxdhDeploymentSecrecy.Ledger × (Inner n Platform × Private)) : State n Platform × Private :=
  ((before.1,before.2.1),before.2.2)

/-- The actual full source closes through the same backend after only product association. -/
theorem query (query : FullSpec.Domain) (before : PqxdhDeploymentSecrecy.Ledger × (Inner n Platform × Private)) :
    Prod.map id associate <$> (RegistrationNativePlatformGatedRecordFlat.full service env reserve crypto codec route serverKid bounds query).run before =
      (QueryImpl.Stateful.link (frontend env reserve crypto codec route serverKid bounds) service query).run (associate before) := by
  rw [RegistrationNativePlatformGatedRecordFlat.full,QueryImpl.flattenStateT_mapStateTBase_apply_run,
    QueryImpl.Stateful.link_impl_apply_run,frontend,QueryImpl.Stateful.link_impl_apply_run]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map]
  change (fun result => (result.1.1,associate (result.1.2,result.2))) <$>
      (simulateQ (RegistrationNativePlatformGatedRecordFlat.native service env reserve codec route)
        ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds query).run before.1)).run before.2 = _
  rw [native_equal,QueryImpl.Stateful.simulateQ_link_run]
  simp only [Functor.map_map,associate]
  rfl

/-- Every adaptive full client retains the same complete source state after this association. -/
theorem program (work : OracleComp FullSpec A) (before : PqxdhDeploymentSecrecy.Ledger × (Inner n Platform × Private)) :
    Prod.map id associate <$> (simulateQ
      (RegistrationNativePlatformGatedRecordFlat.full service env reserve crypto codec route serverKid bounds) work).run before =
      (simulateQ (QueryImpl.Stateful.link (frontend env reserve crypto codec route serverKid bounds) service) work).run (associate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ associate
    (query env reserve crypto codec route serverKid bounds service) work before

def journalAssociate {S : Type} (before : (S × Private) × List (RegistrationNativeStageTrace.Call FullSpec View)) :
    (S × List (RegistrationNativeStageTrace.Call FullSpec View)) × Private :=
  ((before.1.1,before.2),before.1.2)

private theorem observed_run {S R : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : S → R) (implementation : QueryImpl FullSpec (StateT S m)) (query : FullSpec.Domain)
    (before : S × List (RegistrationNativeStageTrace.Call FullSpec R)) :
    (RegistrationNativeObservedStageTrace.handler observe implementation query).run before =
      (fun result => (result.1,(result.2,before.2++[⟨query,observe before.1,result.1,observe result.2⟩]))) <$>
        (implementation query).run before.1 := rfl

private theorem linked_run {S : Type}
    (front : QueryImpl FullSpec (StateT S (OracleComp (ServiceSpec n))))
    (backend : QueryImpl (ServiceSpec n) (StateT Private ProbComp)) (query : FullSpec.Domain) (before : S × Private) :
    (QueryImpl.Stateful.link front backend query).run before =
      (fun result=>(result.1.1,(result.1.2,result.2))) <$> (simulateQ backend ((front query).run before.1)).run before.2 := by
  rw [QueryImpl.Stateful.link_impl_apply_run]
  rfl

private theorem observed_query {S : Type}
    (front : QueryImpl FullSpec (StateT S (OracleComp (ServiceSpec n))))
    (backend : QueryImpl (ServiceSpec n) (StateT Private ProbComp)) (observe : S → View)
    (query : FullSpec.Domain) (before : (S × Private) × List (RegistrationNativeStageTrace.Call FullSpec View)) :
    Prod.map id journalAssociate <$>
      (RegistrationNativeObservedStageTrace.handler (fun current=>observe current.1) (QueryImpl.Stateful.link front backend) query).run before =
      (QueryImpl.Stateful.link (RegistrationNativeObservedStageTrace.handler observe front) backend query).run (journalAssociate before) := by
  rcases before with ⟨⟨current,privateBefore⟩,calls⟩
  rw [observed_run,linked_run,linked_run,observed_run]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map,journalAssociate,Prod.map_def,id_eq]

private theorem observed_link_program {S : Type}
    (front : QueryImpl FullSpec (StateT S (OracleComp (ServiceSpec n))))
    (backend : QueryImpl (ServiceSpec n) (StateT Private ProbComp)) (observe : S → View)
    (work : OracleComp FullSpec A) (before : (S × Private) × List (RegistrationNativeStageTrace.Call FullSpec View)) :
    Prod.map id journalAssociate <$>
      (simulateQ (RegistrationNativeObservedStageTrace.handler (fun current=>observe current.1) (QueryImpl.Stateful.link front backend)) work).run before =
      (simulateQ (QueryImpl.Stateful.link (RegistrationNativeObservedStageTrace.handler observe front) backend) work).run (journalAssociate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ journalAssociate
    (observed_query front backend observe) work before

def observedAssociate (before : (PqxdhDeploymentSecrecy.Ledger × (Inner n Platform × Private)) ×
    List (RegistrationNativeStageTrace.Call FullSpec View)) :
    (State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) × Private :=
  journalAssociate (associate before.1,before.2)

/-- An arbitrary proved analysis projection of actual full callback snapshots has the exact free frontend journal, retaining the live private backend outside that journal. -/
theorem observed_program (observe : State n Platform → View) (work : OracleComp FullSpec A)
    (before : (PqxdhDeploymentSecrecy.Ledger × (Inner n Platform × Private)) × List (RegistrationNativeStageTrace.Call FullSpec View)) :
    Prod.map id observedAssociate <$>
      (simulateQ (RegistrationNativeObservedStageTrace.handler (fun current=>observe (associate current).1)
        (RegistrationNativePlatformGatedRecordFlat.full service env reserve crypto codec route serverKid bounds)) work).run before =
      (simulateQ (QueryImpl.Stateful.link
        (RegistrationNativeObservedStageTrace.handler observe (frontend env reserve crypto codec route serverKid bounds)) service) work).run
          (observedAssociate before) := by
  have first := RegistrationNativeObservedStageTrace.project
    (RegistrationNativePlatformGatedRecordFlat.full service env reserve crypto codec route serverKid bounds)
    (QueryImpl.Stateful.link (frontend env reserve crypto codec route serverKid bounds) service)
    associate (fun current=>observe (associate current).1) (fun current=>observe current.1)
    (query env reserve crypto codec route serverKid bounds service) (fun _=>rfl) work before
  have mapped := congrArg (Functor.map (Prod.map id journalAssociate)) first
  have second := observed_link_program (frontend env reserve crypto codec route serverKid bounds) service observe work (associate before.1,before.2)
  simpa only [Functor.map_map,Prod.map_def,id_eq,observedAssociate] using mapped.trans second

/-- The free journal is a pure result extension of the actual original frontend source, without any extra request. -/
theorem erase (observe : State n Platform → View) (work : OracleComp FullSpec A)
    (before : State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) :
    Prod.map id Prod.fst <$> (simulateQ
      (RegistrationNativeObservedStageTrace.handler observe (frontend env reserve crypto codec route serverKid bounds)) work).run before =
      (simulateQ (frontend env reserve crypto codec route serverKid bounds) work).run before.1 :=
  RegistrationNativeObservedStageTrace.erase observe (frontend env reserve crypto codec route serverKid bounds) work before

/-- The literal free native compiler is exactly the existing nested source interpretation, including all stateful gates. -/
theorem native_source (work : OracleComp Spec A) (before : Inner n Platform) :
    (simulateQ (native env reserve codec route) work).run before =
      join <$> RegistrationNativePlatformOriginNativeTails.source env reserve codec route work before.1.1 before.1.2 before.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,RegistrationNativePlatformOriginNativeTails.source,map_pure,join]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,native,fold_run,
      RegistrationNativePlatformOriginNativeTails.source,map_bind,bind_map_left]
    apply bind_congr
    intro result
    simpa only [join,Functor.map_map,RegistrationNativePlatformOriginNativeTails.source] using ih result.1.1.1 ((result.1.1.2,result.1.2),result.2)

def fullJoin (result : (((A × PqxdhDeploymentSecrecy.Ledger) × Platform) × CborRecordWorldClient.Shell) × Control n) :
    A × State n Platform :=
  let current := join result
  (current.1.1,(current.1.2,current.2))

/-- The free full frontend is the same actual ledger-wrapped source tree with its complete original ledger, platform, cursor and control. -/
theorem frontend_source (work : OracleComp FullSpec A) (before : State n Platform) :
    (simulateQ (frontend env reserve crypto codec route serverKid bounds) work).run before =
      fullJoin <$> RegistrationNativePlatformOriginNativeTails.source env reserve codec route
        ((simulateQ (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds) work).run before.1)
          before.2.1.1 before.2.1.2 before.2.2 := by
  rw [frontend,QueryImpl.Stateful.simulateQ_link_run,native_source]
  simp only [Functor.map_map]
  rfl

def fullObservedAssociate (observe : State n Platform → View)
    (before : (PqxdhDeploymentSecrecy.Ledger × (Inner n Platform × Private)) ×
      List (RegistrationNativeStageTrace.Call FullSpec (PqxdhDeploymentSecrecy.Ledger × (Inner n Platform × Private)))) :
    (State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) × Private :=
  observedAssociate (before.1,before.2.map (RegistrationNativeObservedStageTrace.mapCall (fun current=>observe (associate current).1)))

/-- Full actual physical callback snapshots project to the same executable free observed journal. Live backend state stays complete and outside the journal. -/
theorem full_observed (observe : State n Platform → View) (work : OracleComp FullSpec A)
    (before : (PqxdhDeploymentSecrecy.Ledger × (Inner n Platform × Private)) ×
      List (RegistrationNativeStageTrace.Call FullSpec (PqxdhDeploymentSecrecy.Ledger × (Inner n Platform × Private)))) :
    Prod.map id (fullObservedAssociate observe) <$>
      (simulateQ (RegistrationNativeStageTrace.handler
        (RegistrationNativePlatformGatedRecordFlat.full service env reserve crypto codec route serverKid bounds)) work).run before =
      (simulateQ (QueryImpl.Stateful.link
        (RegistrationNativeObservedStageTrace.handler observe (frontend env reserve crypto codec route serverKid bounds)) service) work).run
          (fullObservedAssociate observe before) := by
  have first := RegistrationNativeObservedStageTrace.full_project (fun current=>observe (associate current).1)
    (RegistrationNativePlatformGatedRecordFlat.full service env reserve crypto codec route serverKid bounds) work before
  have mapped := congrArg (Functor.map (Prod.map id observedAssociate)) first
  have second := observed_program env reserve crypto codec route serverKid bounds service observe work
    (before.1,before.2.map (RegistrationNativeObservedStageTrace.mapCall (fun current=>observe (associate current).1)))
  simpa only [Functor.map_map,Prod.map_def,id_eq,fullObservedAssociate] using mapped.trans second

/-- The existing full closed-source journal law applies literally to this current free compiler. -/
theorem closed_full (work : OracleComp FullSpec A)
    (before : (State n Platform × Private) × List (RegistrationNativeStageTrace.Call FullSpec (State n Platform × Private))) :
    Prod.map id RegistrationNativeIdentityFreeStageTrace.projectFull <$>
      (simulateQ (RegistrationNativeStageTrace.handler
        (QueryImpl.Stateful.link (frontend env reserve crypto codec route serverKid bounds) service)) work).run before =
      (simulateQ (QueryImpl.Stateful.link
        (RegistrationNativeObservedStageTrace.handler id (frontend env reserve crypto codec route serverKid bounds)) service) work).run
          (RegistrationNativeIdentityFreeStageTrace.projectFull before) :=
  RegistrationNativeIdentityFreeStageTrace.full_program (frontend env reserve crypto codec route serverKid bounds) service work before
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.native_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.native_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.observed_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.observed_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.native_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.frontend_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.frontend_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.full_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.full_observed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.closed_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace.closed_full
