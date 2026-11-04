-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootSource
import BeaconcryptCore.Computational.LazyOracleDiscard
/-! The actual root proxy keeps its ordinary recovery cache jointly with arbitrary persistent World state. Its per-callback marginal may erase that cache because protected-key replies are discarded and every cache/material tail uses the literal World route. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery
open RegistrationNativePlatformRecordPartnerExposureRoot (Spec RootSpec coins material known demand handler)
open RegistrationNativePlatformRecordPartnerExposureSlots (State reserve)
open RegistrationNativeSecretWord (Cache Key)
open RegistrationNativeSecretWordMessage (Message)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthKeySchedule (Output)
open LazyOracleDiscard (LawEq)
variable {n : Nat} {Physical A : Type}
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : RegistrationNativeSuffixKeyPrf.Secret)
    (physical : QueryImpl (WorldSpec n) (StateT Physical ProbComp))
noncomputable def close : QueryImpl (Spec n) (StateT (Cache × Physical) ProbComp)
  | .inl query=>fun before=>(fun result=>(result.1,(result.2,before.2))) <$>
      (RegistrationNativeSecretWordRecoveryCompiler.closed source candidate query).run before.1
  | .inr query=>fun before=>(fun result=>(result.1,(before.1,result.2))) <$> (physical query).run before.2

def WorldOnly : (Spec n).Domain →Prop
  | .inl _=>False
  | .inr _=>True

private theorem bind_apply {S X Y : Type} {m : Type →Type} [Monad m]
    (work : StateT S m X) (next : X →StateT S m Y) (before : S) :
    (work >>=next) before=(work before >>=fun result=>next result.1 result.2) := rfl

private theorem pure_apply {S X : Type} {m : Type →Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before=pure (value,before) := rfl
private theorem map_apply {S X Y : Type} {m : Type →Type} [Monad m] [LawfulMonad m]
    (observe : X →Y) (work : StateT S m X) (before : S) :
    (observe <$>work) before=Prod.map observe id <$>work before := StateT.run_map _ _ _

/-- A literal World-only proxy tail retains its original recovery cache and complete physical transition. -/
theorem world_source (filler : Output) (work : OracleComp (Spec n) A) (allowed : work.AllQueriesSatisfy WorldOnly)
    (cache : Cache) (before : Physical) :
    (simulateQ (close source candidate physical) work).run (cache,before)=
      (fun result=>(result.1,(cache,result.2))) <$>
        (simulateQ physical (simulateQ (RegistrationNativePlatformRecordPartnerExposureRootSource.realization source candidate filler) work)).run before := by
  induction work using OracleComp.inductionOn generalizing cache before with
  | pure value=>simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    cases query with
    | inl query=>exact allowed.1.elim
    | inr query=>
      simp only [simulateQ_bind,simulateQ_spec_query,close,StateT.run,bind_apply,
        RegistrationNativePlatformRecordPartnerExposureRootSource.realization,map_bind,bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 (allowed.2 result.1) cache result.2

/-- Erasing only the untouched recovery cache leaves the same reply and physical state for a World-only tail. -/
theorem world_observed (filler : Output) (work : OracleComp (Spec n) A) (allowed : work.AllQueriesSatisfy WorldOnly)
    (cache : Cache) (before : Physical) :
    (fun result=>(result.1,result.2.2)) <$> (simulateQ (close source candidate physical) work).run (cache,before)=
      (simulateQ physical (simulateQ (RegistrationNativePlatformRecordPartnerExposureRootSource.realization source candidate filler) work)).run before := by
  rw [world_source source candidate physical filler work allowed cache before]
  simp only [Functor.map_map,id_map']

/-- An actual discarded protected-key query is unobservable after erasing only the recovery cache, retaining the same World-only continuation. -/
theorem discarded_key (filler : Output) (key : Key) (work : OracleComp (Spec n) A) (allowed : work.AllQueriesSatisfy WorldOnly)
    (cache : Cache) (before : Physical) :
    LawEq ((fun result=>(result.1,result.2.2)) <$>
      (simulateQ (close source candidate physical) ((Spec n).query (.inl (.inl (.inr key))) >>=fun _=>work)).run (cache,before))
      ((simulateQ physical (simulateQ (RegistrationNativePlatformRecordPartnerExposureRootSource.realization source candidate filler) work)).run before) := by
  have shape : (fun result=>(result.1,result.2.2)) <$>
      (simulateQ (close source candidate physical) ((Spec n).query (.inl (.inl (.inr key))) >>=fun _=>work)).run (cache,before)=
      ((RegistrationNativeSecretWordRecoveryCompiler.closed source candidate (.inl (.inr key))).run cache >>=fun reached=>
        (fun result=>(result.1,result.2.2)) <$> (simulateQ (close source candidate physical) work).run (reached.2,before)) := by
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run,bind_apply,close,map_bind,bind_map_left]
  rw [shape]
  simp_rw [world_observed source candidate physical filler work allowed]
  exact LazyOracleDiscard.lawEq_drop _ _

private theorem coins_world (work : ProbComp A) :
    (simulateQ (coins (n := n)) work).AllQueriesSatisfy WorldOnly := by
  induction work using OracleComp.inductionOn with
  | pure value=>trivial
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,coins,QueryImpl.apply_compose,
      PqxdhRecordLiftInterface.coinLift,RegistrationNativePlatformRecordPartnerExposureRoot.world,
      simulateQ_spec_query,allQueriesSatisfy_query_bind_iff,WorldOnly,true_and]
    exact ih

private theorem material_world (slot : PqxdhRecordLiftInterface.Slot n) (before : State n) :
    ((material slot).run before).AllQueriesSatisfy WorldOnly := by
  simp only [material,StateT.run]
  split
  · trivial
  · rw [map_eq_bind_pure_comp]
    exact allQueriesSatisfy_bind (coins_world _) (fun _=>by trivial)

private theorem known_world (bytes : Pqxdh.Bytes) (before : State n) :
    ((known bytes).run before).AllQueriesSatisfy WorldOnly := by
  simp only [known,StateT.run]
  split
  · trivial
  · rw [map_eq_bind_pure_comp]
    exact allQueriesSatisfy_bind (coins_world _) (fun _=>by trivial)
private theorem map_world {B : Type} (observe : A →B) (work : OracleComp (Spec n) A) (allowed : work.AllQueriesSatisfy WorldOnly) :
    (observe <$>work).AllQueriesSatisfy WorldOnly := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _=>by trivial)

/-- Each actual material demand may erase only its final recovery cache while retaining its reply, opaque root state and complete physical World state. -/
theorem demand_observed (filler : Output) (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool)
    (message : Message) (rootBefore : State n) (cache : Cache) (before : Physical) :
    LawEq ((fun result=>(result.1,result.2.2)) <$>
      (simulateQ (close source candidate physical) ((demand source input inside message).run rootBefore)).run (cache,before))
      ((simulateQ physical (simulateQ (RegistrationNativePlatformRecordPartnerExposureRootSource.realization source candidate filler)
        ((demand source input inside message).run rootBefore))).run before) := by
  cases formed : input message with
  | none=>
    apply LawEq.of_eq
    simp only [demand,StateT.run,formed,simulateQ_pure,pure_apply,map_pure]
  | some key=>
    cases protectedInput : inside key.head with
    | true=>
      let counted : State n:={rootBefore with demands:=rootBefore.demands+1}
      let tail : OracleComp (Spec n) (Option (RegistrationNativePairedChoice.Choice n) × State n) :=
        match key.word with
        | .atom=>match reserve key.head counted with
          | (none,after)=>pure (none,after)
          | (some slot,after)=>(fun result=>(some (.hidden ⟨slot,result.1⟩),result.2)) <$> (material slot).run after
        | .literal secret=>(fun result=>(some (.known result.1),result.2)) <$>
            (known (RegistrationNativeSecretWord.eval secret key)).run counted
      have tailWorld : tail.AllQueriesSatisfy WorldOnly := by
        dsimp only [tail]
        cases wordEq : key.word with
        | atom=>
          cases reserved : reserve key.head counted with
          | mk selected after=>cases selected with
            | none=>trivial
            | some slot=>exact map_world _ _ (material_world slot after)
        | literal secret=>exact map_world _ _ (known_world _ counted)
      have shape : (demand source input inside message).run rootBefore=
          (((Spec n).query (.inl (.inl (.inr key))) : OracleComp (Spec n) Output) >>=fun _=>tail) := by
        simp only [demand,StateT.run,formed,protectedInput,ite_true]
        rfl
      have erased : simulateQ (RegistrationNativePlatformRecordPartnerExposureRootSource.realization source candidate filler)
          (((Spec n).query (.inl (.inl (.inr key))) : OracleComp (Spec n) Output) >>=fun _=>tail)=
          simulateQ (RegistrationNativePlatformRecordPartnerExposureRootSource.realization source candidate filler) tail := by
        simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerExposureRootSource.realization,pure_bind]
      rw [shape,erased]
      exact discarded_key source candidate physical filler key tail tailWorld cache before
    | false=>
      cases wordEq : key.word with
      | atom=>
        apply LawEq.of_eq
        simp only [demand,StateT.run,formed,protectedInput,Bool.false_eq_true,ite_false,wordEq,
          simulateQ_map,simulateQ_spec_query,close,RegistrationNativeSecretWordRecoveryCompiler.closed,
          RegistrationNativePlatformRecordPartnerExposureRootSource.realization,StateT.run,simulateQ_pure,pure_apply,map_apply,map_pure]
        rfl
      | literal secret=>
        apply LawEq.of_eq
        simp only [demand,StateT.run,formed,protectedInput,Bool.false_eq_true,ite_false,wordEq,
          simulateQ_pure,pure_apply,map_pure]

/-- The existing root preparation notification and every material-demand branch have the same full physical marginal under actual ordinary recovery. -/
theorem handler_observed (filler : Output) (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool)
    (query : (RootSpec n).Domain) (rootBefore : State n) (cache : Cache) (before : Physical) :
    LawEq ((fun result=>(result.1,result.2.2)) <$>
      (simulateQ (close source candidate physical) ((handler source input inside query).run rootBefore)).run (cache,before))
      ((simulateQ physical (simulateQ (RegistrationNativePlatformRecordPartnerExposureRootSource.realization source candidate filler)
        ((handler source input inside query).run rootBefore))).run before) := by
  cases query with
  | inl message=>
    apply LawEq.of_eq
    simp only [handler,StateT.run,simulateQ_pure,pure_apply,map_pure]
  | inr message=>exact demand_observed source candidate physical filler input inside message rootBefore cache before
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery.world_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery.world_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery.world_observed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery.discarded_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery.discarded_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery.demand_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery.demand_observed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery.handler_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootRecovery.handler_observed
