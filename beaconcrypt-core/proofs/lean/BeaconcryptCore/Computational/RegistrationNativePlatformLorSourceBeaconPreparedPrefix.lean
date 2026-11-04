-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedSeen
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconComplete
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport
/-! A material demand in the actual optional-scalar Beacon callback has the preparation of its same returned reference strictly in its past. Individual prepare echo, recording and trace retention suffice; no whole-controller or known-material premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedPrefix
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec LocalSpec effect)
open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared)
open RegistrationNativePlatformOriginCallbackCut (Prefix)
open RegistrationNativePlatformSecretWordInstallBeaconComplete (compile)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {I KemSK Current A B Auxiliary : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private def Only (reference : Message) : (Spec n KemSK).Domain → Prop
 | .inl (.inr (.inl (.inl message)))=>message=reference
 | _=>True

private def NoDemand : (Spec n KemSK).Domain → Prop
 | .inl (.inr (.inl (.inl _)))=>False
 | _=>True

private theorem simulate_allowed {Q : Type} {queries : OracleSpec Q}
    (handler : QueryImpl queries (OracleComp (Spec n KemSK)))
    (first : Q → Prop) (last : (Spec n KemSK).Domain → Prop)
    (leaves : ∀query,first query →(handler query).AllQueriesSatisfy last)
    (work : OracleComp queries A) (quiet : work.AllQueriesSatisfy first) :
    (simulateQ handler work).AllQueriesSatisfy last := by
  induction work using OracleComp.inductionOn with
  | pure value=>trivial
  | query_bind query next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at quiet
    rw [simulateQ_bind,simulateQ_spec_query]
    exact allQueriesSatisfy_bind (leaves query quiet.1) (fun reply=>ih reply (quiet.2 reply))

private theorem effects_allowed (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (predicate : (Spec n KemSK).Domain → Prop)
    (allowed : ∀query,predicate (.inl (.inr (.inl (.inr query)))))
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) :
    (compile (n := n) setup scalar (simulateQ effect work)).AllQueriesSatisfy predicate := by
  cases scalar <;>
    simp only [compile,RegistrationNativeSecretWordAtomOwnerSource.routing,←QueryImpl.simulateQ_compose]
  all_goals
    apply simulate_allowed _ (fun _=>True) predicate _ work (by induction work using OracleComp.inductionOn with | pure _=>trivial | query_bind q k ih=>exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,ih⟩)
    intro query _
    simpa only [QueryImpl.apply_compose,effect,simulateQ_spec_query,RegistrationNativeSecretWordOwners.ordinary,
      RegistrationNativeSecretWordInterface.liftLocal,allQueriesSatisfy_query_iff] using allowed (.inr query)

private theorem route_free (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (LocalSpec n KemSK) A)
    (quiet : work.IsQueryBoundP (RegistrationNativeSecretWordFrontendCapsLocal.IsDemand (KemSK := KemSK)) 0) :
    (compile (n := n) setup scalar work).AllQueriesSatisfy (NoDemand (KemSK := KemSK)) := by
  have bounded : (compile (n := n) setup scalar work).IsQueryBoundP
      (RegistrationNativeSecretWordInterpreterCaps.IsDemand (KemSK := KemSK)) 0 := by
    cases scalar with
    | none=>exact RegistrationNativePlatformSecretWordCapsTransport.local_bound false work 0 quiet
    | some scalar=>
      simp only [compile,RegistrationNativeSecretWordAtomOwnerSource.routing,QueryImpl.simulateQ_compose]
      apply RegistrationNativePlatformSecretWordCapsTransport.local_bound false _ 0
      apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ quiet
      intro query
      rcases query with message|(message|common)|kem
      · simp only [RegistrationNativeSecretWordOwners.ordinary]
        split <;> simp [RegistrationNativeSecretWordFrontendCapsLocal.IsDemand,isQueryBoundP_query_iff]
      · simp [RegistrationNativeSecretWordOwners.ordinary,RegistrationNativeSecretWordFrontendCapsLocal.IsDemand,isQueryBoundP_query_iff]
      · simp [RegistrationNativeSecretWordOwners.ordinary,RegistrationNativeSecretWordFrontendCapsLocal.IsDemand,isQueryBoundP_query_iff]
      · simp [RegistrationNativeSecretWordOwners.ordinary,RegistrationNativeSecretWordFrontendCapsLocal.IsDemand,isQueryBoundP_query_iff]
  have static := (isQueryBoundP_zero_iff _ (fun query=>¬RegistrationNativeSecretWordInterpreterCaps.IsDemand (KemSK := KemSK) query)).mp
    (by simpa only [not_not] using bounded)
  apply static.mono
  intro query allowed
  rcases query with (message|(message|common)|kem)|record
  · trivial
  · exact allowed trivial
  · trivial
  · trivial
  · trivial

private theorem abort_allowed (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (predicate : (Spec n KemSK).Domain → Prop)
    (allowed : ∀query,predicate (.inl (.inr (.inl (.inr query)))))
    (owner current : SelectedOwner source) (env : EnvState Auxiliary) (value : RustM (Option Pqxdh.Bytes)) :
    (compile (n := n) setup scalar (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure value).run current).run env)).AllQueriesSatisfy predicate := by
  cases scalar <;>
    change (OracleComp.queryBind (spec := Spec n KemSK) (.inl (.inr (.inl (.inr (.inr (.inr (.advanceOwner owner.worldOwner .aborted))))))) (fun _=>pure ((value,current),env))).AllQueriesSatisfy predicate
  all_goals exact ⟨allowed _,fun _=>trivial⟩

private theorem chosen_allowed (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (predicate : (Spec n KemSK).Domain → Prop)
    (allowed : ∀query,predicate (.inl (.inr (.inl (.inr query)))))
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (env : EnvState Auxiliary)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n) :
    (compile (n := n) setup scalar (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer effect owner ready choice).run current).run env)).AllQueriesSatisfy predicate :=
  effects_allowed setup scalar predicate allowed _

private theorem complete_only (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : BeaconReady) (env : EnvState Auxiliary) :
    (compile (n := n) setup scalar (((RegistrationNativePlatformSecretWordFinish.complete crypto writer owner ready).run current).run env)).AllQueriesSatisfy
      (Only (KemSK := KemSK) ready.reference) := by
  simp only [compile,RegistrationNativePlatformSecretWordFinish.complete,StateT.run_bind,StateT.run_lift,
    bind_pure_comp,bind_map_left,RegistrationNativeSecretWordInterface.demand,simulateQ_bind,simulateQ_spec_query]
  have demand : RegistrationNativeSecretWordAtomOwnerSource.routing (n := n) setup scalar (.inr (.inl (.inl ready.reference)))=
      (Spec n KemSK).query (.inl (.inr (.inl (.inl ready.reference)))) := by cases scalar <;> rfl
  rw [demand,allQueriesSatisfy_query_bind_iff]
  refine ⟨rfl,?_⟩
  intro choice
  cases choice with
  | none=>exact abort_allowed setup scalar (Only ready.reference) (fun _=>trivial) owner current env (.ok none)
  | some choice=>exact chosen_allowed setup scalar (Only ready.reference) (fun _=>trivial) crypto writer owner current env (ready.eval RegistrationNativeSecretWordMessage.zero) choice

private theorem after_none (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (env : EnvState Auxiliary)
    (ready : RustM (Option BeaconReady)) (noReady : ∀reference,ready≠.ok (some reference)) :
    (compile (n := n) setup scalar (((RegistrationNativePlatformSecretWordFinish.afterPrepared crypto writer owner ready).run current).run env)).AllQueriesSatisfy
      (NoDemand (KemSK := KemSK)) := by
  cases ready with
  | fail error=>exact abort_allowed setup scalar NoDemand (fun _=>trivial) owner current env (.fail error)
  | div=>exact abort_allowed setup scalar NoDemand (fun _=>trivial) owner current env .div
  | ok result=>cases result with
    | none=>exact abort_allowed setup scalar NoDemand (fun _=>trivial) owner current env (.ok none)
    | some reference=>exact False.elim (noReady reference rfl)

private noncomputable def close {Value : Type} (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePlatformSecretWordFinish.M n KemSK RegistrationServerRoleBackend.State source Value)
    (owner : SelectedOwner source) (env : RegistrationServerReferenceCompiler.Environment) :=
  compile setup scalar ((work.run owner).run env)

private theorem finish_close (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (env : RegistrationServerReferenceCompiler.Environment) :
    close (n := n) setup ownScalar (RegistrationNativePlatformSecretWordFinish.finish setup wire source packet) owner env =
      match owner.phase with
      | .initSent pending _ => match pending.aborted_state with
        | .fail error => pure ((.fail error, owner), env)
        | .div => pure ((.div, owner), env)
        | .ok _ => do
            let reached ← close setup ownScalar (RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet) owner env
            close setup ownScalar (RegistrationNativePlatformSecretWordFinish.afterPrepared setup.source wire.frameWrite owner reached.1.1) reached.1.2 reached.2
      | _ => pure ((.ok none, owner), env) := by
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [close, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile, RegistrationNativePlatformSecretWordFinish.finish, StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, StateT.run_pure, simulateQ_pure]
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [close, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile, RegistrationNativePlatformSecretWordFinish.finish, StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, moved, StateT.run_pure, simulateQ_pure]
      | ok aborted =>
          simp only [close, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile, RegistrationNativePlatformSecretWordFinish.finish, RegistrationNativeSecretWordBeaconCompiler.finishPreparation,
            StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, moved, StateT.run_modify, StateT.run_set,
            StateT.run_lift, bind_pure_comp, bind_map_left, simulateQ_bind, bind_assoc]
          apply bind_congr
          intro accepted
          cases accepted with
          | fail error | div => simp only [StateT.run_pure, simulateQ_pure, pure_bind, RegistrationNativePlatformSecretWordFinish.afterPrepared]
          | ok response => cases response with
            | Err _ => simp only [StateT.run_pure, simulateQ_pure, pure_bind, RegistrationNativePlatformSecretWordFinish.afterPrepared]
            | Ok authenticated =>
                simp only [RegistrationNativePlatformSecretWordFinish.phase, StateT.run_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, bind_map_left, simulateQ_bind, simulateQ_map]


variable (implementation : QueryImpl (Spec n KemSK) (StateT Current ProbComp))
    (seen : Current →RegistrationNativeSecretWordFrontendTrace.State)
    (keeps : ∀message query before result,result∈support ((implementation query).run before) →
      Prepared message (seen before) →Prepared message (seen result.2))
include keeps

private theorem prefix_keeps (message : Message) {work rest : OracleComp (Spec n KemSK) A}
    {before after : Current} (path : Prefix implementation work before rest after)
    (prepared : Prepared message (seen before)) : Prepared message (seen after) := by
  induction path with
  | initial=>exact prepared
  | step earlier called ih=>exact keeps message _ _ _ called ih

private theorem only_prepared (reference : Message) (work : OracleComp (Spec n KemSK) A)
    (quiet : work.AllQueriesSatisfy (Only (KemSK := KemSK) reference)) (before after : Current)
    (prepared : Prepared reference (seen before)) (message : Message)
    (tail : (Spec n KemSK).Range (.inl (.inr (.inl (.inl message)))) →OracleComp (Spec n KemSK) A)
    (path : Prefix implementation work before ((Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) :
    Prepared message (seen after) := by
  have equal : message=reference := RegistrationNativePlatformLorSourcePreparedPrefix.query_allowed implementation
    (Only (KemSK := KemSK) reference) work quiet before _ tail after path
  rw [equal]
  exact prefix_keeps implementation seen keeps reference path prepared

omit seen keeps in
private theorem no_demand {work : OracleComp (Spec n KemSK) A} (quiet : work.AllQueriesSatisfy (NoDemand (KemSK := KemSK)))
    {before after : Current} (message : Message)
    (tail : (Spec n KemSK).Range (.inl (.inr (.inl (.inl message)))) →OracleComp (Spec n KemSK) A)
    (path : Prefix implementation work before ((Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) : False :=
  RegistrationNativePlatformLorSourcePreparedPrefix.query_allowed implementation (NoDemand (KemSK := KemSK)) work quiet before _ tail after path


variable (setup : Setup base KemSK) (input : Message →Option Key)
    (echo : ∀message before result,result∈support ((implementation (.inl (.inl message))).run before) →
      result.1=(input message).map (fun _=>message))
    (recorded : ∀message before result,result∈support ((implementation (.inl (.inl message))).run before) →
      Prepared message (seen result.2))
include echo recorded

omit keeps echo recorded in
private theorem scalar_compose (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativePlatformRecordPartnerFinishScalar.scalarLocal setup implementation scalar=
      implementation ∘ₛ RegistrationNativeSecretWordAtomOwnerSource.routing setup scalar := by
  cases scalar with
  | none=>rfl
  | some scalar=>
    funext query
    simp only [RegistrationNativePlatformRecordPartnerFinishScalar.scalarLocal,
      RegistrationNativeSecretWordAtomOwnerSource.routing,QueryImpl.compose,QueryImpl.simulateQ_compose]

/-- A demand reached inside the complete literal Beacon finish follows the preparation of its same returned reference. -/
theorem local_finish (wire : RegistrationNativeWire.Wire) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : RegistrationServerReferenceCompiler.Environment)
    (before after : Current) (message : Message)
    (tail : (Spec n KemSK).Range (.inl (.inr (.inl (.inl message)))) →
      OracleComp (Spec n KemSK) ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) ×RegistrationServerReferenceCompiler.Environment))
    (path : Prefix implementation (close setup scalar (RegistrationNativePlatformSecretWordFinish.finish setup wire source packet) owner env)
      before ((Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) :
    Prepared message (seen after) := by
  rw [finish_close] at path
  cases phaseEq : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _=>
    simp only [phaseEq] at path
    exact False.elim (no_demand implementation (by trivial) message tail path)
  | initSent pending oneTime=>
    simp only [phaseEq] at path
    cases moved : pending.aborted_state with
    | fail error | div=>
      simp only [moved] at path
      exact False.elim (no_demand implementation (by trivial) message tail path)
    | ok aborted=>
      simp only [moved] at path
      rcases RegistrationNativePlatformLorSourcePreparedPrefix.bind_query_cases implementation _ _ before _ tail after path with first|later
      · obtain ⟨firstTail,firstPath⟩ := first
        have quiet := route_free (n := n) setup scalar _ (RegistrationNativeSecretWordFrontendCapsBeacon.preparation_free setup source packet owner env)
        exact False.elim (no_demand implementation quiet message firstTail firstPath)
      · obtain ⟨reached,middle,called,laterPath⟩ := later
        cases readyEq : reached.1.1 with
        | fail error | div=>
          have quiet := after_none (n := n) (KemSK := KemSK) setup scalar setup.source wire.frameWrite owner reached.1.2 reached.2 reached.1.1 (by intro reference;rw [readyEq];intro h;cases h)
          exact False.elim (no_demand implementation quiet message tail laterPath)
        | ok selected=>cases selected with
          | none=>
            have quiet := after_none (n := n) (KemSK := KemSK) setup scalar setup.source wire.frameWrite owner reached.1.2 reached.2 reached.1.1 (by intro reference;rw [readyEq];intro h;cases h)
            exact False.elim (no_demand implementation quiet message tail laterPath)
          | some ready=>
            have prepared := RegistrationNativePlatformLorSourceBeaconPreparedSeen.preparation setup implementation input echo seen recorded scalar packet owner env before (reached,middle)
              (by rw [scalar_compose,QueryImpl.simulateQ_compose];exact called) ready readyEq
            exact only_prepared implementation seen keeps ready.reference _ (complete_only setup scalar setup.source wire.frameWrite owner reached.1.2 ready reached.2) middle after prepared message tail (by simpa only [close,readyEq,RegistrationNativePlatformSecretWordFinish.afterPrepared] using laterPath)


omit keeps echo recorded in
private theorem map_query_cases (work : OracleComp (Spec n KemSK) A) (change : A →B)
    (before after : Current) (message : Message)
    (tail : (Spec n KemSK).Range (.inl (.inr (.inl (.inl message)))) →OracleComp (Spec n KemSK) B)
    (path : Prefix implementation (change <$>work) before ((Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) :
    ∃firstTail,Prefix implementation work before ((Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) >>=firstTail) after := by
  have same : change <$>work=work >>=fun value=>pure (change value) := (bind_pure_comp change work).symm
  rw [same] at path
  rcases RegistrationNativePlatformLorSourcePreparedPrefix.bind_query_cases implementation _ _ before _ tail after path with first|later
  · exact first
  · obtain ⟨value,middle,_called,laterPath⟩ := later
    exact False.elim (no_demand implementation (by trivial) message tail laterPath)

/-- A demand in the literal public Word finish follows its own inline preparation; missing owners and every failed callback branch are retained. -/
theorem frontend {Platform : Type} (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (index : Nat) (packet : Option registration.ResponsePacket)
    (beforeFront : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (before after : Current) (message : Message)
    (tail : (Spec n KemSK).Range (.inl (.inr (.inl (.inl message)))) →OracleComp (Spec n KemSK)
      (RustM (Option Pqxdh.Bytes) ×RegistrationNativePlatformSecretWordOrdinary.State source Platform))
    (path : Prefix implementation ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) (KemSK := KemSK)
      setup wire source index packet).run beforeFront) before
      ((Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) :
    Prepared message (seen after) := by
  simp only [RegistrationNativePlatformSecretWordFrontend.finish,StateT.run] at path
  cases found : beforeFront.1.beacons[index]? with
  | none=>
    simp only [found] at path
    exact False.elim (no_demand implementation (by trivial) message tail path)
  | some owner=>
    simp only [found] at path
    obtain ⟨firstTail,firstPath⟩ := map_query_cases implementation _ _ before after message tail path
    have original : Prefix implementation
        (close setup owner.scalar (RegistrationNativePlatformSecretWordFinish.finish setup wire source packet) owner.view beforeFront.1.environment)
        before ((Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) >>=firstTail) after := by
      cases scalarEq : owner.scalar with
      | none=>simpa only [scalarEq,close,compile,RegistrationNativeSecretWordAtomOwnerSource.routing,StateT.run] using firstPath
      | some scalar=>simpa only [scalarEq,close,compile,RegistrationNativeSecretWordAtomOwnerSource.routing,QueryImpl.simulateQ_compose,StateT.run] using firstPath
    exact local_finish implementation seen keeps setup input echo recorded wire owner.scalar source packet owner.view
      beforeFront.1.environment before after message firstTail original

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedPrefix.local_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedPrefix.local_finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedPrefix.frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedPrefix.frontend
