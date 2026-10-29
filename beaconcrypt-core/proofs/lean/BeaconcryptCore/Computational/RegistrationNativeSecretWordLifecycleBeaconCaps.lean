-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerCredit

/-! The exact Beacon preparation has one indexed decapsulation position. Every conversion and selected-DH reference retains its actual callback effects, and the operand is the selected owner's stored opaque handle. Material demand, opening, installation and terminal failure contain no further KEM getter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

def IsDecap : (Spec n KemSK).Domain → Prop
  | .inr (.inr (.inr (.inl (.decapsulate _ _)))) => True
  | _ => False
instance : DecidablePred (IsDecap (n := n) (KemSK := KemSK)) := fun query => by
  unfold IsDecap
  split <;> infer_instance

def PrimitiveDecap : RegistrationAgreementExecutor.Spec.Domain → Prop
  | .decapsulate _ => True
  | _ => False
instance : DecidablePred PrimitiveDecap := fun query => by cases query <;> first | exact isTrue trivial | exact isFalse id

def PrefixDecap {I D K X Response : Type} : PqxdhPhase2GapDhSource.Query I D K X Response → Prop
  | .decapsulate _ _ => True
  | _ => False
instance {I D K X Response : Type} : DecidablePred (PrefixDecap (I := I) (D := D) (K := K) (X := X) (Response := Response)) := fun query => by
  cases query <;> first | exact isTrue trivial | exact isFalse id

def AuxDecap {I D K X Response : Type} : PqxdhBeaconPhase2Preparation.Query I D K X Response → Prop
  | .decapsulate _ _ => True
  | _ => False
instance {I D K X Response : Type} : DecidablePred (AuxDecap (I := I) (D := D) (K := K) (X := X) (Response := Response)) := fun query => by
  cases query <;> first | exact isTrue trivial | exact isFalse id

/-- The original twelve-position optional collector has one decapsulation position, including every earlier failure. -/
theorem collector_one {I D K X Response : Type} (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (PqxdhPhase2GapDhSource.collect (X := X) (Response := Response) identity oneTime kem raw).IsQueryBoundP PrefixDecap 1 := by
  unfold PqxdhPhase2GapDhSource.collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
    Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [PrefixDecap], ?_⟩)
    | (fail_if_no_progress simp only [Option.elim_some])
    | (intro answer; cases answer)

private theorem environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsDecap (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsDecap, isQueryBoundP_query_iff]

private theorem sample_free (work : ProbComp Value) :
    (sample (n := n) (KemSK := KemSK) work).IsQueryBoundP (IsDecap (KemSK := KemSK)) 0 := by
  unfold sample
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsDecap, isQueryBoundP_query_iff]

/-- The actual source decapsulation operand is the retained opaque KEM handle and actual received ciphertext, without equating it to any owner index. -/
theorem decapsulation_handle (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (ciphertext : Std.Array U8 1088#usize) :
    primitive (n := n) setup owner oneTime (.decapsulate (.Some ciphertext)) =
      (fun reply => RegistrationAgreementRoot.nativeOption (reply.map PqxdhRootTableInitialization.rootArray)) <$>
        indexed (.inr (.inl (.decapsulate owner.kemHandle (PqxdhPhase2InputBytes.ciphertext ciphertext)))) := by
  simp only [primitive, RegistrationNativeKemInterface.beacon, simulateQ_map, simulateQ_spec_query]

private theorem primitive_bound (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    (primitive (n := n) setup owner oneTime query).IsQueryBoundP (IsDecap (KemSK := KemSK))
      (match query with | .decapsulate _ => 1 | _ => 0) := by
  cases query with
  | convertPublic key | convertSecret role | generate role | dh request =>
      simpa only [primitive, RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        simulateQ_spec_query, other] using sample_free (n := n) (KemSK := KemSK) _
  | encapsulate key => simp only [primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure]; trivial
  | decapsulate ciphertext => cases ciphertext with
    | none => simp only [primitive, RegistrationNativeKemInterface.beacon, simulateQ_pure]; trivial
    | some ciphertext =>
        rw [decapsulation_handle]
        simp [indexed, IsDecap, isQueryBoundP_query_iff]

private theorem backend_bound (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : EnvState Auxiliary) :
    ((backend (n := n) setup owner oneTime query).run before).IsQueryBoundP (IsDecap (KemSK := KemSK))
      (if PrimitiveDecap query then 1 else 0) := by
  simp only [backend, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift,
    bind_pure_comp, isQueryBoundP_map_iff]
  cases query <;> first | exact primitive_bound setup owner oneTime _ | trivial

private theorem backend_program_bound (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP PrimitiveDecap cap) (before : EnvState Auxiliary) :
    ((simulateQ (backend (n := n) setup owner oneTime) work).run before).IsQueryBoundP (IsDecap (KemSK := KemSK)) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query charged current
    simpa only [ite_eq_left charged] using backend_bound setup owner oneTime query current
  · intro query quiet current
    simpa only [ite_eq_right quiet] using backend_bound setup owner oneTime query current

private theorem callback_bound (authenticated : registration.AuthenticatedResponse)
    (query : RegistrationBeaconAgreementRoot.PrefixSpec.Domain) :
    (RegistrationBeaconAgreementRoot.callbacks authenticated query).IsQueryBoundP PrimitiveDecap
      (if AuxDecap query then 1 else 0) := by
  cases query <;> simp [RegistrationBeaconAgreementRoot.callbacks, AuxDecap, PrimitiveDecap,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem prefix_bound (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain)
    (before : EnvState Auxiliary) :
    ((PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
      (RegistrationBeaconRootInterpreter.auxImpl (backend (n := n) setup owner oneTime) authenticated) visit query).run before).IsQueryBoundP
      (IsDecap (KemSK := KemSK)) (if PrefixDecap query then 1 else 0) := by
  cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl, RegistrationBeaconRootInterpreter.auxImpl]
  all_goals first
    | exact backend_program_bound setup owner oneTime _ _ (callback_bound authenticated _) before
    | trivial

/-- Exact metadata admission adds no KEM callback after the sole decapsulation. -/
theorem collect_bound (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsDecap (KemSK := KemSK)) 1 := by
  unfold collect
  have original : (PqxdhPhase2DhMetadata.prepare authenticated.pending.control () () () []).IsQueryBoundP
      (PrefixDecap (X := Unit) (Response := registration.AuthenticatedResponse)) 1 := by
    simp only [PqxdhPhase2DhMetadata.prepare, bind_pure_comp, isQueryBoundP_map_iff]
    exact collector_one () () () []
  apply original.simulateQ_run_of_step
  · intro query charged current
    simpa only [ite_eq_left charged] using prefix_bound setup owner oneTime authenticated query current
  · intro query quiet current
    simpa only [ite_eq_right quiet] using prefix_bound setup owner oneTime authenticated query current

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem prepare_free (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    (simulateQ (prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsDecap (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [prepare, IsDecap, isQueryBoundP_query_iff]

private theorem agreement_bound (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP (IsDecap (KemSK := KemSK)) 1 := by
  simp only [agreement, StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (collect_bound setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
      simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
        prepare_free (n := n) (KemSK := KemSK) (RegistrationBeaconReferenceRoot.client authenticated pending)

/-- Response authentication precedes at most one actual indexed decapsulation. -/
theorem preparation_bound (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner mlSource) (before : EnvState Auxiliary) :
    (((finishPreparation (n := n) setup mlSource packet).run owner).run before).IsQueryBoundP (IsDecap (KemSK := KemSK)) 1 := by
  simp only [finishPreparation, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh => trivial
  | freshWithCoins oneTime => trivial
  | established completed => trivial
  | aborted aborted => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error => simp only [moved, StateT.run_pure]; trivial
      | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc]
          apply isQueryBoundP_bind (n := 0) (m := 1) (environment_free _)
          intro accepted _
          cases accepted with
          | fail error => trivial
          | div => trivial
          | ok reply => cases reply with
            | Err error => trivial
            | Ok authenticated =>
                simpa only [StateT.run_lift, StateT.run_map, bind_pure_comp, map_apply, isQueryBoundP_map_iff] using
                  agreement_bound setup owner oneTime authenticated before

private theorem service_free (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value) :
    (simulateQ (RegistrationBeaconReferenceFinish.service (KemSK := KemSK)) work).IsQueryBoundP (IsDecap (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationBeaconReferenceFinish.service, IsDecap, isQueryBoundP_query_iff]

private theorem abort_free {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.abort (n := n) (KemSK := KemSK) owner).run current).run before).IsQueryBoundP
      (IsDecap (KemSK := KemSK)) 0 := by
  simp only [RegistrationBeaconReferenceFinish.abort,
    bind_pure_comp]
  simp [effect, IsDecap, isQueryBoundP_query_iff]

/-- Prepared owner completion performs no further indexed decapsulation, including every opening and installation failure. -/
theorem complete_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) source owner ready).run current).run before).IsQueryBoundP
      (IsDecap (KemSK := KemSK)) 0 := by
  simp only [RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_map_left, bind_pure_comp]
  apply isQueryBoundP_bind (n := 0) (m := 0) (service_free
    (RegistrationNativePairedBeaconService.admitted source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference))
  intro completed _
  cases completed with
  | fail error =>
      simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply,
        isQueryBoundP_map_iff] using abort_free (KemSK := KemSK) owner current before
  | div =>
      simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply,
        isQueryBoundP_map_iff] using abort_free (KemSK := KemSK) owner current before
  | ok completed => cases completed with
    | Err aborted =>
        simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply,
          isQueryBoundP_map_iff] using abort_free (KemSK := KemSK) owner current before
    | Ok completed => trivial

/-- The actual full selected-owner finish has one decapsulation only after passing its terminal-move gate; every other phase/gate is decapsulation-free. -/
theorem finish_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.finish (n := n) (KemSK := KemSK) setup source packet).run owner).run before).IsQueryBoundP
      (IsDecap (KemSK := KemSK)) (if RegistrationNativeSecretWordLifecycleOwnerCredit.canFinish owner.phase then 1 else 0) := by
  simp only [RegistrationBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins oneTime | established completed | aborted aborted =>
      simp only [RegistrationNativeSecretWordLifecycleOwnerCredit.canFinish]
      trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, StateT.run_pure, RegistrationNativeSecretWordLifecycleOwnerCredit.canFinish, Bool.false_eq_true, ite_false]
          trivial
      | ok aborted =>
          simp only [RegistrationNativeSecretWordLifecycleOwnerCredit.canFinish, moved, ite_true]
          apply isQueryBoundP_bind (n := 1) (m := 0) (preparation_bound setup source packet owner before)
          intro result _
          rcases result with ⟨⟨prepared, current⟩, env⟩
          cases prepared with
          | fail error | div =>
              simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                (abort_free (KemSK := KemSK) owner current env)
          | ok prepared => cases prepared with
            | none =>
                simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                  (abort_free (KemSK := KemSK) owner current env)
            | some ready => exact complete_free setup.source owner current ready env

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.collector_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.collector_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.decapsulation_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.decapsulation_handle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.collect_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.preparation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.preparation_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.complete_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.complete_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleBeaconCaps.finish_bound
