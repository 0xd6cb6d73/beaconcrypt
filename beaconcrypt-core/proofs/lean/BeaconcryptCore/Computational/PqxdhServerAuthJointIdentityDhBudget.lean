import BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources

/-! Static-DH accounting for the actual joint identity reduction, retaining every rejected finish attempt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget
open PqxdhJointIdentity PqxdhServerAuthExperiment
open PqxdhServerAuthJointIdentityCompiler PqxdhServerAuthJointIdentityLog
open PqxdhJointGapDh (ScalarBytes)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Exact optional static-DH requests to the joint challenger. -/
def IsDh : AdversarySpec.Domain → Prop
  | .inr (.staticDh _) => True
  | _ => False

instance : DecidablePred IsDh := fun query => by
  rcases query with coin | (message | point) <;> simp only [IsDh] <;> infer_instance

/-- Source callback that consumes the converted identity secret; all scalar DH work stays local. -/
def IdentityDh {I D K X R : Type} : (PqxdhBeaconPhase2Preparation.Spec I D K X R).Domain → Prop
  | .dhIdentity _ _ => True
  | _ => False

instance {I D K X R : Type} : DecidablePred (IdentityDh (I := I) (D := D) (K := K) (X := X) (R := R)) :=
  fun query => by cases query <;> simp only [IdentityDh] <;> infer_instance

/-- Local uniform and fully interpreted primitive/base work cannot access the target static-DH service. -/
theorem coins_no_dh {Result : Type} (work : ProbComp Result) :
    (coins work).IsQueryBoundP IsDh 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [coins, simulateQ_bind, simulateQ_spec_query, isQueryBoundP_query_bind_iff,
      IsDh, not_false_eq_true, true_or, true_and] at *
    exact ih

set_option maxHeartbeats 1000000 in
/-- Every original preparation path reaches at most one converted-identity DH callback, including malformed inputs and primitive rejection. -/
theorem collect_identity {I D K X R : Type} (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (PqxdhBeaconPhase2Preparation.collect (X := X) (Response := R) identity prekey oneTime kem raw).IsQueryBoundP
      IdentityDh 1 := by
  unfold PqxdhBeaconPhase2Preparation.collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [IdentityDh], ?_⟩)
    | (fail_if_no_progress simp only [Option.elim_some])
    | intro answer; cases answer

/-- Core preparation and mandatory shared-secret erasure add no identity-DH callback. -/
theorem prepare_identity {I D K X R : Type} (control : pqxdh.BeaconInitSent)
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (PqxdhBeaconPhase2Preparation.prepare (X := X) (Response := R) control identity prekey oneTime kem raw).IsQueryBoundP
      IdentityDh 1 := by
  unfold PqxdhBeaconPhase2Preparation.prepare
  refine isQueryBoundP_bind (n := 1) (m := 0) (collect_identity identity prekey oneTime kem raw) ?_
  rintro (_ | input) _
  · trivial
  · simp [PqxdhBeaconPhase2Preparation.afterInputs, IdentityDh]

set_option backward.isDefEq.respectTransparency false in
/-- The actual auxiliary interpreter forwards exactly one logical joint DH call for the identity callback; KEM, base and uniform work stays local. -/
theorem auxiliary_dh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response).Domain) :
    (auxiliary setup codec query).IsQueryBoundP IsDh (if IdentityDh query then 1 else 0) := by
  cases query <;> simp only [auxiliary, IdentityDh, ite_true, ite_false, isQueryBoundP_pure,
    coins_no_dh, isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsDh, true_implies, Nat.one_pos]
  rename_i pair point
  cases pair <;> trivial

set_option backward.isDefEq.respectTransparency false in
/-- The selected-prekey wrapper keeps the exact logical identity-DH bill, while its selected scalar callback remains local. -/
theorem prefix_dh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (scalar : ScalarBytes)
    (query : (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ (Unit ⊕ ScalarBytes)) KemSK Unit Response).Domain)
    (state : Unit) :
    ((prefixImpl setup codec scalar query).run state).IsQueryBoundP IsDh (if IdentityDh query then 1 else 0) := by
  cases query <;> simp only [prefixImpl, PqxdhPhase2GapDhSource.nativeImpl, StateT.run_lift, bind_pure_comp,
    isQueryBoundP_map_iff]
  all_goals try exact auxiliary_dh setup codec _
  rename_i pair point
  cases pair <;> simp only [StateT.run, StateT.lift, bind_pure_comp, isQueryBoundP_map_iff]
  all_goals first | exact auxiliary_dh setup codec _ | trivial

set_option backward.isDefEq.respectTransparency false in
/-- The complete original preparation forwards at most one optional static-DH query. All parsing, KEM and scalar-DH rejection branches are retained. -/
theorem prepare_dh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    (prepare setup codec scalar control identity oneTime kem raw).IsQueryBoundP IsDh 1 := by
  simp only [prepare, StateT.run'_eq, isQueryBoundP_map_iff]
  have source := prepare_identity (X := Unit) (R := Response) control identity
    (Sum.inl () : Unit ⊕ (Unit ⊕ ScalarBytes)) (.inr oneTime) kem raw
  exact source.simulateQ_run_StateT_of_step
    (fun query state => prefix_dh setup codec scalar query state) ()

/-- Root derivation, opening, publication and all local primitive work add no target static-DH query after preparation. -/
theorem stage_dh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (control : pqxdh.BeaconInitSent)
    (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((stage setup codec serverSeed scalar control identity oneTime kem raw).run state).IsQueryBoundP IsDh 1 := by
  simp only [stage, StateT.run]
  refine isQueryBoundP_bind (n := 1) (m := 0) (prepare_dh setup codec scalar control identity oneTime kem raw) ?_
  rintro (_ | original) _
  · trivial
  · exact coins_no_dh _

/-- One original finish makes at most one logical target static-DH request, whether it succeeds, rejects, aborts or is inactive. -/
theorem finish_dh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((finish setup codec serverSeed scalar raw).run state).IsQueryBoundP IsDh 1 := by
  simp only [finish, StateT.run]
  cases state.2.beacon.beacon.phase <;> simp only [isQueryBoundP_pure]
  rename_i control prekey oneTime kem
  exact isQueryBoundP_bind (n := 1) (m := 0)
    (stage_dh setup codec serverSeed scalar control state.2.beacon.beacon.identity oneTime kem raw state)
    (fun _ _ => trivial)

/-- All attempted original Beacon finishes, including calls that reject or arrive after termination. -/
def IsFinish : ServerAuthSpec.Domain → Prop
  | .inr (.finish _) => True
  | _ => False

instance : DecidablePred IsFinish := fun query => by
  rcases query with coin | request
  · simp only [IsFinish]; infer_instance
  · cases request <;> simp only [IsFinish] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Every native API callback pays its own identity-DH allowance; all nontarget and local primitive work remains executed. -/
theorem handler_dh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (query : ServerAuthSpec.Domain)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((handler setup codec checks serverSeed scalar query).run state).IsQueryBoundP IsDh
      (if IsFinish query then 1 else 0) := by
  rcases query with coin | (raw | build | raw | hmac | bytes | key)
  all_goals simp only [handler, StateT.run, IsFinish, ite_true, ite_false]
  all_goals first | exact coins_no_dh _ | exact finish_dh setup codec serverSeed scalar _ state

/-- The complete adaptive public program makes at most one joint static-DH query per attempted finish. The source cap counts every possible reply path. -/
theorem program_dh {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp ServerAuthSpec Result)
    (qFinish : Nat) (bounded : work.IsQueryBoundP IsFinish qFinish)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((simulateQ (handler setup codec checks serverSeed scalar) work).run state).IsQueryBoundP IsDh qFinish := by
  exact bounded.simulateQ_run_StateT_of_step
    (fun query state => handler_dh setup codec checks serverSeed scalar query state) state

set_option backward.isDefEq.respectTransparency false in
/-- The original Phase1 publication performs its three signature calls but never accesses the joint static-DH interface. -/
theorem phase1_no_dh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (target : PublicIdentity) (publicValue : PqxdhJointGapDh.PublicChallenge) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) :
    (phase1 setup codec target publicValue oneTime kemPk kemSk).IsQueryBoundP IsDh 0 := by
  unfold phase1
  apply (isQueryBoundP_false _ 0).simulateQ_of_step
  · intro query impossible
    exact impossible.elim
  · intro query _
    rcases query with gen | ((coin | request) | bundle)
    all_goals try simp only [signingImpl, isQueryBoundP_pure, isQueryBoundP_query_iff, IsDh, false_implies]
    cases request <;> try trivial
    rename_i index service
    cases service <;> simp [IsDh]

/-- The complete publication/API execution spends only the attempted-finish static-DH allowance; arbitrary identity candidates do not add a target DH oracle capability. -/
theorem execution_dh {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (qFinish : Nat)
    (bounded : ∀ input, (work input).IsQueryBoundP IsFinish qFinish) (target : PublicIdentity) :
    (execution setup codec checks serverSeed scalar oneTime keys work target).IsQueryBoundP IsDh qFinish := by
  unfold execution
  refine (isQueryBoundP_bind (n := 0) (m := qFinish)
    (phase1_no_dh setup codec target _ oneTime keys.1 keys.2) ?_).mono (by omega)
  intro published _
  refine (isQueryBoundP_bind (n := qFinish) (m := 0)
    (program_dh setup codec checks serverSeed scalar _ qFinish (bounded _) _) ?_).mono (by omega)
  intro result _
  trivial

/-- Source generation and journal recording preserve the original attempted-finish cap for the full concrete primitive client. -/
theorem capture_dh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qFinish : Nat)
    (bounded : ∀ input, (adversary input).IsQueryBoundP IsFinish qFinish) (target : PublicIdentity) :
    (PqxdhServerAuthJointIdentityEuf.capture setup codec checks adversary target).IsQueryBoundP IsDh qFinish := by
  unfold PqxdhServerAuthJointIdentityEuf.capture
  refine (isQueryBoundP_bind (n := 0) (m := qFinish) (coins_no_dh _) (fun serverSeed _ => ?_)).mono (by omega)
  refine (isQueryBoundP_bind (n := 0) (m := qFinish) (coins_no_dh _) (fun scalar _ => ?_)).mono (by omega)
  refine (isQueryBoundP_bind (n := 0) (m := qFinish) (coins_no_dh _) (fun keys _ => ?_)).mono (by omega)
  refine (isQueryBoundP_bind (n := 0) (m := qFinish) (coins_no_dh _) (fun oneTime _ => ?_)).mono (by omega)
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  exact execution_dh setup codec checks serverSeed scalar oneTime keys _ qFinish
    (fun input => (PqxdhServerAuthApiJournal.query_bound (adversary input) IsFinish qFinish).mpr (bounded input)) target

/-- The same constructed coefficient-one weak-EUF reduction has logical static-DH cap qFinish, with every attempted finish counted. This bound is conservative for the one-shot owner. -/
theorem reduction_dh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (qFinish : Nat)
    (bounded : ∀ input, (adversary input).IsQueryBoundP IsFinish qFinish)
    (fallback : Forgery) (target : PublicIdentity) :
    (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary fallback target).IsQueryBoundP IsDh qFinish :=
  (PqxdhServerAuthJointIdentityResources.reduction_queries setup codec checks adversary fallback target IsDh qFinish).mpr
    (capture_dh setup codec checks adversary qFinish bounded target)

end BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget

/-! Checked theorem dependencies. -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.coins_no_dh' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.coins_no_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.collect_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.collect_identity
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.prepare_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.prepare_identity
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.auxiliary_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.auxiliary_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.prefix_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.prefix_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.prepare_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.prepare_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.stage_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.stage_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.finish_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.finish_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.handler_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.handler_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.program_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.program_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.phase1_no_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.phase1_no_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.execution_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.execution_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.capture_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.capture_dh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.reduction_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget.reduction_dh
