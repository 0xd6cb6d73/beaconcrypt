-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaChronology
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundle

/-! Every actual reified outgoing Beacon callback appends the same chronological complete-request attempt and native unsigned-payload receipt at the true-count private table. Hash and Ed callbacks preserve both histories; no closed opaque signer is used for the named ML branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaChronology (Aligned append call_history)
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativeMldsaRequestAlignment (BeaconQuery)
open RegistrationNativeMldsaTableProgram (runState evaluate handler)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

private theorem hash_receipts (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source)) (request : registration.HashRequest)
    (before : Local n KemSK (handleSource source))
    (result : CtxRomAuth.CtxDigest × Local n KemSK (handleSource source))
    (supported : result ∈ support ((lower setup checks representation created
      (RegistrationNativeBeaconFrontend.outgoing setup (handleSource source) index owner (.inl (.hash request)))).run before)) :
    result.2.2.1.receipts = before.2.1.receipts := by
  have projected : (result.1, project result.2) ∈ support
      ((RegistrationNativeMldsaShared.implementation setup owner (.inl (.hash request))).run (project before)) := by
    rw [← RegistrationNativeMldsaShared.outgoing setup checks representation created index owner _ before, support_map]
    exact Set.mem_image_of_mem (Prod.map id project) supported
  simp only [RegistrationNativeMldsaShared.implementation, RegistrationSigningShared.implementation,
    MldsaSharedNative.authentication, StateT.run, support_map] at projected
  obtain ⟨hashed, _queried, same⟩ := projected
  exact (congrArg (fun value : CtxRomAuth.CtxDigest × RegistrationSigningShared.State => value.2.1) same).symm

private theorem ed_receipts (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source)) (request : registration.Ed25519SigningRequest)
    (before : Local n KemSK (handleSource source))
    (result : RegistrationSigningShared.SignReply × Local n KemSK (handleSource source))
    (supported : result ∈ support ((lower setup checks representation created
      (RegistrationNativeBeaconFrontend.outgoing setup (handleSource source) index owner (.inr request))).run before)) :
    result.2.2.1.receipts = before.2.1.receipts := by
  have projected : (result.1, project result.2) ∈ support
      ((RegistrationNativeMldsaShared.implementation setup owner (.inr request)).run (project before)) := by
    rw [← RegistrationNativeMldsaShared.outgoing setup checks representation created index owner _ before, support_map]
    exact Set.mem_image_of_mem (Prod.map id project) supported
  simp only [RegistrationNativeMldsaShared.implementation, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at projected
  exact congrArg (fun value : RegistrationSigningShared.SignReply × RegistrationSigningShared.State => value.2.1) projected

/-- An actual outgoing Beacon callback links its complete private request to the same source payload/digest receipt, including failed replies. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source))
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (correct : BeaconQuery query)
    (before : Local n KemSK (handleSource source)) (pool : Pool source)
    (result : (RegistrationBeaconInitExecutor.Spec.Range query × Local n KemSK (handleSource source)) × Pool source)
    (aligned : Aligned pool.signing before.2.1.receipts)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner query) before pool)) :
    Aligned result.2.signing result.1.2.2.1.receipts := by
  cases query with
  | inl query => cases query with
    | hash request =>
        change result ∈ support (runState source (RegistrationNativeMldsaBundle.native setup checks representation created
          (RegistrationNativeBeaconFrontend.outgoing setup (handleSource source) index owner (.inl (.hash request)))) before pool) at supported
        rw [RegistrationNativeMldsaBundle.native, RegistrationNativeMldsaTableProgram.run_liftState, support_map] at supported
        obtain ⟨reply, possible, same⟩ := supported
        cases same
        rw [hash_receipts source setup checks representation created index owner request before reply possible]
        exact aligned
    | sign request payload digest =>
        simp only [RegistrationNativeMldsaBundle.outgoing, StateT.run, bind_pure_comp, runState, evaluate,
          simulateQ_map, map_apply, support_map] at supported
        obtain ⟨reply, possible, same⟩ := supported
        cases same
        have history := call_history source .environment before.2.2.server.world.world.1 pool owner.mldsa request reply possible
        dsimp only [Prod.map, id] at ⊢
        rw [history]
        exact append _ _ _ _ aligned ⟨rfl, correct, rfl⟩
  | inr request =>
      change result ∈ support (runState source (RegistrationNativeMldsaBundle.native setup checks representation created
        (RegistrationNativeBeaconFrontend.outgoing setup (handleSource source) index owner (.inr request))) before pool) at supported
      rw [RegistrationNativeMldsaBundle.native, RegistrationNativeMldsaTableProgram.run_liftState, support_map] at supported
      obtain ⟨reply, possible, same⟩ := supported
      cases same
      rw [ed_receipts source setup checks representation created index owner request before reply possible]
      exact aligned

/-- Whole actual outgoing Init programs preserve the complete chronological source/table history correspondence. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source))
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) (correct : work.AllQueriesSatisfy BeaconQuery)
    (before : Local n KemSK (handleSource source)) (pool : Pool source)
    (result : (Value × Local n KemSK (handleSource source)) × Pool source)
    (aligned : Aligned pool.signing before.2.1.receipts)
    (supported : result ∈ support (runState source
      (simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner) work) before pool)) :
    Aligned result.2.signing result.1.2.2.1.receipts := by
  induction work using OracleComp.inductionOn generalizing before pool with
  | pure value =>
      rw [simulateQ_pure, RegistrationNativeMldsaTableProgram.run_pure] at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact aligned
  | query_bind query next ih =>
      obtain ⟨head, tail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp correct
      rw [simulateQ_bind, simulateQ_spec_query, RegistrationNativeMldsaTableProgram.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact ih middle.1.1 (tail middle.1.1) middle.1.2 middle.2
        (outgoing source setup checks representation created index owner query head before pool middle aligned queried) continued

/-- Actual complete Init signing derives request alignment itself from the source continuations, without a correct-request premise at the use site. -/
theorem begin (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source))
    (encode : registration.SignedInitView → core.option.Option Value)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (before : Local n KemSK (handleSource source)) (pool : Pool source)
    (result : (RustM (RegistrationBeaconInitExecutor.Result Value) × Local n KemSK (handleSource source)) × Pool source)
    (aligned : Aligned pool.signing before.2.1.receipts)
    (supported : result ∈ support (runState source
      (simulateQ (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner)
        (RegistrationBeaconInitExecutor.begin encode control inputs coins pin mldsa)) before pool)) :
    Aligned result.2.signing result.1.2.2.1.receipts :=
  program source setup checks representation created index owner _
    (RegistrationNativeMldsaRequestAlignment.Beacon.begin_all encode control inputs coins pin mldsa) before pool result aligned supported

private def NoSign (work : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → result.2.receipts = env.receipts

private theorem noSign_lift (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    NoSign source (StateT.lift (StateT.lift work) : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl
private theorem noSign_get : NoSign source
    (get : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State
      (RegistrationNativeBeaconFrontend.State (handleSource source))) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem noSign_phase (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    NoSign source (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK)
      (mldsaSource := handleSource source) (Auxiliary := RegistrationServerRoleBackend.State) index phase) := by
  intro owners env result supported
  simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem noSign_sample (draw : ProbComp Value) :
    NoSign source (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK)
      (mldsaSource := handleSource source) (Auxiliary := RegistrationServerRoleBackend.State) draw) := by
  have lift_bind {A B : Type}
      (work : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State A)
      (next : A → RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State B)
      (first : NoSign source work) (rest : ∀ value, NoSign source (next value)) : NoSign source (work >>= next) := by
    intro owners env result supported
    simp only [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, queried, continued⟩ := supported
    exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle queried)
  induction draw using OracleComp.inductionOn with
  | pure value =>
      intro owners env result supported
      simp only [RegistrationNativeBeaconFrontend.sample, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      simp only [RegistrationNativeBeaconFrontend.sample, simulateQ_bind, simulateQ_spec_query]
      exact lift_bind _ _ (noSign_lift source _) ih

private def Keeps (work : StateT (Local n KemSK (handleSource source))
    (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Value) : Prop :=
  ∀ before pool result, Aligned pool.signing before.2.1.receipts →
    result ∈ support (runState source work before pool) → Aligned result.2.signing result.1.2.2.1.receipts

private theorem pure_keeps (value : Value) : Keeps source
    (pure value : StateT (Local n KemSK (handleSource source)) _ Value) := by
  intro before pool result aligned supported
  rw [RegistrationNativeMldsaTableProgram.run_pure] at supported
  simp only [support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact aligned
private theorem bind_keeps {Next : Type}
    (work : StateT (Local n KemSK (handleSource source)) (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Value)
    (next : Value → StateT (Local n KemSK (handleSource source)) (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Next)
    (first : Keeps source work) (rest : ∀ value, Keeps source (next value)) : Keeps source (work >>= next) := by
  intro before pool result aligned supported
  rw [RegistrationNativeMldsaTableProgram.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first before pool middle aligned queried) continued

private theorem native_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State Value)
    (law : NoSign source work) : Keeps source (RegistrationNativeMldsaBundle.native setup checks representation created work) := by
  intro before pool result aligned supported
  rw [RegistrationNativeMldsaBundle.native, RegistrationNativeMldsaTableProgram.run_liftState, support_map] at supported
  obtain ⟨reached, possible, same⟩ := supported
  cases same
  have retained : reached.2.2.1.receipts = before.2.1.receipts := by
    simp only [lower, StateT.run, support_map] at possible
    obtain ⟨inner, called, same⟩ := possible
    cases same
    apply law before.1 before.2.1 inner.1
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created (handleSource source)) _ before.2.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  rw [retained]
  exact aligned

private theorem afterPublished_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source)) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (published : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Keeps source (RegistrationNativeMldsaBundle.afterPublished (n := n) setup checks representation created index owner oneTime published) := by
  cases published with
  | fail error | div => exact pure_keeps source _
  | ok answer => cases answer with
    | Err previous => exact pure_keeps source _
    | Ok completed =>
        unfold RegistrationNativeMldsaBundle.afterPublished
        apply bind_keeps source _ _ (native_keeps source setup checks representation created _ (noSign_phase source index _))
        intro ignored
        exact bind_keeps source _ _ (native_keeps source setup checks representation created _ (noSign_lift source _))
          (fun _ => pure_keeps source _)

attribute [local irreducible] RegistrationBeaconInitExecutor.begin
  RegistrationNativeMldsaBundle.outgoing

set_option maxHeartbeats 1000000 in
/-- Actual complete reified bundle callbacks preserve correspondence of every prior and reached ML attempt and native payload receipt, including failed publication. -/
theorem bundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (before : Local n KemSK (handleSource source)) (pool : Pool source)
    (result : (RustM (Option Pqxdh.Bytes) × Local n KemSK (handleSource source)) × Pool source)
    (aligned : Aligned pool.signing before.2.1.receipts)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaBundle.bundle setup checks wire representation created index) before pool)) :
    Aligned result.2.signing result.1.2.2.1.receipts := by
  have law : Keeps source (RegistrationNativeMldsaBundle.bundle (n := n) (source := handleSource source)
      setup checks wire representation created index) := by
    unfold RegistrationNativeMldsaBundle.bundle
    apply bind_keeps source _ _ (native_keeps source setup checks representation created _ (noSign_get source))
    intro owners
    cases owners[index]? with
    | none => exact pure_keeps source _
    | some owner =>
        dsimp only
        cases owner.phase with
        | fresh | freshWithCoins _ =>
            apply bind_keeps source _ _ ?_
            · intro oneTime
              apply bind_keeps source _ _ (begin source setup checks representation created index owner wire.encodeInit
                ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
                ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
              exact afterPublished_keeps source setup checks representation created index owner oneTime
            · first | exact pure_keeps source _
                    | exact native_keeps source setup checks representation created _ (noSign_sample source _)
        | _ => exact pure_keeps source _
  exact law before pool result aligned supported

/-- The outer original native closure publishes that same chronological correspondence into the literal global ML receipt list. -/
theorem sourceBundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (pool : Pool source)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (aligned : Aligned pool.signing before.server.world.world.2)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaBundle.sourceBundle setup checks wire representation created index) before pool)) :
    Aligned result.2.signing result.1.2.server.world.world.2 := by
  simp only [RegistrationNativeMldsaBundle.sourceBundle, StateT.run, runState, evaluate,
    simulateQ_map, map_apply, support_map] at supported
  obtain ⟨reached, possible, same⟩ := supported
  cases same
  exact bundle source setup checks wire representation created index _ pool reached aligned possible

end BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology.begin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology.bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology.sourceBundle
