-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityOutgoingSource

/-! Native owner Ed histories are analysis metadata. Their signed-message order can be retained with one public placeholder in every signature slot. Actual input selection and source outgoing callbacks never inspect these earlier signature bytes. This view is separate from the ordinary challenger's private signing history, which remains literal for freshness. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView
open PqxdhJointIdentity (History)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityFrontend (Owner State M)
open PqxdhServerAuthExperiment (Setup)
variable {I KemSK Auxiliary Value : Type} {base : OracleSpec I} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def history (placeholder : Ed25519Signature) (before : History) : History := before.map fun event =>
  match event with
  | .signed message _ => .signed message placeholder
  | .staticDh peer reply => .staticDh peer reply

def owner (placeholder : Ed25519Signature) (before : Owner source) : Owner source :=
  {before with edHistory := history placeholder before.edHistory}
def owners (placeholder : Ed25519Signature) (before : State source) : State source := before.map (owner placeholder)

/-- Message freshness and signing order are unchanged; only raw signature slots are replaced. -/
theorem messages (placeholder : Ed25519Signature) (before : History) :
    PqxdhJointIdentity.signedMessages (history placeholder before) = PqxdhJointIdentity.signedMessages before := by
  induction before with
  | nil => rfl
  | cons head rest ih => cases head <;> simp only [history, List.map_cons,
      PqxdhJointIdentity.signedMessages, List.filterMap_cons] at ih ⊢ <;> rw [ih]

def update (index : Nat) (change : Owner source → Owner source) (before : State source) :=
  match before[index]? with
  | none => before
  | some selected => before.set index (change selected)

private theorem update_map (placeholder : Ed25519Signature) (index : Nat)
    (left right : Owner source → Owner source) (law : ∀ before, owner placeholder (left before) = right (owner placeholder before))
    (before : State source) :
    owners placeholder (update index left before) = update index right (owners placeholder before) := by
  unfold update
  cases found : before[index]? with
  | none => simp only [owners, List.getElem?_map, found, Option.map_none]
  | some selected => simp only [owners, List.getElem?_map, found, Option.map_some, List.map_set, law]

/-- The literal lifecycle update commutes with the private history view. -/
theorem phase (placeholder : Ed25519Signature) (index : Nat)
    (phase : RegistrationNativeBeaconFrontend.Phase) (before : State source) :
    owners placeholder (update index (fun selected => {selected with phase}) before) =
      update index (fun selected => {selected with phase}) (owners placeholder before) :=
  update_map placeholder index (fun selected => {selected with phase})
    (fun selected => {selected with phase}) (fun _ => rfl) before

/-- An actual appended signature becomes the same placeholder while its message and position remain literal. -/
theorem append (placeholder signature : Ed25519Signature) (index : Nat) (message : Pqxdh.Bytes) (before : State source) :
    owners placeholder (update index (fun selected => {selected with edHistory := selected.edHistory ++ [.signed message signature]}) before) =
      update index (fun selected => {selected with edHistory := selected.edHistory ++ [.signed message placeholder]}) (owners placeholder before) := by
  apply update_map placeholder index _ _ _ before
  intro selected
  simp only [owner, history, List.map_append, List.map_cons, List.map_nil]

/-- Capturing an owner for the original outgoing source callback does not capture any earlier raw Ed signature. -/
theorem captured (placeholder : Ed25519Signature) (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (before : Owner source) :
    RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index before =
      RegistrationNativeIdentityFrontend.outgoing setup source index (owner placeholder before) := rfl

private theorem history_idempotent (placeholder : Ed25519Signature) (before : History) :
    history placeholder (history placeholder before) = history placeholder before := by
  induction before with
  | nil => rfl
  | cons head rest ih => cases head <;> simp only [history, List.map_cons] at ih ⊢ <;> rw [ih]

private theorem owners_idempotent (placeholder : Ed25519Signature) (before : State source) :
    owners placeholder (owners placeholder before) = owners placeholder before := by
  induction before with
  | nil => rfl
  | cons head rest ih =>
    simp only [owners, List.map_cons] at ih ⊢
    rw [ih]
    exact congrArg (fun selected => selected :: rest.map (owner placeholder)) (show owner placeholder (owner placeholder head) = owner placeholder head by simp only [owner, history_idempotent])

def output (placeholder : Ed25519Signature)
    (result : (Value × State source) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) :=
  ((result.1.1, owners placeholder result.1.2), result.2)

/-- The original source Ed-history append has an exact private-view implementation retaining its actual message and current owner position. -/
theorem log_ed (placeholder signature : Ed25519Signature) (index : Nat) (message : Pqxdh.Bytes)
    (before : State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    output placeholder <$> (((RegistrationNativeIdentityFrontend.logEd (n := n) (KemSK := KemSK) index message signature).run before).run env) =
      (((RegistrationNativeIdentityFrontend.logEd (n := n) (KemSK := KemSK) index message placeholder).run (owners placeholder before)).run env) := by
  simp only [RegistrationNativeIdentityFrontend.logEd, StateT.run_modify, StateT.run_pure, map_pure, output]
  exact congrArg (fun selected => (pure (((), selected), env) : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK)
    ((Unit × State source) × RegistrationWorldAgreementCompiler.EnvState Auxiliary))) (append placeholder signature index message before)

/-- The original lifecycle write commutes literally with the same private Ed-history view. -/
theorem update_phase (placeholder : Ed25519Signature) (index : Nat) (selectedPhase : RegistrationNativeBeaconFrontend.Phase)
    (before : State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    output placeholder <$> (((RegistrationNativeIdentityFrontend.updatePhase (n := n) (KemSK := KemSK) index selectedPhase).run before).run env) =
      (((RegistrationNativeIdentityFrontend.updatePhase (n := n) (KemSK := KemSK) index selectedPhase).run (owners placeholder before)).run env) := by
  simp only [RegistrationNativeIdentityFrontend.updatePhase, StateT.run_modify, StateT.run_pure, map_pure, output]
  exact congrArg (fun selected => (pure (((), selected), env) : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK)
    ((Unit × State source) × RegistrationWorldAgreementCompiler.EnvState Auxiliary))) (phase placeholder index selectedPhase before)

abbrev Packed := State source × RegistrationWorldAgreementCompiler.EnvState Auxiliary
def pack (work : M n KemSK Auxiliary source Value) :
    StateT (Packed (source := source) (Auxiliary := Auxiliary))
      (OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK)) Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> ((work.run before.1).run before.2)
def project (placeholder : Ed25519Signature) (before : Packed (source := source) (Auxiliary := Auxiliary)) :=
  (owners placeholder before.1, before.2)

def Stable (placeholder : Ed25519Signature) (work : M n KemSK Auxiliary source Value) : Prop :=
  ∀ before, Prod.map id (project placeholder) <$> (pack work).run before =
    Prod.map id (project placeholder) <$> (pack work).run (project placeholder before)

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

private theorem pack_bind {Next : Type} (work : M n KemSK Auxiliary source Value)
    (next : Value → M n KemSK Auxiliary source Next) :
    pack (work >>= next) = (pack work >>= fun value => pack (next value)) := by
  funext before
  simp only [pack, StateT.run, bind_apply, map_bind, bind_map_left]

private theorem pure_stable (placeholder : Ed25519Signature) (value : Value) :
    Stable placeholder (pure value : M n KemSK Auxiliary source Value) := by
  intro before
  simp only [pack, StateT.run, pure_apply, map_pure, Prod.map_def, id_eq, project, owners_idempotent]

private theorem lift_stable (placeholder : Ed25519Signature)
    (work : StateT (RegistrationWorldAgreementCompiler.EnvState Auxiliary)
      (OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK)) Value) :
    Stable placeholder (StateT.lift work : M n KemSK Auxiliary source Value) := by
  intro before
  simp only [pack, StateT.run, lift_apply, map_apply, Functor.map_map,
    Prod.map_def, id_eq, project, owners_idempotent]

private theorem bind_stable {Next : Type} (placeholder : Ed25519Signature)
    (work : M n KemSK Auxiliary source Value) (next : Value → M n KemSK Auxiliary source Next)
    (first : Stable placeholder work) (later : ∀ value, Stable placeholder (next value)) :
    Stable placeholder (work >>= next) := by
  intro before
  simp only [pack_bind, StateT.run_bind, map_bind]
  calc
    _ = (do
      let middle ← (pack work).run before
      Prod.map id (project placeholder) <$> (pack (next middle.1)).run (project placeholder middle.2)) :=
      bind_congr (fun (middle : Value × Packed (source := source) (Auxiliary := Auxiliary)) => later middle.1 middle.2)
    _ = (do
      let middle ← Prod.map id (project placeholder) <$> (pack work).run before
      Prod.map id (project placeholder) <$> (pack (next middle.1)).run middle.2) := by rw [bind_map_left]; rfl
    _ = (do
      let middle ← Prod.map id (project placeholder) <$> (pack work).run (project placeholder before)
      Prod.map id (project placeholder) <$> (pack (next middle.1)).run middle.2) := by rw [first before]
    _ = _ := by
      rw [bind_map_left]
      exact bind_congr (fun (middle : Value × Packed (source := source) (Auxiliary := Auxiliary)) => (later middle.1 middle.2).symm)

private theorem simulate_stable {K : Type} {queries : OracleSpec K} (placeholder : Ed25519Signature)
    (handler : QueryImpl queries (M n KemSK Auxiliary source)) (law : ∀ query, Stable placeholder (handler query))
    (work : OracleComp queries Value) : Stable placeholder (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_stable placeholder value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_stable placeholder _ _ (law query) ih

private theorem sample_stable (placeholder : Ed25519Signature) (work : ProbComp Value) :
    Stable placeholder (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) := by
  unfold RegistrationNativeIdentityFrontend.sample
  apply simulate_stable placeholder
  intro query
  exact lift_stable placeholder _

private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (change : S → S) (before : S) :
    (modify change : StateT S m Unit) before = pure ((), change before) := rfl

private theorem log_stable (placeholder signature : Ed25519Signature) (index : Nat) (message : Pqxdh.Bytes) :
    Stable placeholder (RegistrationNativeIdentityFrontend.logEd (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index message signature) := by
  intro before
  simp only [pack, StateT.run, RegistrationNativeIdentityFrontend.logEd, modify_apply, pure_apply,
    map_pure, Prod.map_def, id_eq, project]
  have initial := append placeholder signature index message before.1
  have following := append placeholder signature index message (owners placeholder before.1)
  simp only [update] at initial following
  rw [owners_idempotent] at following
  exact congrArg (fun selected => (pure ((), (selected, before.2)) : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK)
    (Unit × Packed (source := source) (Auxiliary := Auxiliary)))) (initial.trans following.symm)

/-- Every actual outgoing callback ignores earlier signature bytes while keeping the exact current signature reply and actual shared CTX effects. -/
theorem outgoing (placeholder : Ed25519Signature) (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (selected : Owner source) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Stable placeholder (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index selected query) := by
  classical
  cases query with
  | inl query => cases query with
    | hash request => exact lift_stable placeholder _
    | sign request payload digest => exact pure_stable placeholder _
  | inr request =>
    simp only [RegistrationNativeIdentityFrontend.outgoing]
    split
    · apply bind_stable placeholder _ _ (lift_stable placeholder _)
      intro signature
      cases signature with
      | none => exact pure_stable placeholder _
      | some signature =>
        exact bind_stable placeholder _ _ (log_stable placeholder signature index _) fun _ => pure_stable placeholder _
    · exact pure_stable placeholder _

/-- Every adaptive original Init request tree uses the same private history view; current optional replies and all native effects remain unchanged. -/
theorem program (placeholder : Ed25519Signature) (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (selected : Owner source) (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) :
    Stable placeholder (simulateQ (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index selected) work) :=
  simulate_stable placeholder _ (outgoing placeholder setup source index selected) work

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.messages' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.messages
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.phase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.captured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.captured
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.log_ed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.log_ed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.update_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.update_phase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView.program
