-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication

/-! The private Ed-history view commutes with the complete actual effectful Init publication program. Ordinary native callbacks retain their original counted semantics, and source allocators/writers keep their complete mutable P poststate. Only earlier raw signature slots are replaced; signed-message order and all current replies remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView
open RegistrationNativePlatformIdentityProgram (M)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {n : Nat} {I KemSK Auxiliary Platform Value Next : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

abbrev Packed := (RegistrationNativeIdentityFrontend.State source × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × Platform

def pack (work : M n KemSK Auxiliary Platform source Value) :
    StateT (Packed (source := source) (Auxiliary := Auxiliary) (Platform := Platform))
      (OracleComp (RegistrationNativePlatformIdentityProgram.Spec n KemSK)) Value := fun before =>
  (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
    (((work.run before.1.1).run before.1.2).run before.2)

def view (placeholder : Ed25519Signature) (before : Packed (source := source) (Auxiliary := Auxiliary) (Platform := Platform)) :=
  ((RegistrationNativeIdentityHistoryView.owners placeholder before.1.1, before.1.2), before.2)

def Stable (placeholder : Ed25519Signature) (work : M n KemSK Auxiliary Platform source Value) : Prop :=
  ∀ before, Prod.map id (view placeholder) <$> (pack work).run before =
    Prod.map id (view placeholder) <$> (pack work).run (view placeholder before)

private theorem history_idempotent (placeholder : Ed25519Signature) (before : PqxdhJointIdentity.History) :
    RegistrationNativeIdentityHistoryView.history placeholder (RegistrationNativeIdentityHistoryView.history placeholder before) =
      RegistrationNativeIdentityHistoryView.history placeholder before := by
  induction before with
  | nil => rfl
  | cons head rest ih => cases head <;> simp only [RegistrationNativeIdentityHistoryView.history, List.map_cons] at ih ⊢ <;> rw [ih]
private theorem owners_idempotent (placeholder : Ed25519Signature) (before : RegistrationNativeIdentityFrontend.State source) :
    RegistrationNativeIdentityHistoryView.owners placeholder (RegistrationNativeIdentityHistoryView.owners placeholder before) =
      RegistrationNativeIdentityHistoryView.owners placeholder before := by
  induction before with
  | nil => rfl
  | cons head rest ih =>
    simp only [RegistrationNativeIdentityHistoryView.owners, List.map_cons] at ih ⊢
    rw [ih]
    exact congrArg (fun selected => selected :: rest.map (RegistrationNativeIdentityHistoryView.owner placeholder))
      (show RegistrationNativeIdentityHistoryView.owner placeholder (RegistrationNativeIdentityHistoryView.owner placeholder head) =
        RegistrationNativeIdentityHistoryView.owner placeholder head by simp only [RegistrationNativeIdentityHistoryView.owner, history_idempotent])

/-- Adding the actual shared allocator/writer stack preserves an established source native-history view. -/
theorem native (placeholder : Ed25519Signature)
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (law : RegistrationNativeIdentityHistoryView.Stable placeholder work) :
    Stable placeholder (RegistrationNativePlatformIdentityProgram.native work : M n KemSK Auxiliary Platform source Value) := by
  rintro ⟨⟨before, env⟩, platform⟩
  have same := congrArg (fun action => (fun result => (result.1, (result.2, platform))) <$>
    simulateQ (RegistrationNativePlatformIdentityProgram.nativeLift (n := n) (KemSK := KemSK)) action) (law (before, env))
  simpa only [pack, RegistrationNativePlatformIdentityProgram.native, StateT.run, view,
    RegistrationNativeIdentityHistoryView.pack, RegistrationNativeIdentityHistoryView.project,
    simulateQ_map, Functor.map_map, Prod.map_def, id_eq] using same

/-- The actual source writer may fail or mutate P; it never inspects earlier native signature-history bytes. -/
theorem external (placeholder : Ed25519Signature) (work : StateT Platform ProbComp Value) :
    Stable placeholder (RegistrationNativePlatformIdentityProgram.external work : M n KemSK Auxiliary Platform source Value) := by
  rintro ⟨⟨before, env⟩, platform⟩
  simp only [pack, RegistrationNativePlatformIdentityProgram.external, StateT.run, view,
    Functor.map_map, Prod.map_def, id_eq, owners_idempotent]

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem pack_bind (work : M n KemSK Auxiliary Platform source Value)
    (next : Value → M n KemSK Auxiliary Platform source Next) :
    pack (work >>= next) = (pack work >>= fun value => pack (next value)) := by
  funext before
  simp only [pack, StateT.run, bind_apply, map_bind, bind_map_left]
private theorem pure_stable (placeholder : Ed25519Signature) (value : Value) :
    Stable placeholder (pure value : M n KemSK Auxiliary Platform source Value) := by
  rintro ⟨⟨before, env⟩, platform⟩
  simp only [pack, StateT.run, pure_apply, view, map_pure, Prod.map_def, id_eq, owners_idempotent]
private theorem bind_stable (placeholder : Ed25519Signature) (work : M n KemSK Auxiliary Platform source Value)
    (next : Value → M n KemSK Auxiliary Platform source Next) (first : Stable placeholder work)
    (later : ∀ value, Stable placeholder (next value)) : Stable placeholder (work >>= next) := by
  intro before
  simp only [pack_bind, StateT.run_bind, map_bind]
  calc
    _ = (do let middle ← (pack work).run before
            Prod.map id (view placeholder) <$> (pack (next middle.1)).run (view placeholder middle.2)) :=
      bind_congr (fun (middle : Value × Packed (source := source) (Auxiliary := Auxiliary) (Platform := Platform)) => later middle.1 middle.2)
    _ = (do let middle ← Prod.map id (view placeholder) <$> (pack work).run before
            Prod.map id (view placeholder) <$> (pack (next middle.1)).run middle.2) := by rw [bind_map_left]; rfl
    _ = (do let middle ← Prod.map id (view placeholder) <$> (pack work).run (view placeholder before)
            Prod.map id (view placeholder) <$> (pack (next middle.1)).run middle.2) := by rw [first before]
    _ = _ := by rw [bind_map_left]; exact bind_congr (fun (middle : Value × Packed (source := source) (Auxiliary := Auxiliary) (Platform := Platform)) => (later middle.1 middle.2).symm)

private theorem query {E : Type} (placeholder : Ed25519Signature) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : (RegistrationNativePlatformWriter.Spec E).Domain) :
    Stable placeholder (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary) setup index owner writer request) := by
  cases request with
  | inl request => exact native placeholder _ (RegistrationNativeIdentityHistoryView.outgoing placeholder setup source index owner request)
  | inr request => exact external placeholder (writer request)

/-- All actual Init signing/hash/writer branches commute with this private history view, including allocator mutation and every publication failure. -/
theorem program {E : Type} (placeholder : Ed25519Signature) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) Value) :
    Stable placeholder (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary) setup index owner writer) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]; exact pure_stable placeholder value
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_stable placeholder _ _ (query placeholder setup index owner writer request) ih

/-- Capturing the current owner for the effectful source program exposes no earlier raw signature slot. -/
theorem captured {E : Type} (placeholder : Ed25519Signature) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary) setup index owner writer =
      RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary) setup index (RegistrationNativeIdentityHistoryView.owner placeholder owner) writer := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView.external' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView.external

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView.captured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView.captured
