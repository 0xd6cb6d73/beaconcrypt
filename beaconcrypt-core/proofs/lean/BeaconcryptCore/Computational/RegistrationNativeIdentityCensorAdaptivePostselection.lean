-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPacketClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource

/-! The actual typed frontend can normalize only its stored signature/ML-receipt view after every callback. Every query and current reply remains literal. The selected source row/target invariant threads complete private physical state through the actual callback tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (selected position : Nat) (placeholder : Ed25519Signature)
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve)
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "MainState" => RegistrationNativeIdentityMain.State n KemSK mlSource × Platform
local notation "view" => RegistrationNativeIdentityCensorOutgoingView.view placeholder

noncomputable def normalized : QueryImpl TypedSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource) :=
  fun query before => Prod.map id (RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder) <$> (actual query).run before

/-- The complete actual adaptive query tree retains its current replies and every other Main/P field when old log slots are normalized online. -/
theorem normalized_program (work : OracleComp TypedSpec A) (before : MainState) :
    (simulateQ (normalized setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer
      reserveFrame erased helper reserve placeholder) work).run (RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder before) =
      Prod.map id (RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder) <$> (simulateQ actual work).run before := by
  symm
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  exact RegistrationNativePlatformIdentityCtxTypedJointView.handler_stable setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve) placeholder query current

def Selected (selected : Nat) (target : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed) (before : FullState) : Prop :=
  before.1.2.target = some target ∧ before.2.target = some target ∧ before.2.pool.seeds[selected]? = some seed

omit primitive in
/-- Complete continued Main work retains the actual selected target and source row in both private interpretations. -/
theorem source_selected (masked : Bool) (target : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : FullState) (prior : Selected selected target seed before) (result : A × FullState)
    (reached : result ∈ support ((interpret setup.joint selected placeholder masked work).run before)) :
    Selected selected target seed result.2 := by
  simp only [interpret, StateT.run, bind_pure_comp, support_map] at reached
  obtain ⟨inner, actualRun, rfl⟩ := reached
  exact RegistrationNativeIdentityCensorSelectedInvariant.lower_program setup.joint selected placeholder masked target seed
    (work.run before.1.1) before.1.2 before.2 prior.1 prior.2 inner actualRun

/-- The actual marked callback entry clears only public control flags and increments the public bundle counter. -/
def entered (position : Nat) (query : TypedSpec.Domain) (before : FullState) : FullState :=
  ((before.1.1, RegistrationNativeIdentityCensorCompiler.enter position query before.1.2), before.2)

omit primitive in
private theorem entry_selected (query : TypedSpec.Domain) (target : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState) (prior : Selected selected target seed before) :
    Selected selected target seed (entered position query before) := by
  rcases query with query | query
  · exact prior
  · cases query <;> exact prior

local notation "current" => normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before


private theorem normalized_source (masked : Bool) (query : TypedSpec.Domain) (before : FullState) :
    (interpret setup.joint selected placeholder masked (current query)).run before =
      Prod.map id view <$> (interpret setup.joint selected placeholder masked (actual query)).run before := by
  simp only [normalized, interpret, StateT.run, simulateQ_map, map_apply, bind_pure_comp,
    Functor.map_map, RegistrationNativeIdentityCensorOutgoingView.view, Prod.map_def, id_eq]

noncomputable def call (masked : Bool) (query : TypedSpec.Domain) (before : FullState) :
    ProbComp (TypedSpec.Range query × FullState) :=
  (interpret setup.joint selected placeholder masked (current query)).run (entered position query before)
local notation "called(" masked "," query "," before ")" => call setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked query before

/-- The marked actual callback preserves the selected row and public/private target even if it returns a failure or performs later key generation. -/
theorem call_selected (masked : Bool) (query : TypedSpec.Domain) (target : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState) (prior : Selected selected target seed before) (result : TypedSpec.Range query × FullState)
    (reached : result ∈ support (called(masked, query, before))) : Selected selected target seed result.2 := by
  exact source_selected setup selected placeholder masked target seed _ (entered position query before)
    (entry_selected selected position query target seed before prior) result reached

def published : (query : TypedSpec.Domain) → TypedSpec.Range query → FullState → Bool
  | .inr (.bundle _), reply, after => after.1.2.active && (RegistrationNativeRawAdapter.resultOption reply).isSome
  | _, _, _ => false

def cut (query : TypedSpec.Domain) (result : TypedSpec.Range query × FullState) : Option (TypedSpec.Range query × FullState) :=
  if published query result.1 result.2 then none else some result

/-- Every actual selected-source callback has the same publicly surviving reply and normalized complete private state. The proof discharges each literal API branch. -/
theorem call_cut (query : TypedSpec.Domain) (target : Pqxdh.Bytes)
    (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState) (prior : Selected selected target seed before) :
    cut query <$> called(false, query, before) = cut query <$> called(true, query, before) := by
  by_cases bundleQuery : ∃ index, query = .inr (.bundle index)
  · obtain ⟨index, rfl⟩ := bundleQuery
    simp only [call, normalized_source, Functor.map_map]
    change RegistrationNativeIdentityCensorPostselectionBundleCut.replyCut placeholder <$>
        (interpret setup.joint selected placeholder false
          (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created
            (RegistrationNativePlatformConcreteSource.writer reserve) index)).run (entered position (.inr (.bundle index)) before) =
      RegistrationNativeIdentityCensorPostselectionBundleCut.replyCut placeholder <$>
        (interpret setup.joint selected placeholder true
          (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created
            (RegistrationNativePlatformConcreteSource.writer reserve) index)).run (entered position (.inr (.bundle index)) before)
    have held := entry_selected selected position (.inr (.bundle index)) target seed before prior
    exact RegistrationNativeIdentityCensorPostselectionBundleCut.callback setup checks representation created selected index placeholder reserve
      target targetRole (entered position (.inr (.bundle index)) before) seed held.1 held.2.1
      (RegistrationNativeIdentityCensorCompiler.enter_inactive position (.inr (.bundle index)) before.1.2) held.2.2
  · have notBundle : ∀ index, query ≠ .inr (.bundle index) := fun index same => bundleQuery ⟨index, same⟩
    simp only [call, normalized_source]
    rw [RegistrationNativeIdentityCensorQuietSource.callback setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve)
      selected placeholder query notBundle (entered position query before)]

def attempt (accept : Nat) : TypedSpec.Domain → Nat → Option registration.InitPacket
  | .inr (.accept packet), counter => if counter = accept then some packet else none
  | _, _ => none

/-- The private same-run value interpretation stops before the public accept and absorbs only actual selected successful publications. -/
noncomputable def visit (masked : Bool) (accept : Nat) (work : OracleComp TypedSpec A) :
    FullState × Nat → ProbComp (Option RegistrationNativeIdentityCensorPacketClient.Found) :=
  work.recOn (fun _ _before => pure none)
    (fun query _next continued before =>
      match attempt accept query before.2 with
      | some packet => pure (before.1.1.2.target.map fun message => (message, packet))
      | none => do
          let selectedCut ← cut query <$> called(masked, query, before.1)
          match selectedCut with
          | none => pure none
          | some kept => continued kept.1 (kept.2, before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0))
local notation "run(" masked "," accept "," work "," before ")" => visit setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked accept work before

private theorem visit_pure (masked : Bool) (accept : Nat) (value : A) (before : FullState × Nat) :
    run(masked, accept, (pure value), before) = pure none := rfl
private theorem visit_query (masked : Bool) (accept : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : FullState × Nat) :
    run(masked, accept, (TypedSpec.query query >>= next), before) =
      (match attempt accept query before.2 with
      | some packet => pure (before.1.1.2.target.map fun message => (message, packet))
      | none => do
          let selectedCut ← cut query <$> called(masked, query, before.1)
          match selectedCut with
          | none => pure none
          | some kept => visit setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked accept (next kept.1) (kept.2, before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)) := by rfl

private theorem cut_selected (masked : Bool) (query : TypedSpec.Domain) (target : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState) (prior : Selected selected target seed before) (kept : TypedSpec.Range query × FullState)
    (reached : some kept ∈ support (cut query <$> called(masked, query, before))) :
    Selected selected target seed kept.2 := by
  rw [support_map] at reached
  obtain ⟨result, actualRun, same⟩ := reached
  unfold cut at same
  split at same
  · cases same
  · have literal : result = kept := Option.some.inj same
    simpa only [literal] using call_selected setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked query target seed before prior result actualRun

/-- Every adaptive continuation after a genuine selected source call has identical canonical/placeholder public packet observations. Failed callbacks, failed writers, all stateful P and same physical cache/journal remain coupled until the public stop. -/
theorem paired (accept : Nat) (work : OracleComp TypedSpec A) (target : Pqxdh.Bytes)
    (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState × Nat) (prior : Selected selected target seed before.1) :
    run(false, accept, work, before) = run(true, accept, work, before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    rw [visit_query, visit_query]
    cases guessed : attempt accept query before.2 with
    | some packet => rfl
    | none =>
      dsimp only
      rw [call_cut setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer
        reserveFrame erased helper reserve selected position placeholder query target targetRole seed before.1 prior]
      apply bind_congr_of_forall_mem_support
      intro selectedCut reached
      cases selectedCut with
      | none => rfl
      | some kept =>
        exact ih kept.1 (kept.2, before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)
          (cut_selected setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer
            reserveFrame erased helper reserve selected position placeholder true query target seed before.1 prior kept reached)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection.normalized_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection.normalized_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection.source_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection.source_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection.call_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection.call_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection.call_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection.call_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection.paired
