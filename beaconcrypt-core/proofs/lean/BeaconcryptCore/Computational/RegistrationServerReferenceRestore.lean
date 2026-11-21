-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialFrontend
import BeaconcryptCore.Computational.RegistrationServerSdkSource

/-! Private reconstruction of native Server one-use tokens from public root references. Only this proof map receives root values; executable frontend state contains no root. Actual replay insertion and moved-handle consumption commute with reconstruction for every replay outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceRestore
open RegistrationServerReferenceRoot (Ready atRoot)
open RegistrationServerMaterialFrontend (State)
open PqxdhSecretInputKdf (RootOutput)
variable {n : Nat}

abbrev Roots := RegistrationNativeRelatedFamily.Message → RootOutput

def token (roots : Roots) (ready : Ready) : peer.ConsumedRegistration := ⟨atRoot ready (roots ready.reference)⟩

def sessions (roots : Roots) (before : State) : List (Option peer.ConsumedRegistration) :=
  before.sessions.map (Option.map (token roots))

def restore (roots : Roots) (before : State) (nativeLocal : RegistrationServerRootCompiler.Local n) :
    RegistrationServerFrontendCompiler.State n :=
  ⟨before.control, before.pin, before.consumed, sessions roots before, nativeLocal⟩

/-- Token reconstruction retains the literal populated registration binding and replay identifier. -/
theorem token_fields (roots : Roots) (ready : Ready) :
    (token roots ready).agreement.binding = ready.agreement.binding ∧
      (token roots ready).agreement.pending.registration_id = ready.agreement.pending.registration_id := ⟨rfl, rfl⟩

/-- Actual replay insertion depends on the public cleared registration identifier, while the consumed token retains its private source root. -/
theorem consume (ready : Ready) (first second : RootOutput) (history : RegistrationReplaySchedule.State) :
    RegistrationReplaySchedule.consume (atRoot ready second) history =
      (fun result => ((match result.1 with | .None => .None | .Some _ => .Some ⟨atRoot ready second⟩), result.2)) <$>
        RegistrationReplaySchedule.consume (atRoot ready first) history := by
  by_cases present : history.contains (absBytes ready.agreement.pending.registration_id.bytes) = true
  · rw [RegistrationReplaySchedule.consume_replayed _ _ present,
      RegistrationReplaySchedule.consume_replayed _ _ present]
    rfl
  · have absent : history.contains (absBytes ready.agreement.pending.registration_id.bytes) = false :=
      Bool.eq_false_iff.mpr present
    rw [RegistrationReplaySchedule.consume_fresh _ _ absent,
      RegistrationReplaySchedule.consume_fresh _ _ absent]
    rfl

/-- Native token reconstruction preserves complete private SDK state and the exact public session handle on either replay branch. -/
theorem retain (roots : Roots) (ready : Ready) (before : State) (nativeLocal : RegistrationServerRootCompiler.Local n) :
    (fun result => (result.1, restore roots result.2 nativeLocal)) <$>
        RegistrationServerMaterialFrontend.retain ready before =
      (match RegistrationReplaySchedule.consume (atRoot ready (roots ready.reference)) before.consumed with
      | .fail error => .fail error
      | .div => .div
      | .ok (.None, history) => .ok (none, { restore roots before nativeLocal with consumed := history })
      | .ok (.Some consumed, history) => .ok (some (restore roots before nativeLocal).sessions.length,
          { restore roots before nativeLocal with
            consumed := history
            sessions := (restore roots before nativeLocal).sessions ++ [some consumed] })) := by
  simp only [RegistrationServerMaterialFrontend.retain]
  by_cases present : before.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) = true
  · rw [RegistrationReplaySchedule.consume_replayed (atRoot ready RegistrationBoundKeySchedule.zero) before.consumed present,
      RegistrationReplaySchedule.consume_replayed (atRoot ready (roots ready.reference)) before.consumed present]
    rfl
  · have absent : before.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) = false :=
      Bool.eq_false_iff.mpr present
    rw [RegistrationReplaySchedule.consume_fresh (atRoot ready RegistrationBoundKeySchedule.zero) before.consumed absent,
      RegistrationReplaySchedule.consume_fresh (atRoot ready (roots ready.reference)) before.consumed absent]
    change RustM.ok (some before.sessions.length, restore roots
      { before with
        consumed := before.consumed ++ [absBytes ready.agreement.pending.registration_id.bytes]
        sessions := before.sessions ++ [some ready] } nativeLocal) = _
    simp only [restore, sessions, List.map_append, List.map_cons, List.map_nil, Option.map_some, List.length_map, token]
    rfl

/-- Moving a public one-use handle before every later failure moves exactly the corresponding private source token. -/
theorem take (roots : Roots) (handle : Nat) (before : State) (nativeLocal : RegistrationServerRootCompiler.Local n) :
    let selected := RegistrationServerMaterialFrontend.take handle before
    RegistrationServerSdkSource.take handle (restore roots before nativeLocal) =
      (selected.1.map (token roots), restore roots selected.2 nativeLocal) := by
  unfold RegistrationServerMaterialFrontend.take RegistrationServerSdkSource.take
  simp only [restore, sessions, List.getElem?_map]
  cases found : before.sessions[handle]? with
  | none => rfl
  | some entry =>
      cases entry with
      | none => rfl
      | some ready =>
          simp only [Option.map_some]
          rw [List.map_set]
          rfl

end BeaconcryptCore.Computational.RegistrationServerReferenceRestore

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRestore.token_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRestore.token_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRestore.consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRestore.consume
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRestore.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRestore.retain
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRestore.take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRestore.take
