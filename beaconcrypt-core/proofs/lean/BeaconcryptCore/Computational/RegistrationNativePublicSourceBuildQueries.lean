-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo

/-! A moved Server capability can demand only its own already prepared root. This derived query property connects the optional actual memo lookup to the total private source-root interpretation without adding a live-token restriction to the public security event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildQueries
open RegistrationServerMaterialFrontend (State Spec)
open RegistrationServerReferenceRoot (Ready)
open RegistrationNativeRetainedRoots (Memo)
open RegistrationServerReferenceRestore (Roots)
open RegistrationNativeRelatedFamily (Message)
variable {n : Nat} {Value : Type}

def Prepared (memo : Memo) (roots : Roots) : (Spec n).Domain → Prop
  | .inl message => memo message = some (roots message)
  | .inr _ => True

private theorem common_free (memo : Memo) (roots : Roots)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) :
    (simulateQ RegistrationNativePairedServerService.publicCommon work).AllQueriesSatisfy (Prepared memo roots) := by
  induction work using OracleComp.inductionOn with
  | pure output => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query,
        RegistrationNativePairedServerService.publicCommon, allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial, ih⟩

private theorem admitted_prepared (memo : Memo) (roots : Roots)
    (wire : RegistrationNativeWire.Wire) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (message : Message)
    (stored : memo message = some (roots message)) :
    (RegistrationNativePairedServerService.publicAdmitted (n := n) wire.encodeResponse control initial message).AllQueriesSatisfy
      (Prepared memo roots) := by
  rw [RegistrationNativePairedServerService.publicAdmitted, allQueriesSatisfy_query_bind_iff]
  refine ⟨stored, ?_⟩
  intro selected
  cases selected with
  | none => trivial
  | some choice => exact common_free memo roots _

private theorem finish_free (memo : Memo) (roots : Roots)
    (published : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes)) (before : State) :
    ((RegistrationServerMaterialFrontend.finish (n := n) published).run before).AllQueriesSatisfy (Prepared memo roots) := by
  cases published with
  | fail error => trivial
  | div => trivial
  | ok published => cases published <;> trivial

/-- An admitted completion asks only for the descriptor whose actual private root was prepared. -/
theorem complete_prepared (memo : Memo) (roots : Roots)
    (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (ready : Ready)
    (application : Slice U8) (before : State) (stored : memo ready.reference = some (roots ready.reference)) :
    ((RegistrationServerMaterialFrontend.complete (n := n) wire reservePeer ready application).run before).AllQueriesSatisfy
      (Prepared memo roots) := by
  unfold RegistrationServerMaterialFrontend.complete
  simp only [StateT.run]
  cases beginEq : peer.begin_completion_lookup before.control before.pin (RegistrationServerMaterialFrontend.token ready) application with
  | fail error => trivial
  | div => trivial
  | ok lookupResult => cases lookupResult with
    | Err previous => trivial
    | Ok lookup => cases requested : lookup.request with
      | fail error => trivial
      | div => trivial
      | ok keyId =>
          simp only [requested]
          split
          · simp only [RegistrationServerMaterialFrontend.effect, allQueriesSatisfy_query_bind_iff]
            refine ⟨trivial, ?_⟩
            intro occupied
            cases resumedEq : lookup.resume occupied with
            | fail error => trivial
            | div => trivial
            | ok completionResult => cases completionResult with
              | Err previous => trivial
              | Ok initial =>
                  simp only []
                  split
                  · exact allQueriesSatisfy_bind (admitted_prepared memo roots wire before.control
                      (RegistrationBoundKeySchedule.publicInitial initial) ready.reference stored)
                      (fun published => finish_free memo roots published before)
                  · trivial
          · trivial

/-- Every actual build demand is backed by the internal live-session and functional memo receipts, including moved-handle and cancellation branches. -/
theorem build_prepared (memo : Memo) (roots : Roots)
    (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (handle : Nat)
    (application : Option (Slice U8)) (before : State)
    (live : RegistrationServerMaterialRoots.Live before memo)
    (consistent : ∀ message root, memo message = some root → roots message = root) :
    ((RegistrationServerMaterialFrontend.build (n := n) wire reservePeer handle application).run before).AllQueriesSatisfy
      (Prepared memo roots) := by
  have taken := RegistrationServerMaterialRoots.take_live handle before memo live
  unfold RegistrationServerMaterialFrontend.build
  simp only [StateT.run]
  cases chosen : RegistrationServerMaterialFrontend.take handle before with
  | mk ready current => cases ready with
    | none => trivial
    | some ready =>
        obtain ⟨root, stored⟩ := taken.2 ready (by rw [chosen])
        have literal := consistent ready.reference root stored
        cases application with
        | none => trivial
        | some application => exact complete_prepared memo roots wire reservePeer ready application current (by simpa only [literal] using stored)

end BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildQueries
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildQueries.complete_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildQueries.complete_prepared
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildQueries.build_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildQueries.build_prepared
