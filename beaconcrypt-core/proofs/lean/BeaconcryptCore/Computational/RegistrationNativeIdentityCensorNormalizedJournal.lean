-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
import BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProgram

/-! The original signed full-state callback journal projects to the same online normalized source journal, with every literal reply and complete live normalized private state retained. Only the stated signature/receipt view and analysis snapshots are projected; normalized and original private states are not identified. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxMain (Full interpret)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "current(" placeholder ")" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder


open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeObservedStageTrace (mapCall)
local notation "plainView" => RegistrationNativeIdentityCensorPrefixOwned.view
local notation "signed" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint actual

def project (placeholder : Ed25519Signature) (before : Whole n KemSK Platform source) : Full n KemSK Platform source :=
  plainView placeholder (drop before)

/-- Closing the genuine free normalization law retains every backend state and does not require generated ownership. -/
theorem normalized_program (placeholder : Ed25519Signature) (work : OracleComp TypedSpec A)
    (before : Full n KemSK Platform source) :
    (interpret setup.joint (simulateQ current(placeholder) work)).run (plainView placeholder before) =
      Prod.map id (plainView placeholder) <$> (interpret setup.joint (simulateQ actual work)).run before := by
  have free := RegistrationNativeIdentityCensorAdaptivePostselection.normalized_program setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve placeholder work before.1
  have closed := congrArg (fun code => (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) code).run before.2) free
  simp only [simulateQ_map,StateT.run_map] at closed
  have observed := congrArg (Functor.map (fun result => (result.1.1,(result.1.2,result.2)))) closed
  simpa only [interpret,StateT.run,RegistrationNativeIdentityCensorPrefixOwned.view,Functor.map_map,Prod.map_def,id_eq] using observed

private theorem normalized_query (placeholder : Ed25519Signature) (query : TypedSpec.Domain)
    (before : Full n KemSK Platform source) :
    Prod.map id (plainView placeholder) <$> (interpret setup.joint (actual query)).run before =
      (interpret setup.joint (current(placeholder) query)).run (plainView placeholder before) := by
  have law := normalized_program setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    placeholder (liftM (TypedSpec.query query) : OracleComp TypedSpec _) before
  simpa only [simulateQ_spec_query] using law.symm

/-- One original signed callback projects to its exact online normalized source callback and original reply. -/
theorem query (placeholder : Ed25519Signature) (request : TypedSpec.Domain) (before : Whole n KemSK Platform source) :
    Prod.map id (project placeholder) <$> (signed request).run before =
      (interpret setup.joint (current(placeholder) request)).run (project placeholder before) := by
  have original := RegistrationNativePlatformIdentityCtxKeyJournal.query_erasure setup.joint actual request before
  have observed := congrArg (Functor.map (Prod.map id (plainView placeholder))) original
  simpa only [Functor.map_map,Prod.map_def,id_eq,project,drop] using
    observed.trans (normalized_query setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      placeholder request (drop before))

/-- Every adaptive original signed callback tree has the same complete normalized source marginal. -/
theorem program (placeholder : Ed25519Signature) (work : OracleComp TypedSpec A) (before : Whole n KemSK Platform source) :
    Prod.map id (project placeholder) <$> (simulateQ signed work).run before =
      (simulateQ (fun query => interpret setup.joint (current(placeholder) query)) work).run (project placeholder before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (project placeholder)
    (query setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve placeholder) work before

omit primitives in
private theorem identity_handler (implementation : QueryImpl TypedSpec (StateT (Full n KemSK Platform source) ProbComp)) :
    RegistrationNativeObservedStageTrace.handler id implementation = RegistrationNativeStageTrace.handler implementation := by
  funext request before
  rfl

/-- Observing normalized snapshots of the original signed execution yields the literal normalized chronological journal with the same leading observations. -/
theorem observed_source (placeholder : Ed25519Signature) (work : OracleComp TypedSpec A)
    (before : Whole n KemSK Platform source) (leading : List (Call TypedSpec (Full n KemSK Platform source))) :
    Prod.map id (Prod.map (project placeholder) id) <$>
      (simulateQ (RegistrationNativeObservedStageTrace.handler (project placeholder) signed) work).run (before,leading) =
    (simulateQ (RegistrationNativeStageTrace.handler (fun query => interpret setup.joint (current(placeholder) query))) work).run
      (project placeholder before,leading) := by
  have law := RegistrationNativeObservedStageTrace.project signed (fun query => interpret setup.joint (current(placeholder) query))
    (project placeholder) (project placeholder) id
    (query setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve placeholder)
    (fun _ => rfl) work (before,leading)
  rw [identity_handler] at law
  exact law

/-- The complete ORIGINAL private stage journal projects only its signed snapshots and current state into that same normalized source journal. -/
theorem full_source (placeholder : Ed25519Signature) (work : OracleComp TypedSpec A)
    (before : Whole n KemSK Platform source) (leading : List (Call TypedSpec (Whole n KemSK Platform source))) :
    Prod.map id (fun current => (project placeholder current.1,current.2.map (mapCall (project placeholder)))) <$>
      (simulateQ (RegistrationNativeStageTrace.handler signed) work).run (before,leading) =
    (simulateQ (RegistrationNativeStageTrace.handler (fun query => interpret setup.joint (current(placeholder) query))) work).run
      (project placeholder before,leading.map (mapCall (project placeholder))) := by
  have full := RegistrationNativeObservedStageTrace.full_project (project placeholder) signed work (before,leading)
  have observed := congrArg (Functor.map (Prod.map id (Prod.map (project placeholder) id))) full
  rw [observed_source setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve] at observed
  simpa only [Functor.map_map,Prod.map_def,id_eq] using observed

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal.normalized_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal.normalized_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal.observed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal.full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal.full_source
