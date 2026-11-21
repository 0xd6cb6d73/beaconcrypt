-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProgram

/-! The same original source prefix supplies actual generated-row ownership to the normalized public bundle cutoff. Normalization erases only prior signature slots and raw ML receipts; private source rows, full hash state and signing history remain in the interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned
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

omit primitives in
def view (placeholder : Ed25519Signature) (before : Full n KemSK Platform source) : Full n KemSK Platform source :=
  (RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder before.1, before.2)

omit primitives in
private theorem view_owned (joint : PqxdhJointIdentity.Primitives) (placeholder : Ed25519Signature)
    (before : Full n KemSK Platform source) (prior : Owned joint before) : Owned joint (view placeholder before) := by
  change RegistrationNativeIdentityRealization.Owned joint before.2.1 before.1.1.beacons at prior
  change RegistrationNativeIdentityRealization.Owned joint before.2.1 (RegistrationNativeIdentityHistoryView.owners placeholder before.1.1.beacons)
  intro owner member
  obtain ⟨original, earlier, rfl⟩ := List.mem_map.mp member
  exact prior original earlier

private theorem normalized_program (placeholder : Ed25519Signature) (work : OracleComp TypedSpec A)
    (before : Full n KemSK Platform source) :
    (interpret setup.joint (simulateQ current(placeholder) work)).run (view placeholder before) =
      Prod.map id (view placeholder) <$> (interpret setup.joint (simulateQ actual work)).run before := by
  have free := RegistrationNativeIdentityCensorAdaptivePostselection.normalized_program setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve placeholder work before.1
  have closed := congrArg (fun code => (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) code).run before.2) free
  simp only [simulateQ_map, StateT.run_map] at closed
  have observed := congrArg (Functor.map (fun result => (result.1.1, (result.1.2, result.2)))) closed
  simpa only [interpret, StateT.run, view, Functor.map_map, Prod.map_def, id_eq] using observed


omit primitives in
def lift (placeholder : Ed25519Signature) (mode : RegistrationNativeIdentityCensorCompiler.Mode)
    (before : Full n KemSK Platform source) :
    RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source) :=
  ((RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder before.1, mode),
    ⟨before.2.1, before.2.2, none, none, none⟩)

/-- Every supported normalized public bundle cutoff has the actual original source-prefix witness, with the same pool/hash state and derived generated-row ownership. -/
theorem witness (selected position : Nat) (placeholder : Ed25519Signature) (masked : Bool)
    (work : OracleComp TypedSpec A) (cursor : Nat) (mode : RegistrationNativeIdentityCensorCompiler.Mode)
    (before : Full n KemSK Platform source) (owned : Owned setup.joint before)
    (room : cursor ≤ position) (count : mode.bundles = cursor) (missing : mode.target = none)
    (result : RegistrationNativeIdentityCensorBundlePrefix.Cut A ×
      RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source))
    (reached : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint selected position placeholder masked current(placeholder))
      (RegistrationNativeIdentityCensorBundlePrefix.stop position work cursor)).run (lift placeholder mode before))) :
    ∃ original : RegistrationNativeIdentityCensorBundlePrefix.Cut A × Full n KemSK Platform source,
      original ∈ support ((interpret setup.joint (simulateQ actual (RegistrationNativeIdentityCensorBundlePrefix.stop position work cursor))).run before) ∧
      original.1 = result.1 ∧ view placeholder original.2 = RegistrationNativeIdentityCensorActualHashSource.project result.2 ∧
      Owned setup.joint original.2 := by
  have projected := Set.mem_image_of_mem (Prod.map id RegistrationNativeIdentityCensorActualHashSource.project) reached
  rw [← support_map, RegistrationNativeIdentityCensorBundlePrefix.source setup.joint selected position placeholder masked current(placeholder)
    work cursor (lift placeholder mode before) room count missing] at projected
  change (result.1, RegistrationNativeIdentityCensorActualHashSource.project result.2) ∈ support
    ((simulateQ (fun query => interpret setup.joint (current(placeholder) query)) (RegistrationNativeIdentityCensorBundlePrefix.stop position work cursor)).run
      (view placeholder before)) at projected
  rw [← RegistrationNativePlatformIdentityCtxProgram.interpret_program setup.joint current(placeholder),
    normalized_program setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      placeholder (RegistrationNativeIdentityCensorBundlePrefix.stop position work cursor) before, support_map] at projected
  obtain ⟨original, called, same⟩ := projected
  refine ⟨original, called, congrArg Prod.fst same, congrArg Prod.snd same, ?_⟩
  exact RegistrationNativePlatformIdentityCtxProgram.program_owned setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer (RegistrationNativeIdentityCensorBundlePrefix.stop position work cursor) before original owned called


/-- Conversely, an original supported cutoff lifts to the actual public marked cutoff with the same query continuation, pool and physical hash state. The prior signature-slot view is applied only to frontend metadata. -/
theorem from_original (selected position : Nat) (placeholder : Ed25519Signature) (masked : Bool)
    (work : OracleComp TypedSpec A) (cursor : Nat) (mode : RegistrationNativeIdentityCensorCompiler.Mode)
    (before : Full n KemSK Platform source)
    (room : cursor ≤ position) (count : mode.bundles = cursor) (missing : mode.target = none)
    (result : RegistrationNativeIdentityCensorBundlePrefix.Cut A × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret setup.joint (simulateQ actual
      (RegistrationNativeIdentityCensorBundlePrefix.stop position work cursor))).run before)) :
    ∃ markedResult,
      markedResult ∈ support ((simulateQ (RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint selected position placeholder masked current(placeholder))
        (RegistrationNativeIdentityCensorBundlePrefix.stop position work cursor)).run (lift placeholder mode before)) ∧
      markedResult.1 = result.1 ∧ RegistrationNativeIdentityCensorActualHashSource.project markedResult.2 = view placeholder result.2 := by
  have image := Set.mem_image_of_mem (Prod.map id (view placeholder)) reached
  rw [←support_map,←normalized_program setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer
    reserveFrame erased helper reserve placeholder (RegistrationNativeIdentityCensorBundlePrefix.stop position work cursor) before] at image
  rw [RegistrationNativePlatformIdentityCtxProgram.interpret_program] at image
  change (result.1,view placeholder result.2) ∈ support ((simulateQ
    (RegistrationNativeIdentityCensorBundlePrefix.original setup.joint current(placeholder))
    (RegistrationNativeIdentityCensorBundlePrefix.stop position work cursor)).run
      (RegistrationNativeIdentityCensorActualHashSource.project (lift placeholder mode before))) at image
  rw [←RegistrationNativeIdentityCensorBundlePrefix.source setup.joint selected position placeholder masked current(placeholder)
    work cursor (lift placeholder mode before) room count missing,support_map] at image
  obtain ⟨markedResult,called,same⟩ := image
  exact ⟨markedResult,called,congrArg Prod.fst same,congrArg Prod.snd same⟩

/-- In particular, each actual owner at that cutoff has its original private generated row. This is derived from the same initialized source path, rather than supplied as a controller condition. -/
theorem row (selected position : Nat) (placeholder : Ed25519Signature) (masked : Bool)
    (work : OracleComp TypedSpec A) (cursor : Nat) (mode : RegistrationNativeIdentityCensorCompiler.Mode)
    (before : Full n KemSK Platform source) (owned : Owned setup.joint before)
    (room : cursor ≤ position) (count : mode.bundles = cursor) (missing : mode.target = none)
    (result : RegistrationNativeIdentityCensorBundlePrefix.Cut A ×
      RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source))
    (reached : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint selected position placeholder masked current(placeholder))
      (RegistrationNativeIdentityCensorBundlePrefix.stop position work cursor)).run (lift placeholder mode before)))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (found : result.2.1.1.1.beacons[index]? = some owner) :
    ∃ seed, result.2.2.pool.seeds[owner.identity.handle]? = some seed ∧ owner.identity.publicIdentity = setup.joint.publicKeys seed := by
  obtain ⟨original, _called, _sameCut, sameState, originalOwned⟩ := witness setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked work cursor mode before owned room count missing result reached
  have normalizedOwned := view_owned setup.joint placeholder original.2 originalOwned
  have currentOwned : Owned setup.joint (RegistrationNativeIdentityCensorActualHashSource.project result.2) := sameState ▸ normalizedOwned
  change RegistrationNativeIdentityRealization.Owned setup.joint result.2.2.pool result.2.1.1.1.beacons at currentOwned
  exact currentOwned owner (List.mem_of_getElem? found)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned.witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned.witness

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned.row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned.row

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned.from_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixOwned.from_original
