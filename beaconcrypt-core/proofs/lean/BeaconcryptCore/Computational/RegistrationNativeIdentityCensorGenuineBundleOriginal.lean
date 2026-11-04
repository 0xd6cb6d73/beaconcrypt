-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineOriginal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOtherMessageSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary

/-! Actual captured bundle bodies for another handle or another one-time message keep their complete original source marginal. Their request scopes follow literal captured operands and every terminal/failed writer state is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineBundleOriginal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOtherOwnerSource (Genuine Holds)
variable {n : Nat} {I KemSK Platform E A Q : Type} {base : OracleSpec I} {queries : OracleSpec Q} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "original(" work ")" => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint work
local notation "tree(" scalar ")" => RegistrationNativePlatformWriter.begin E (pqxdh.BeaconFresh.mk owner.pin.binding)
  (RegistrationNativeIdentityFrontend.inputs owner) (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) owner.pin owner.mldsa.publicKey
local notation "publication(" scalar ")" => Main (simulateQ
  (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
    setup index owner (RegistrationNativePlatformConcreteSource.writer reserve)) (tree(scalar)))
local notation "body(" scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar (RegistrationNativePlatformConcreteSource.writer reserve))

private theorem original_program
    (impl : QueryImpl queries (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource)) (work : OracleComp queries A) :
    original(simulateQ impl work) = simulateQ (fun query => original(impl query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure setup.joint value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, ih]

private theorem terminal (censored : Bool) (scalar : PqxdhJointGapDh.ScalarBytes) (reply : RegistrationNativePlatformIdentityBundle.Reply)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    let action := Main (RegistrationNativePlatformIdentityBundle.next index owner scalar reply)
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(censored, action)).run before =
      (original(action)).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  dsimp only
  have real := RegistrationNativeIdentityCensorRealSigning.main setup.joint selected placeholder
    (Main (RegistrationNativePlatformIdentityBundle.next index owner scalar reply)) before (by
      rw [RegistrationNativeIdentityCensorBundleTerminal.next_run]
      trivial)
  cases censored with
  | false => exact real
  | true =>
    rw [RegistrationNativeIdentityCensorBundleTerminal.source] at real ⊢
    exact real

private theorem genuine (censored : Bool) (target : Pqxdh.Bytes) (scalar : PqxdhJointGapDh.ScalarBytes)
    (allowed : (tree(scalar)).AllQueriesSatisfy (Genuine (E := E) selected owner target))
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (held : Holds target before) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(censored, body(scalar))).run before =
      (original(body(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  have initial : Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(censored, publication(scalar))).run before =
      (original(publication(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
    rw [RegistrationNativeIdentityCensorSourceFold.publication]
    conv_rhs => rw [RegistrationNativePlatformIdentityCtxOutgoingFold.publication, original_program]
    exact RegistrationNativeIdentityCensorGenuineOriginal.program setup checks representation created selected index owner placeholder
      (RegistrationNativePlatformConcreteSource.writer reserve) censored target (tree(scalar)) allowed before held
  simp only [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold, RegistrationNativeIdentityCensorSourceFold.bind_source,
    RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind, map_bind]
  rw [← initial, bind_map_left]
  apply bind_congr
  intro result
  simpa only [Prod.map, id_eq] using terminal setup checks representation created selected index owner placeholder censored scalar result.1 result.2

/-- Another captured handle cannot select the target and retains exact current source replies and full native/private/P state, even on failed or successful publication. -/
theorem other (censored : Bool) (target : Pqxdh.Bytes) (different : owner.identity.handle ≠ selected)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (held : Holds target before) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(censored, body(scalar))).run before =
      (original(body(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  apply genuine setup checks representation created selected index owner placeholder reserve censored target scalar _ before held
  have scope : ∀ query : (RegistrationNativePlatformWriter.Spec E).Domain, Genuine (E := E) selected owner target query := by
    intro query
    rcases query with (_query | request) | query
    · trivial
    · exact Or.inl different
    · trivial
  induction (tree(scalar)) using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨scope query, ih⟩

/-- Literal one-time operand lineage makes every current source Ed call genuine for a different one-time target message. -/
theorem message (censored : Bool) (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (scalar : PqxdhJointGapDh.ScalarBytes) (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged started)
    (different : target ≠ absBytes started.message.one_time_key)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (held : Holds target before) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(censored, body(scalar))).run before =
      (original(body(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  apply genuine setup checks representation created selected index owner placeholder reserve censored target scalar _ before held
  apply (RegistrationNativePlatformOneTimeOperandLineage.begin_allowed (E := E) _ _ _ _ _ started built tagged).mono
  intro query allowed
  rcases query with (_query | request) | query
  · trivial
  · apply Or.inr
    intro same
    have currentRole : RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true := by
      rw [← same]
      exact targetRole
    exact different (same.trans (allowed currentRole))
  · trivial

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineBundleOriginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineBundleOriginal.other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineBundleOriginal.other

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineBundleOriginal.message' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorGenuineBundleOriginal.message
