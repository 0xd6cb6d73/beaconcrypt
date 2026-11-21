-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplatePair
import BeaconcryptCore.Computational.RegistrationNativeIdentityReadyFailure

/-! The literal native request-hash-to-Ready suffix closes on the actual private real/censored source and concrete Init writer. Only the failed-publication observation and stored-log projection are compared; successful encoded payloads remain distinct. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaSuffix
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOutgoingView (view)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

private theorem observed_stable {S A B : Type} (project : S → S) (observe : A → B)
    (work : StateT S ProbComp A) (stable : RegistrationNativePlatformViewStable.Stable project work) (before : S) :
    Prod.map observe project <$> work.run before = Prod.map observe project <$> work.run (project before) := by
  have same := congrArg (fun distribution => Prod.map observe id <$> distribution) (stable before)
  simpa only [Functor.map_map, Prod.map_def, id_eq] using same

private theorem bind_pair {S A B C : Type} (project : S → S) (observe : B → C)
    (left right : StateT S ProbComp A) (tailLeft tailRight : A → StateT S ProbComp B)
    (first : ∀ before, Prod.map id project <$> left.run before = Prod.map id project <$> right.run before)
    (stableLeft : ∀ value, RegistrationNativePlatformViewStable.Stable project (tailLeft value))
    (stableRight : ∀ value, RegistrationNativePlatformViewStable.Stable project (tailRight value))
    (paired : ∀ value before, Prod.map observe project <$> (tailLeft value).run before =
      Prod.map observe project <$> (tailRight value).run before) (before : S) :
    Prod.map observe project <$> (left >>= tailLeft).run before =
      Prod.map observe project <$> (right >>= tailRight).run before := by
  simp only [StateT.run_bind, map_bind]
  calc
    _ = left.run before >>= fun result => Prod.map observe project <$> (tailLeft result.1).run (project result.2) :=
      bind_congr (fun result => observed_stable project observe _ (stableLeft result.1) result.2)
    _ = (Prod.map id project <$> left.run before) >>= fun result => Prod.map observe project <$> (tailLeft result.1).run result.2 := by rw [bind_map_left]; rfl
    _ = (Prod.map id project <$> right.run before) >>= fun result => Prod.map observe project <$> (tailLeft result.1).run result.2 := by rw [first before]
    _ = (Prod.map id project <$> right.run before) >>= fun result => Prod.map observe project <$> (tailRight result.1).run result.2 :=
      bind_congr (fun result => paired result.1 result.2)
    _ = right.run before >>= fun result => Prod.map observe project <$> (tailRight result.1).run (project result.2) := by rw [bind_map_left]; rfl
    _ = _ := bind_congr (fun result => (observed_stable project observe _ (stableRight result.1) result.2).symm)

section Actual
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "external" work => Main (RegistrationNativePlatformIdentityProgram.external work)
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "fullReserve" => (fun size => source(false, external (reserve size)))
local notation "fullWriter" => RegistrationNativeSourceWriterFailureView.writer fullReserve RegistrationNativeConcreteCodec.serializerBranches
local notation "action(" query ")" => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))
local notation "callback(" censored ")" => (fun query => source(censored, action(query)))
local notation "encoder(" censored ")" => (fun fields => source(censored, external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields)))

private theorem encode_left (fields : registration.InitView) : encoder(false) fields = fullWriter fields :=
  RegistrationNativeIdentityCensorExternalSource.writer setup.joint selected placeholder false setup checks representation created reserve fields

private theorem encode_right (fields : registration.InitView) : encoder(true) fields = fullWriter fields := by
  change source(true, external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields)) = fullWriter fields
  rw [RegistrationNativeIdentityCensorExternalSource.writer]
  have same : (fun size => source(true, external (reserve size))) = fullReserve := by
    funext size
    exact (RegistrationNativeIdentityCensorExternalSource.source_equal setup.joint selected placeholder setup checks representation created (reserve size)).symm
  rw [same]

private theorem writer_stable (fields : registration.InitView) :
    RegistrationNativePlatformViewStable.Stable (view placeholder) (fullWriter fields) := by
  rw [← encode_left setup checks representation created selected placeholder reserve fields]
  exact RegistrationNativeIdentityCensorExternalSource.stable setup.joint selected placeholder false setup checks representation created _

private abbrev TailSpec := RegistrationBeaconInitExecutor.Spec +
  (registration.InitView →ₒ RustM (core.option.Option (alloc.vec.Vec U8)))
private noncomputable def dictionary (censored : Bool) : QueryImpl TailSpec
    (StateT (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) ProbComp)
  | .inl query => callback(censored) query
  | .inr fields => encoder(censored) fields

private theorem dictionary_stable (censored : Bool) (query : TailSpec.Domain) :
    RegistrationNativePlatformViewStable.Stable (view placeholder)
      (dictionary (n := n) setup checks representation created selected index owner placeholder reserve censored query) := by
  cases query with
  | inl query => exact RegistrationNativeIdentityCensorOutgoingView.query setup.joint selected placeholder censored setup checks representation created index owner query
  | inr fields => exact RegistrationNativeIdentityCensorExternalSource.stable setup.joint selected placeholder censored setup checks representation created _

/-- The complete actual source Ed/controller suffix ignores only previous stored raw logs, while retaining every current byte reply and the complete private/P state. -/
theorem ed_stable (censored : Bool) (pending : registration.BeaconEd25519Signing) :
    RegistrationNativePlatformViewStable.Stable (view placeholder)
      (RegistrationNativePlatformBeaconPublication.fromEd (callback(censored)) (encoder(censored)) pending) := by
  have same := RegistrationNativePlatformViewStable.program_stable (view placeholder)
    (RegistrationNativeIdentityCensorOutgoingView.view_idempotent placeholder)
    (dictionary (n := n) setup checks representation created selected index owner placeholder reserve censored)
    (dictionary_stable setup checks representation created selected index owner placeholder reserve censored)
    (RegistrationNativePlatformBeaconPublication.fromEd
      (fun query => TailSpec.query (.inl query)) (fun fields => TailSpec.query (.inr fields)) pending)
  rw [RegistrationNativePlatformBeaconPublication.ed_interpret] at same
  simpa only [simulateQ_spec_query, dictionary] using same

/-- The two actual internal attached-signature Init requests use the same private template and current reply before entering the current Ready/writer suffix. -/
theorem hash (left right : registration.BeaconInitHash) (paired : RegistrationNativeIdentityHashPair.Same left right)
    (requestLeft requestRight : registration.HashRequest)
    (requestedLeft : left.request = .ok requestLeft) (requestedRight : right.request = .ok requestRight)
    (framing : RegistrationNativeIdentityCensorOperational.parts (RegistrationInputs.hashBytes requestLeft) =
      RegistrationNativeIdentityCensorOperational.parts (RegistrationInputs.hashBytes requestRight))
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (active : before.1.2.active = true) :
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromHash (callback(false)) (encoder(false)) left).run before =
    Prod.map RegistrationNativeIdentityReadyFailure.observe (view placeholder) <$>
      (RegistrationNativePlatformBeaconPublication.fromHash (callback(true)) (encoder(true)) right).run before := by
  obtain ⟨actualLeft, sourceLeft, _, routeLeft⟩ := RegistrationNativeIdentityHashRoute.transcript left
  obtain ⟨actualRight, sourceRight, _, routeRight⟩ := RegistrationNativeIdentityHashRoute.transcript right
  cases RustM.ok.inj (sourceLeft.symm.trans requestedLeft)
  cases RustM.ok.inj (sourceRight.symm.trans requestedRight)
  have currentHash : (callback(false) (.inl (.hash requestLeft))).run before =
      (callback(true) (.inl (.hash requestRight))).run before :=
    RegistrationNativeIdentityCensorHashOutgoingSource.hidden setup checks representation created selected placeholder
      requestLeft requestRight before active routeLeft routeRight framing
  simp only [RegistrationNativePlatformBeaconPublication.fromHash, requestedLeft, requestedRight,
    RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, map_bind]
  rw [currentHash]
  apply bind_congr
  intro result
  obtain ⟨nextLeft, nextRight, resumedLeft, resumedRight, same⟩ := RegistrationNativeIdentityHashPair.hash left right paired
    (RegistrationAuthenticationShared.digestArray result.1)
  simp only [resumedLeft, resumedRight]
  have writersLeft : encoder(false) = fullWriter := funext (encode_left setup checks representation created selected placeholder reserve)
  have writersRight : encoder(true) = fullWriter := funext (encode_right setup checks representation created selected placeholder reserve)
  rw [writersLeft,writersRight]
  have result := congrArg (fun distribution => Prod.map id (view placeholder) <$> distribution)
    (RegistrationNativeIdentityReadyFailure.independent fullReserve RegistrationNativeConcreteCodec.serializerBranches nextLeft nextRight same result.2)
  simpa only [Functor.map_map,Prod.map_def,id_eq] using result

end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaSuffix


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaSuffix.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaSuffix.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaSuffix.ed_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaSuffix.ed_stable
