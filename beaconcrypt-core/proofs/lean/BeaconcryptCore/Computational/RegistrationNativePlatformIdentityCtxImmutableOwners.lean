-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedKeys
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners
def snapshot {source : RegistrationNativeMldsa.Source} (owner : RegistrationNativeIdentityFrontend.Owner source) :=
  { owner with phase := .fresh, edHistory := [] }
def snapshots {source : RegistrationNativeMldsa.Source} (owners : RegistrationNativeIdentityFrontend.State source) := owners.map snapshot
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners

namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.Core
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeIdentityFrontend
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value Other : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private def key (owner : Owner source) := snapshot owner
def keys (current : State source) := current.map key

def Preserves (work : M n KemSK Auxiliary source Value) : Prop :=
  ∀ current env result, result ∈ support ((work.run current).run env) → keys result.1.2 = keys current

private theorem pure_preserves (value : Value) : Preserves (pure value : M n KemSK Auxiliary source Value) := by
  intro current env result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem get_preserves : Preserves (get : M n KemSK Auxiliary source (State source)) := by
  intro current env result supported
  simp only [StateT.run_get, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem bind_preserves (work : M n KemSK Auxiliary source Value) (next : Value → M n KemSK Auxiliary source Other)
    (first : Preserves work) (later : ∀ value, Preserves (next value)) : Preserves (work >>= next) := by
  intro current env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (later middle.1.1 middle.1.2 middle.2 result continued).trans (first current env middle reached)

private theorem lift_preserves (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Preserves (StateT.lift work : M n KemSK Auxiliary source Value) := by
  intro current env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _reached, returned⟩ := supported
  cases returned
  rfl

private theorem simulate_preserves {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (M n KemSK Auxiliary source))
    (step : ∀ query, Preserves (implementation query)) (work : OracleComp spec Value) :
    Preserves (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_preserves value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_preserves _ _ (step query) ih

private theorem sample_preserves (work : ProbComp Value) :
    Preserves (sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) :=
  simulate_preserves (fun (query : unifSpec.Domain) => effect (.inl query)) (fun _ => lift_preserves _) work

private theorem set_found {Element : Type} (items : List Element) (index : Nat) (value : Element)
    (found : items[index]? = some value) : items.set index value = items := by
  induction items generalizing index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | cons head rest ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero] at found; cases found; rfl
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          change head :: rest.set index value = head :: rest
          rw [ih index found]

private theorem current_preserves (index : Nat) (change : Owner source → Owner source)
    (same : ∀ owner, key (change owner) = key owner) :
    Preserves ((modify fun current => match current[index]? with
      | none => current
      | some selected => current.set index (change selected)) : M n KemSK Auxiliary source Unit) := by
  intro current env result supported
  simp only [StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  cases found : current[index]? with
  | none => simp only []
  | some selected =>
      simp only [keys, List.map_set, same]
      apply set_found
      simp only [List.getElem?_map, found, Option.map_some]

private theorem phase_preserves (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    Preserves (updatePhase (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index phase) :=
  current_preserves index (fun owner => { owner with phase }) (fun _ => rfl)

private theorem history_preserves (index : Nat) (message : Pqxdh.Bytes) (value : PqxdhEd25519EufCma.Ed25519Signature) :
    Preserves (logEd (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index message value) :=
  current_preserves index (fun owner => { owner with edHistory := owner.edHistory ++ [.signed message value] }) (fun _ => rfl)

private theorem outgoing_preserves (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Preserves (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  classical
  cases query with
  | inl query => cases query with
    | hash request => exact lift_preserves _
    | sign request payload digest =>
        exact bind_preserves _ _ (sample_preserves _) (fun _ => bind_preserves _ _ (lift_preserves _) (fun _ => pure_preserves _))
  | inr request =>
      simp only [outgoing]
      split
      · apply bind_preserves _ _ (lift_preserves _)
        intro value
        cases value with
        | none => exact pure_preserves _
        | some value => exact bind_preserves _ _ (history_preserves index _ value) (fun _ => pure_preserves _)
      · exact pure_preserves _

private theorem authentication_preserves (setup : Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    Preserves (authentication (n := n) (Auxiliary := Auxiliary) setup source query) := by
  cases query with
  | hash request => exact bind_preserves _ _ (lift_preserves _) (fun _ => pure_preserves _)
  | mldsa request | ed25519 request => exact pure_preserves _

private theorem primitive_preserves (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Preserves (primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  cases query with
  | convertSecret role => cases role <;> exact pure_preserves _
  | dh request => cases role : request.secret_role <;>
      simp only [primitive, role] <;> exact lift_preserves _
  | convertPublic key | generate role | encapsulate key | decapsulate ciphertext => exact lift_preserves _

private theorem agreement_preserves (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    Preserves (agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  apply bind_preserves _ _ (lift_preserves _)
  intro _
  cases query with
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | dh request =>
      simp only [agreementCore]
      exact primitive_preserves setup owner oneTime _
  | root request => exact pure_preserves _

private theorem record_preserves (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Preserves (record (n := n) (Auxiliary := Auxiliary) (source := source) setup wire query) := lift_preserves _

private theorem abort_preserves (owner : Owner source) : Preserves (abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner) :=
  bind_preserves _ _ (lift_preserves _) (fun _ => pure_preserves _)

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.Core

namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.Bundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformIdentityCtxImmutableOwners.Core (keys)
open RegistrationNativePlatformIdentityProgram (M)
variable {n : Nat} {ι KemSK Auxiliary Platform E Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Preserves (work : M n KemSK Auxiliary Platform source Value) : Prop :=
  ∀ current env previous result, result ∈ support (((work.run current).run env).run previous) →
    keys result.1.1.2 = keys current

private theorem support_simulate_subset {κ τ A : Type} {spec : OracleSpec κ} {other : OracleSpec τ}
    (implementation : QueryImpl spec (OracleComp other)) (work : OracleComp spec A) :
    support (simulateQ implementation work) ⊆ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]; exact Set.Subset.refl _
  | query_bind query next ih =>
    intro result reached
    simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
    obtain ⟨answer, _first, continued⟩ := reached
    exact (mem_support_bind_iff _ _ _).mpr ⟨answer, mem_support_query query answer, ih answer continued⟩

/-- Pure source replies retain the full immutable credential roster. -/
private theorem pure_preserves (value : Value) : Preserves (pure value : M n KemSK Auxiliary Platform source Value) := by
  intro current env previous result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem get_preserves : Preserves (get : M n KemSK Auxiliary Platform source (RegistrationNativeIdentityFrontend.State source)) := by
  intro current env previous result supported
  simp only [StateT.run_get, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

/-- Complete adaptive continuation preserves metadata only after the actual reached first operation. -/
private theorem bind_preserves (work : M n KemSK Auxiliary Platform source Value) (next : Value → M n KemSK Auxiliary Platform source Next)
    (first : Preserves work) (later : ∀ value, Preserves (next value)) : Preserves (work >>= next) := by
  intro current env previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (later middle.1.1.1 middle.1.1.2 middle.1.2 middle.2 result continued).trans (first current env previous middle reached)

/-- Existing all-reply metadata preservation lifts through the native request branch without changing P. -/
private theorem native_preserves (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (preserves : RegistrationNativePlatformIdentityCtxImmutableOwners.Core.Preserves work) :
    Preserves (RegistrationNativePlatformIdentityProgram.native (Platform := Platform) work) := by
  intro current env previous result supported
  simp only [RegistrationNativePlatformIdentityProgram.native, StateT.run, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  cases returned
  exact preserves current env inner (support_simulate_subset _ _ reached)

/-- The actual stateful serializer has no access to owner metadata, including all failed prefixes. -/
private theorem external_preserves (work : StateT Platform ProbComp Value) :
    Preserves (RegistrationNativePlatformIdentityProgram.external (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) := by
  intro current env previous result supported
  simp only [RegistrationNativePlatformIdentityProgram.external, StateT.run, support_map] at supported
  obtain ⟨inner, _reached, returned⟩ := supported
  cases returned
  rfl

private theorem simulate_preserves {κ : Type} {spec : OracleSpec κ}
    (implementation : QueryImpl spec (M n KemSK Auxiliary Platform source))
    (step : ∀ request, Preserves (implementation request)) (work : OracleComp spec Value) :
    Preserves (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_preserves value
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact bind_preserves _ _ (step query) ih

private theorem next_preserves (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (reply : RegistrationNativePlatformIdentityBundle.Reply) :
    Preserves (RegistrationNativePlatformIdentityBundle.next (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact pure_preserves _
  | ok reply => cases reply with
    | Err error => exact pure_preserves _
    | Ok published =>
      exact bind_preserves _ _
        (native_preserves _ (RegistrationNativePlatformIdentityCtxImmutableOwners.Core.phase_preserves index _))
        (fun _ => bind_preserves _ _ (native_preserves _ (RegistrationNativePlatformIdentityCtxImmutableOwners.Core.lift_preserves _)) (fun _ => pure_preserves _))

private theorem bundled_preserves (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := Auxiliary) setup index owner oneTime writer) := by
  apply bind_preserves _ _ (simulate_preserves _ ?_ _)
  · exact next_preserves index owner oneTime
  · intro request
    cases request with
    | inl request => exact native_preserves _ (RegistrationNativePlatformIdentityCtxImmutableOwners.Core.outgoing_preserves setup index owner request)
    | inr request => exact external_preserves _

private theorem start_preserves (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (RegistrationNativePlatformIdentityBundleRun.start (n := n) (Auxiliary := Auxiliary) setup index owner writer) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
    exact bind_preserves _ _ (native_preserves _ (RegistrationNativePlatformIdentityCtxImmutableOwners.Core.sample_preserves _))
      (fun scalar => bundled_preserves setup index owner scalar writer)
  | freshWithCoins scalar =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind] using bundled_preserves setup index owner scalar writer
  | initSent pending scalar | established completed | aborted previous =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase] using
      (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) (.ok none : RustM (Option (alloc.vec.Vec U8))))

/-- Complete actual stateful bundle lookup and all optional writer results retain the actual immutable credential roster. -/
private theorem bundle_preserves (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (RegistrationNativePlatformIdentityBundleRun.bundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer) := by
  apply bind_preserves _ _ get_preserves
  intro current
  cases current[index]? with
  | none => exact pure_preserves _
  | some owner => exact start_preserves setup index owner writer

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.Bundle

namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.Finish
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformIdentityCtxImmutableOwners.Core
open RegistrationNativeIdentityFrontend (Owner)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem abort_value (owner : Owner source) {Value : Type} (value : Value) :
    Preserves (RegistrationNativeIdentityFrontend.abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner *> pure value) := by
  simpa only [seqRight_eq_bind] using bind_preserves _ _ (abort_preserves owner) (fun _ => pure_preserves value)

private theorem finish_record (index : Nat) (owner : Owner source) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Preserves (RegistrationNativePlatformIdentityFinishRecord.after (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner reply) := by
  cases reply with
  | fail error | div => exact abort_value owner _
  | ok result => cases result with
    | Err error => exact abort_value owner _
    | Ok established =>
        change Preserves (RegistrationNativePlatformIdentityFinishRecord.install index owner established)
        rw [RegistrationNativePlatformIdentityFinishRecord.install_exact]
        apply bind_preserves _ _ (lift_preserves _)
        intro installed
        cases installed with
        | false => exact abort_value owner _
        | true => exact bind_preserves _ _ (phase_preserves index _) (fun _ => pure_preserves _)

private theorem finish_agreement (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (reply : RustM agreement.AgreementEffect) :
    Preserves (RegistrationNativePlatformIdentityFinishSteps.afterAgreement (n := n) (Auxiliary := Auxiliary) setup wire index owner reply) := by
  cases reply with
  | fail error | div => exact abort_value owner _
  | ok effect => cases effect with
    | Rejected previous | ConvertPublic pending | ConvertSecret pending | GenerateEphemeral pending | Encapsulate pending
      | Decapsulate pending | Dh pending | RootKdf pending | ServerComplete completed => exact abort_value owner _
    | BeaconComplete completed =>
        exact bind_preserves _ _ (simulate_preserves _ (record_preserves setup wire) _) (finish_record index owner)

private theorem finish_authentication (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Preserves (RegistrationNativePlatformIdentityFinishSteps.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact abort_value owner _
  | ok result => cases result with
    | Err previous => exact abort_value owner _
    | Ok accepted =>
        exact bind_preserves _ _ (simulate_preserves _ (agreement_preserves setup owner oneTime) _)
          (finish_agreement setup wire index owner)

private theorem finish_begin (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) :
    Preserves (RegistrationNativePlatformIdentityFinishSteps.begin (n := n) (Auxiliary := Auxiliary) setup wire index owner pending oneTime packet) := by
  cases moved : pending.aborted_state with
  | fail error | div =>
      simpa only [RegistrationNativePlatformIdentityFinishSteps.begin, moved] using
        (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) _)
  | ok aborted =>
      simp only [RegistrationNativePlatformIdentityFinishSteps.begin, moved]
      exact bind_preserves _ _ (phase_preserves index _) (fun _ =>
        bind_preserves _ _ (simulate_preserves _ (authentication_preserves setup) _) (finish_authentication setup wire index owner oneTime))

private theorem finish_start (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (packet : Option registration.ResponsePacket) :
    Preserves (RegistrationNativePlatformIdentityFinishRun.start (n := n) (Auxiliary := Auxiliary) setup wire index owner packet) := by
  cases phase : owner.phase with
  | initSent pending oneTime =>
      simpa only [RegistrationNativePlatformIdentityFinishRun.start, phase] using finish_begin setup wire index owner pending oneTime packet
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simpa only [RegistrationNativePlatformIdentityFinishRun.start, phase] using
        (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (.ok none : RustM (Option Pqxdh.Bytes)))

/-- Actual finish retains immutable public credentials and fields through abort, verifier failure, optional agreement/opening failure and successful kernel installation. -/
private theorem finish_preserves (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) :
    Preserves (RegistrationNativePlatformIdentityFinishRun.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  intro current env result supported
  cases found : current[index]? with
  | none =>
      simp only [RegistrationNativePlatformIdentityFinishRun.finish, StateT.run_bind, StateT.run_get,
        pure_bind, found, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some owner =>
      simp only [RegistrationNativePlatformIdentityFinishRun.finish, StateT.run_bind, StateT.run_get,
        pure_bind, found] at supported
      exact finish_start setup wire index owner packet current env result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.Finish

namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private def Extends (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A) : Prop :=
  ∀ current env previous result, result ∈ support (((work.run current).run env).run previous) →
    snapshots current <+: snapshots result.1.1.2

private theorem beacon_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (prefixLaw : Extends work) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : A × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work).run before)) :
    snapshots before.1.beacons <+: snapshots result.2.1.beacons := by
  simp only [RegistrationNativePlatformIdentityCtxMain.beacon,RegistrationNativePlatformIdentityCtxCompiler.beacon,
    StateT.run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  apply prefixLaw _ _ _ inner.1
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) _ before.1.context
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called


private theorem append_prefix (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (keyId : U64) (prepared : RegistrationNativeIdentityFrontend.Prepared source)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (supported : result ∈ support (((RegistrationNativeIdentitySourceCreate.append (n := n) setup source edPin keyId prepared).run current).run env)) :
    snapshots current <+: snapshots result.1.2 := by
  rw [RegistrationNativeIdentitySourceCreate.append_program] at supported
  have raw := Bundle.support_simulate_subset _ _ supported
  simp only [mem_support_bind_iff,mem_support_pure_iff] at raw
  obtain ⟨born,_generated,worldOwner,_allocated,rfl⟩ := raw
  simp only [snapshots,List.map_append]
  exact List.prefix_append _ _

private theorem native_create_prefix (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (supported : result ∈ support (((RegistrationNativeIdentityFrontend.create (n := n) setup source edPin mlPin keyId).run current).run env)) :
    snapshots current <+: snapshots result.1.2 := by
  rw [RegistrationNativeIdentitySourceCreate.create_factor] at supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,reached,continued⟩ := supported
  have same : middle.1.2 = current := by
    rw [RegistrationNativeIdentitySourcePrepare.prepare_run,support_map] at reached
    obtain ⟨inner,_called,rfl⟩ := reached
    rfl
  rcases middle with ⟨⟨reply,nextOwners⟩,nextEnv⟩
  change nextOwners = current at same
  subst nextOwners
  cases reply with
  | fail error | div =>
    simp only [StateT.run_pure,mem_support_pure_iff] at continued
    cases continued
    exact List.prefix_rfl
  | ok reply => cases reply with
    | none =>
      simp only [StateT.run_pure,mem_support_pure_iff] at continued
      cases continued
      exact List.prefix_rfl
    | some prepared => exact append_prefix setup edPin keyId prepared current nextEnv result continued


private theorem native_create_extends (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Extends (RegistrationNativePlatformIdentityProgram.native (Platform := Platform)
      (RegistrationNativeIdentityFrontend.create (n := n) setup source edPin mlPin keyId)) := by
  intro current env previous result supported
  simp only [RegistrationNativePlatformIdentityProgram.native,StateT.run,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact native_create_prefix setup edPin mlPin keyId current env inner (Bundle.support_simulate_subset _ _ called)

private theorem preserving_extends
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (safe : Bundle.Preserves work) : Extends work := by
  intro current env previous result supported
  have same := safe current env previous result supported
  change snapshots result.1.1.2 = snapshots current at same
  rw [same]

private theorem create_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : RustM (Option Nat) × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxLifecycle.create setup edPin mlPin keyId checks representation created).run before)) :
    snapshots before.1.beacons <+: snapshots result.2.1.beacons :=
  beacon_prefix setup checks representation created _ (native_create_extends setup edPin mlPin keyId) before result reached


private theorem bundle_prefix {E : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : RustM (Option Pqxdh.Bytes) × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index).run before)) :
    snapshots before.1.beacons <+: snapshots result.2.1.beacons := by
  have same : (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index).run before =
      Prod.map RegistrationNativePlatformIdentityNativeBundle.reply id <$>
        (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
          (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer)).run before := by
    exact StateT.run_map _ _ _
  rw [same,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  exact beacon_prefix setup checks representation created _
    (preserving_extends _ (Bundle.bundle_preserves setup index writer)) before inner called

private theorem finish_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : RustM (Option Pqxdh.Bytes) × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxLifecycle.finish setup checks representation created wire index packet).run before)) :
    snapshots before.1.beacons <+: snapshots result.2.1.beacons :=
  beacon_prefix setup checks representation created _
    (preserving_extends _ (Bundle.native_preserves _ (Finish.finish_preserves setup wire index packet))) before result reached


private theorem ordinary_prefix (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : A × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxOrdinary.ordinary work).run before)) :
    snapshots before.1.beacons <+: snapshots result.2.1.beacons := by
  simp only [RegistrationNativePlatformIdentityCtxOrdinary.ordinary,RegistrationNativePlatformIdentityCtxCompiler.ordinary,
    StateT.run,support_map] at reached
  obtain ⟨inner,_called,rfl⟩ := reached
  exact List.prefix_rfl

private theorem report_prefix (packet : registration.InitPacket)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : Unit × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxOrdinary.report packet).run before)) :
    snapshots before.1.beacons <+: snapshots result.2.1.beacons := by
  have reportRun : (RegistrationNativeIdentityMain.report (n := n) (KemSK := KemSK) (mlSource := source) packet).run before.1 =
      (fun reply : Unit => (reply,before.1)) <$> RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityMain.reports packet before.1.beacons) := by
    simp only [RegistrationNativeIdentityMain.report,StateT.run_bind,StateT.run_get,pure_bind,StateT.run_lift,bind_pure_comp]
  change result ∈ support ((fun result => (result.1,(result.2,before.2))) <$>
    simulateQ RegistrationNativePlatformIdentityCtxCompiler.protocol ((RegistrationNativeIdentityMain.report packet).run before.1)) at reached
  rw [reportRun,simulateQ_map,Functor.map_map,support_map] at reached
  obtain ⟨inner,_called,rfl⟩ := reached
  exact List.prefix_rfl



open BeaconcryptCore.Refinement
open RegistrationNativeRawAdapter (TypedSpec)
variable [primitives : AdapterSealPrimitive.Operations]
variable {E : Type}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

private theorem ambient_prefix (query : TypedSpec.Domain)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : TypedSpec.Range query × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxDispatch.step setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    snapshots before.1.beacons <+: snapshots result.2.1.beacons :=
  ordinary_prefix _ before result reached

/-- Every literal current callback preserves the complete immutable owner snapshot in order, for arbitrary source replies and platform failures. Only phase and Ed history are omitted. -/
theorem free_handler_prefix (query : TypedSpec.Domain)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : TypedSpec.Range query × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((frontend query).run before)) :
    snapshots before.1.beacons <+: snapshots result.2.1.beacons := by
  cases query with
  | inl coin => exact ambient_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result reached
  | inr query => cases query with
    | create edPin mlPin keyId => exact create_prefix setup checks representation created edPin mlPin keyId before result reached
    | bundle index => exact bundle_prefix setup checks representation created writer index before result reached
    | finish index packet => exact finish_prefix setup checks representation created (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet before result reached
    | accept packet =>
      unfold RegistrationNativePlatformIdentityCtxTyped.handler at reached
      rw [StateT.run_bind,mem_support_bind_iff] at reached
      obtain ⟨middle,first,last⟩ := reached
      exact (report_prefix packet before middle first).trans
        (ambient_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ middle.2 result last)
    | build session application | hmac key message | hash bytes | serverSend keyId plaintext | serverRaw raw | beaconSend index plaintext | beaconRaw index raw =>
      exact ambient_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result reached


/-- All old immutable owner snapshots remain at their original indices after any adaptive free source program. -/
theorem free_program_prefix (work : OracleComp TypedSpec A)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : A × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((simulateQ frontend work).run before)) :
    snapshots before.1.beacons <+: snapshots result.2.1.beacons := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at reached
    cases reached
    exact List.prefix_rfl
  | query_bind query next ih =>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at reached
    obtain ⟨middle,first,last⟩ := reached
    exact (free_handler_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before middle first).trans
      (ih middle.1 middle.2 result last)

/-- Closing the real private source retains the same full snapshot prefix with no ownership or security premise. -/
theorem handler_prefix (query : TypedSpec.Domain)
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : TypedSpec.Range query × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (frontend query)).run before)) :
    snapshots before.1.1.beacons <+: snapshots result.2.1.1.beacons := by
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret,StateT.run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  apply free_handler_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1 inner.1
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

/-- Entire real interpreted adaptive programs preserve the immutable owner prefix on every failure or success path. -/
theorem program_prefix (work : OracleComp TypedSpec A)
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : A × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (simulateQ frontend work)).run before)) :
    snapshots before.1.1.beacons <+: snapshots result.2.1.1.beacons := by
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret,StateT.run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  apply free_program_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work before.1 inner.1
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called


/-- Every original interpreted callback path retains all preceding complete immutable snapshots. -/
theorem path_prefix
    {first last : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source}
    {calls : List (RegistrationNativeStageTrace.Call TypedSpec (RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source))}
    (path : RegistrationNativeStageTrace.Path (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (frontend query)) first calls last) :
    snapshots first.1.1.beacons <+: snapshots last.1.1.beacons := by
  induction path with
  | nil => exact List.prefix_rfl
  | cons call called rest last following ih =>
    exact (handler_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      call.query call.before (call.reply,call.after) called).trans ih

omit primitives in
/-- A captured owner remains at the same later list index with its entire immutable snapshot, independently of public-key aliases. -/
theorem snapshot_at (first last : RegistrationNativeIdentityFrontend.State source)
    (retained : snapshots first <+: snapshots last) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (found : first[index]? = some owner) :
    ∃ finalOwner, last[index]? = some finalOwner ∧ snapshot finalOwner = snapshot owner := by
  have earlier : (snapshots first)[index]? = some (snapshot owner) := by
    simp only [snapshots,List.getElem?_map,found,Option.map_some]
  obtain ⟨tail,same⟩ := retained
  have later : (snapshots last)[index]? = some (snapshot owner) := by
    rw [← same,List.getElem?_append_left (List.getElem?_eq_some_iff.mp earlier).1]
    exact earlier
  simp only [snapshots,List.getElem?_map] at later
  cases selected : last[index]? with
  | none => simp only [selected,Option.map_none] at later; cases later
  | some finalOwner =>
    refine ⟨finalOwner,rfl,?_⟩
    simpa only [selected,Option.map_some,Option.some.injEq] using later

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.free_handler_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.free_handler_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.free_program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.free_program_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.handler_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.handler_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.program_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.path_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.path_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.snapshot_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners.snapshot_at
