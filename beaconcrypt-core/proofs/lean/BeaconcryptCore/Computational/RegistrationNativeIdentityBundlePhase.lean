-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxImmutableOwners
/-! The original source owner cannot become bundle-eligible again once its pending or terminal phase has been reached. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase
open RegistrationNativeIdentityFrontend (Owner State)
open RegistrationNativeBeaconFrontend (Phase)
variable {source : RegistrationNativeMldsa.Source}

def Eligible : Phase → Prop
  | .fresh | .freshWithCoins _ => True
  | _ => False
instance : DecidablePred Eligible := fun phase => by cases phase <;> unfold Eligible <;> infer_instance

def Closed (index : Nat) (owners : State source) : Prop :=
  ∃ owner, owners[index]?=some owner ∧ ¬Eligible owner.phase

def Keeps (before after : State source) : Prop :=
  ∀ (index : Nat) (owner : Owner source), before[index]?=some owner →
    ∃ current : Owner source,after[index]?=some current ∧ (¬Eligible owner.phase → ¬Eligible current.phase)

theorem Keeps.refl (owners : State source) : Keeps owners owners := fun _ owner found=>⟨owner,found,fun prior=>prior⟩

theorem Keeps.trans {first middle last : State source} (following : Keeps middle last) (previous : Keeps first middle) : Keeps first last := by
  intro index owner found
  obtain ⟨current,present,closed⟩ := previous index owner found
  obtain ⟨later,there,kept⟩ := following index current present
  exact ⟨later,there,fun prior=>kept (closed prior)⟩

/-- The same preexisting position stays closed through every later callback. -/
theorem Keeps.closed {before after : State source} (kept : Keeps before after) (index : Nat) (prior : Closed index before) : Closed index after := by
  obtain ⟨owner,found,closed⟩ := prior
  obtain ⟨current,present,policy⟩ := kept index owner found
  exact ⟨current,present,policy closed⟩

/-- Source creation appends a new owner without changing any earlier closed position. -/
theorem append (owners : State source) (owner : Owner source) : Keeps owners (owners++[owner]) := by
  intro index earlier found
  exact ⟨earlier,by simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found,fun prior=>prior⟩

/-- Updating one actual owner can retain closedness using only that owner's phase policy. -/
theorem current (owners : State source) (index : Nat) (change : Owner source → Owner source)
    (policy : ∀ owner, ¬Eligible owner.phase → ¬Eligible (change owner).phase) :
    Keeps owners (match owners[index]? with |none=>owners|some owner=>owners.set index (change owner)) := by
  intro selected earlier present
  cases found : owners[index]? with
  | none => exact ⟨earlier,present,fun prior=>prior⟩
  | some owner =>
      by_cases same : selected=index
      · subst selected
        have equal := Option.some.inj (present.symm.trans found)
        subst earlier
        exact ⟨change owner,List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1,policy owner⟩
      · exact ⟨earlier,by simpa only [List.getElem?_set_ne (Ne.symm same)] using present,fun prior=>prior⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase

namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Core
open RegistrationNativeIdentityBundlePhase (Keeps Eligible)
open RegistrationNativeIdentityFrontend
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {KemSK Auxiliary Value Next : Type} {source : RegistrationNativeMldsa.Source}

def Preserves (work : M n KemSK Auxiliary source Value) : Prop :=
  ∀ current env result, result ∈ support ((work.run current).run env) → Keeps current result.1.2

private theorem pure_preserves (value : Value) : Preserves (pure value : M n KemSK Auxiliary source Value) := by
  intro current env result supported
  simp only [StateT.run_pure,mem_support_pure_iff] at supported
  cases supported
  exact Keeps.refl current

private theorem get_preserves : Preserves (get : M n KemSK Auxiliary source (State source)) := by
  intro current env result supported
  simp only [StateT.run_get,StateT.run_pure,mem_support_pure_iff] at supported
  cases supported
  exact Keeps.refl current

private theorem bind_preserves (work : M n KemSK Auxiliary source Value) (next : Value → M n KemSK Auxiliary source Next)
    (first : Preserves work) (later : ∀ value,Preserves (next value)) : Preserves (work>>=next) := by
  intro current env result supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩ := supported
  exact (later middle.1.1 middle.1.2 middle.2 result continued).trans (first current env middle called)

private theorem lift_preserves (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Preserves (StateT.lift work : M n KemSK Auxiliary source Value) := by
  intro current env result supported
  simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at supported
  obtain ⟨middle,_called,equal⟩ := supported
  cases equal
  exact Keeps.refl current

private theorem simulate_preserves {Q : Type} {spec : OracleSpec Q}
    (implementation : QueryImpl spec (M n KemSK Auxiliary source))
    (step : ∀ query,Preserves (implementation query)) (work : OracleComp spec Value) :
    Preserves (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_preserves value
  | query_bind query next ih =>
      rw [simulateQ_bind,simulateQ_spec_query]
      exact bind_preserves _ _ (step query) ih

private theorem sample_preserves (work : ProbComp Value) :
    Preserves (sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) :=
  simulate_preserves (fun (query : unifSpec.Domain) => effect (.inl query)) (fun _=>lift_preserves _) work

private theorem current_preserves (index : Nat) (change : Owner source → Owner source)
    (policy : ∀ owner,¬Eligible owner.phase → ¬Eligible (change owner).phase) :
    Preserves ((modify fun current => match current[index]? with
      |none=>current|some owner=>current.set index (change owner)) : M n KemSK Auxiliary source Unit) := by
  intro current env result supported
  simp only [StateT.run_modify,StateT.run_pure,mem_support_pure_iff] at supported
  cases supported
  exact RegistrationNativeIdentityBundlePhase.current current index change policy

private theorem phase_preserves (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) (closed : ¬Eligible phase) :
    Preserves (updatePhase (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index phase) :=
  current_preserves index (fun owner=>{owner with phase}) (fun _ _=>closed)

private theorem history_preserves (index : Nat) (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Preserves (logEd (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index message signature) :=
  current_preserves index (fun owner=>{owner with edHistory:=owner.edHistory++[.signed message signature]}) (fun _ prior=>prior)

variable {ι : Type} {base : OracleSpec ι}
open PqxdhServerAuthExperiment (Setup)

private theorem outgoing_preserves (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Preserves (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  classical
  cases query with
  | inl query => cases query with
    | hash request => exact lift_preserves _
    | sign request payload digest =>
        exact pure_preserves _
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

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Core

namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Finish
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeIdentityBundlePhase.Core
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
        | true => exact bind_preserves _ _ (phase_preserves index _ (by simp [Eligible])) (fun _ => pure_preserves _)

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
      exact bind_preserves _ _ (phase_preserves index _ (by simp [Eligible])) (fun _ =>
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

/-- Actual finish retains every existing owner position and its closedness through abort, verifier failure, optional agreement/opening failure and successful kernel installation. -/
private theorem finish_preserves (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) :
    Preserves (RegistrationNativePlatformIdentityFinishRun.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  intro current env result supported
  cases found : current[index]? with
  | none =>
      simp only [RegistrationNativePlatformIdentityFinishRun.finish, StateT.run_bind, StateT.run_get,
        pure_bind, found, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact Keeps.refl current
  | some owner =>
      simp only [RegistrationNativePlatformIdentityFinishRun.finish, StateT.run_bind, StateT.run_get,
        pure_bind, found] at supported
      exact finish_start setup wire index owner packet current env result supported

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Finish

namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Bundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeIdentityBundlePhase (Keeps Eligible)
open RegistrationNativePlatformIdentityProgram (M)
variable {n : Nat} {ι KemSK Auxiliary Platform E Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Preserves (work : M n KemSK Auxiliary Platform source Value) : Prop :=
  ∀ current env previous result, result ∈ support (((work.run current).run env).run previous) →
    Keeps current result.1.1.2

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

/-- Pure source replies retain every existing phase position. -/
private theorem pure_preserves (value : Value) : Preserves (pure value : M n KemSK Auxiliary Platform source Value) := by
  intro current env previous result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact Keeps.refl current

private theorem get_preserves : Preserves (get : M n KemSK Auxiliary Platform source (RegistrationNativeIdentityFrontend.State source)) := by
  intro current env previous result supported
  simp only [StateT.run_get, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact Keeps.refl current

/-- Adaptive continuation retains the phase policy after the actual reached first operation. -/
private theorem bind_preserves (work : M n KemSK Auxiliary Platform source Value) (next : Value → M n KemSK Auxiliary Platform source Next)
    (first : Preserves work) (later : ∀ value, Preserves (next value)) : Preserves (work >>= next) := by
  intro current env previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (later middle.1.1.1 middle.1.1.2 middle.1.2 middle.2 result continued).trans (first current env previous middle reached)

/-- The all-reply phase policy lifts through the native request branch without changing P. -/
private theorem native_preserves (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (preserves : RegistrationNativeIdentityBundlePhase.Core.Preserves work) :
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
  exact Keeps.refl current

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
        (native_preserves _ (RegistrationNativeIdentityBundlePhase.Core.phase_preserves index _ (by simp [Eligible])))
        (fun _ => bind_preserves _ _ (native_preserves _ (RegistrationNativeIdentityBundlePhase.Core.lift_preserves _)) (fun _ => pure_preserves _))

private theorem bundled_preserves (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := Auxiliary) setup index owner oneTime writer) := by
  apply bind_preserves _ _ (simulate_preserves _ ?_ _)
  · exact next_preserves index owner oneTime
  · intro request
    cases request with
    | inl request => exact native_preserves _ (RegistrationNativeIdentityBundlePhase.Core.outgoing_preserves setup index owner request)
    | inr request => exact external_preserves _

private theorem start_preserves (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (RegistrationNativePlatformIdentityBundleRun.start (n := n) (Auxiliary := Auxiliary) setup index owner writer) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
    exact bind_preserves _ _ (native_preserves _ (RegistrationNativeIdentityBundlePhase.Core.sample_preserves _))
      (fun scalar => bundled_preserves setup index owner scalar writer)
  | freshWithCoins scalar =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind] using bundled_preserves setup index owner scalar writer
  | initSent pending scalar | established completed | aborted previous =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase] using
      (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) (.ok none : RustM (Option (alloc.vec.Vec U8))))

/-- Actual bundle lookup and every optional writer result retain all existing closed positions. -/
private theorem bundle_preserves (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (RegistrationNativePlatformIdentityBundleRun.bundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer) := by
  apply bind_preserves _ _ get_preserves
  intro current
  cases current[index]? with
  | none => exact pure_preserves _
  | some owner => exact start_preserves setup index owner writer

private theorem publication_preserves (setup : Setup base KemSK) (index : Nat)
    (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) Value) :
    Preserves (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary) setup index owner writer) work) := by
  apply simulate_preserves
  intro request
  cases request with
  | inl request => exact native_preserves _ (Core.outgoing_preserves setup index owner request)
  | inr request => exact external_preserves _

private theorem next_closed (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (reply : RegistrationNativePlatformIdentityBundle.Reply)
    (current : RegistrationNativeIdentityFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (previous : Platform) (encoded : alloc.vec.Vec U8)
    (present : ∃ earlier,current[index]?=some earlier)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState Auxiliary) × Platform)
    (supported : result ∈ support ((((RegistrationNativePlatformIdentityBundle.next (n := n) (KemSK := KemSK) index owner oneTime reply).run current).run env).run previous))
    (returned : result.1.1.1=.ok (some encoded)) : Closed index result.1.1.2 := by
  cases reply with
  | fail error | div =>
      simp only [RegistrationNativePlatformIdentityBundle.next,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      cases returned
  | ok answer => cases answer with
    | Err error =>
        simp only [RegistrationNativePlatformIdentityBundle.next,StateT.run_pure,mem_support_pure_iff] at supported
        cases supported
        cases returned
    | Ok published =>
        simp only [RegistrationNativePlatformIdentityBundle.next,StateT.run_bind,mem_support_bind_iff] at supported
        obtain ⟨phase,phaseCalled,advance,advanced,finished⟩ := supported
        obtain ⟨earlier,found⟩ := present
        simp only [RegistrationNativePlatformIdentityProgram.native,RegistrationNativeIdentityFrontend.updatePhase,
          StateT.run] at phaseCalled
        cases phaseCalled
        have closed : Closed index (current.set index {earlier with phase:=.initSent published.pending oneTime}) :=
          ⟨_,List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1,by simp [Eligible]⟩
        have kept := native_preserves _ (Core.lift_preserves _) _ _ _ advance advanced
        have final := kept.closed index (by simpa only [found] using closed)
        simp only [StateT.run_pure,mem_support_pure_iff] at finished
        cases finished
        exact final

private theorem bundled_closed (setup : Setup base KemSK) (index : Nat)
    (owner : RegistrationNativeIdentityFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (current : RegistrationNativeIdentityFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (previous : Platform) (encoded : alloc.vec.Vec U8) (present : ∃ earlier,current[index]?=some earlier)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState Auxiliary) × Platform)
    (supported : result ∈ support ((((RegistrationNativePlatformIdentityBundle.bundled (n := n) setup index owner oneTime writer).run current).run env).run previous))
    (returned : result.1.1.1=.ok (some encoded)) : Closed index result.1.1.2 := by
  simp only [RegistrationNativePlatformIdentityBundle.bundled,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩ := supported
  obtain ⟨earlier,found⟩ := present
  have kept := publication_preserves setup index owner writer _ current env previous middle called
  obtain ⟨now,there,_policy⟩ := kept index earlier found
  exact next_closed index owner oneTime middle.1.1.1 middle.1.1.2 middle.1.2 middle.2 encoded ⟨now,there⟩ result continued returned

private theorem start_closed (setup : Setup base KemSK) (index : Nat)
    (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (current : RegistrationNativeIdentityFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (previous : Platform) (encoded : alloc.vec.Vec U8) (present : ∃ earlier,current[index]?=some earlier)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState Auxiliary) × Platform)
    (supported : result ∈ support ((((RegistrationNativePlatformIdentityBundleRun.start (n := n) setup index owner writer).run current).run env).run previous))
    (returned : result.1.1.1=.ok (some encoded)) : Closed index result.1.1.2 := by
  cases phase : owner.phase with
  | fresh =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start,phase,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,called,continued⟩ := supported
      obtain ⟨earlier,found⟩ := present
      have kept := native_preserves _ (Core.sample_preserves _) current env previous middle called
      obtain ⟨now,there,_policy⟩ := kept index earlier found
      exact bundled_closed setup index owner middle.1.1.1 writer middle.1.1.2 middle.1.2 middle.2 encoded ⟨now,there⟩ result continued returned
  | freshWithCoins scalar =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start,phase,pure_bind] at supported
      exact bundled_closed setup index owner scalar writer current env previous encoded present result supported returned
  | initSent pending scalar | established completed | aborted aborted =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start,phase,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      cases returned

/-- Every actual successful dynamic-writer source bundle closes its existing owner position to further bundling, regardless of primitive replies or later platform failures. -/
theorem bundle_closed (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (current : RegistrationNativeIdentityFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (previous : Platform) (encoded : alloc.vec.Vec U8)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState Auxiliary) × Platform)
    (supported : result ∈ support ((((RegistrationNativePlatformIdentityBundleRun.bundle (n := n) setup index writer).run current).run env).run previous))
    (returned : result.1.1.1=.ok (some encoded)) : Closed index result.1.1.2 := by
  simp only [RegistrationNativePlatformIdentityBundleRun.bundle,StateT.run_bind,StateT.run_get,pure_bind] at supported
  cases found : current[index]? with
  | none =>
      simp only [found,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      cases returned
  | some owner =>
      rw [found] at supported
      exact start_closed setup index owner writer current env previous encoded ⟨owner,found⟩ result supported returned

/-- An already pending or terminal source owner rejects every later bundle attempt at that same position. -/
theorem bundle_declines (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (current : RegistrationNativeIdentityFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (previous : Platform) (encoded : alloc.vec.Vec U8) (closed : Closed index current)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState Auxiliary) × Platform)
    (supported : result ∈ support ((((RegistrationNativePlatformIdentityBundleRun.bundle (n := n) setup index writer).run current).run env).run previous)) :
    result.1.1.1 ≠ .ok (some encoded) := by
  intro returned
  obtain ⟨owner,found,inactive⟩ := closed
  simp only [RegistrationNativePlatformIdentityBundleRun.bundle,StateT.run_bind,StateT.run_get,pure_bind,found] at supported
  cases phase : owner.phase with
  | fresh | freshWithCoins scalar => simp only [Eligible,phase,not_true_eq_false] at inactive
  | initSent pending scalar | established completed | aborted aborted =>
      simp only [RegistrationNativePlatformIdentityBundleRun.start,phase,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      cases returned

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Bundle

namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private def Extends (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A) : Prop :=
  ∀ current env previous result, result ∈ support (((work.run current).run env).run previous) →
    Keeps current result.1.1.2

private theorem beacon_supported (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : A × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work).run before)) :
    ∃ raw : ((A × RegistrationNativeIdentityFrontend.State source) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × Platform,
      raw ∈ support (((work.run before.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)).run before.2) ∧
      result.1=raw.1.1.1 ∧ result.2.1.beacons=raw.1.1.2 := by
  simp only [RegistrationNativePlatformIdentityCtxMain.beacon,RegistrationNativePlatformIdentityCtxCompiler.beacon,
    StateT.run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  refine ⟨inner.1,?_,rfl,rfl⟩
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) _ before.1.context
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

private theorem beacon_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (prefixLaw : Extends work) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : A × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work).run before)) :
    Keeps before.1.beacons result.2.1.beacons := by
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
    Keeps current result.1.2 := by
  rw [RegistrationNativeIdentitySourceCreate.append_program] at supported
  have raw := Bundle.support_simulate_subset _ _ supported
  simp only [mem_support_bind_iff,mem_support_pure_iff] at raw
  obtain ⟨born,_generated,worldOwner,_allocated,rfl⟩ := raw
  exact append current _

private theorem native_create_prefix (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (supported : result ∈ support (((RegistrationNativeIdentityFrontend.create (n := n) setup source edPin mlPin keyId).run current).run env)) :
    Keeps current result.1.2 := by
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
    exact Keeps.refl _
  | ok reply => cases reply with
    | none =>
      simp only [StateT.run_pure,mem_support_pure_iff] at continued
      cases continued
      exact Keeps.refl _
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
    (safe : Bundle.Preserves work) : Extends work := safe

private theorem create_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : RustM (Option Nat) × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxLifecycle.create setup edPin mlPin keyId checks representation created).run before)) :
    Keeps before.1.beacons result.2.1.beacons :=
  beacon_prefix setup checks representation created _ (native_create_extends setup edPin mlPin keyId) before result reached


private theorem bundle_prefix {E : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : RustM (Option Pqxdh.Bytes) × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index).run before)) :
    Keeps before.1.beacons result.2.1.beacons := by
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
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : RustM (Option Pqxdh.Bytes) × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxLifecycle.finish setup checks representation created wire index packet).run before)) :
    Keeps before.1.beacons result.2.1.beacons :=
  beacon_prefix setup checks representation created _
    (preserving_extends _ (Bundle.native_preserves _ (Finish.finish_preserves setup wire index packet))) before result reached


private theorem ordinary_prefix (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : A × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxOrdinary.ordinary work).run before)) :
    Keeps before.1.beacons result.2.1.beacons := by
  simp only [RegistrationNativePlatformIdentityCtxOrdinary.ordinary,RegistrationNativePlatformIdentityCtxCompiler.ordinary,
    StateT.run,support_map] at reached
  obtain ⟨inner,_called,rfl⟩ := reached
  exact Keeps.refl _

private theorem report_prefix (packet : registration.InitPacket)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : Unit × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxOrdinary.report packet).run before)) :
    Keeps before.1.beacons result.2.1.beacons := by
  have reportRun : (RegistrationNativeIdentityMain.report (n := n) (KemSK := KemSK) (mlSource := source) packet).run before.1 =
      (fun reply : Unit => (reply,before.1)) <$> RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityMain.reports packet before.1.beacons) := by
    simp only [RegistrationNativeIdentityMain.report,StateT.run_bind,StateT.run_get,pure_bind,StateT.run_lift,bind_pure_comp]
  change result ∈ support ((fun result => (result.1,(result.2,before.2))) <$>
    simulateQ RegistrationNativePlatformIdentityCtxCompiler.protocol ((RegistrationNativeIdentityMain.report packet).run before.1)) at reached
  rw [reportRun,simulateQ_map,Functor.map_map,support_map] at reached
  obtain ⟨inner,_called,rfl⟩ := reached
  exact Keeps.refl _



open BeaconcryptCore.Refinement
open RegistrationNativeRawAdapter (TypedSpec)
variable [primitives : AdapterSealPrimitive.Operations]
variable {E : Type}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
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
    Keeps before.1.beacons result.2.1.beacons :=
  ordinary_prefix _ before result reached

attribute [local irreducible] RegistrationNativePlatformIdentityCtxDispatch.step

/-- Every literal current callback retains each existing owner position and never revives a pending or terminal phase, for arbitrary source replies and platform failures. -/
theorem free_handler (query : TypedSpec.Domain)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : TypedSpec.Range query × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((frontend query).run before)) :
    Keeps before.1.beacons result.2.1.beacons := by
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
      exact (ambient_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ middle.2 result last).trans
        (report_prefix packet before middle first)
    | build session application | hmac key message | hash bytes | serverSend keyId plaintext | serverRaw raw | beaconSend index plaintext | beaconRaw index raw =>
      exact ambient_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result reached



omit primitives in
/-- Every successful literal CTX bundle leaves that source owner closed, for arbitrary source replies and without generated-row ownership as a premise. -/
theorem free_bundle_closed (index : Nat)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : RustM (Option Pqxdh.Bytes) × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (bytes : Pqxdh.Bytes) (returned : result.1=.ok (some bytes))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index).run before)) :
    Closed index result.2.1.beacons := by
  have same : (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index).run before =
      Prod.map RegistrationNativePlatformIdentityNativeBundle.reply id <$>
        (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
          (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer)).run before := StateT.run_map _ _ _
  rw [same,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  obtain ⟨raw,possible,valueEq,ownersEq⟩ := beacon_supported setup checks representation created _ before inner called
  change RegistrationNativePlatformIdentityNativeBundle.reply inner.1=.ok (some bytes) at returned
  rw [valueEq] at returned
  cases answer : raw.1.1.1 with
  | fail error | div => simp only [RegistrationNativePlatformIdentityNativeBundle.reply,answer] at returned; cases returned
  | ok optional => cases optional with
    | none => simp only [RegistrationNativePlatformIdentityNativeBundle.reply,answer] at returned; cases returned
    | some encoded =>
        have closed := Bundle.bundle_closed setup index writer before.1.beacons _ before.2 encoded raw possible answer
        change Closed index inner.2.1.beacons
        rw [ownersEq]
        exact closed

omit primitives in
/-- An actual pending or terminal CTX owner cannot return another successful bundle at that same position. -/
theorem free_bundle_declines (index : Nat)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : RustM (Option Pqxdh.Bytes) × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (bytes : Pqxdh.Bytes) (closed : Closed index before.1.beacons)
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index).run before)) :
    result.1≠.ok (some bytes) := by
  intro returned
  have same : (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index).run before =
      Prod.map RegistrationNativePlatformIdentityNativeBundle.reply id <$>
        (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
          (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer)).run before := StateT.run_map _ _ _
  rw [same,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  obtain ⟨raw,possible,valueEq,_ownersEq⟩ := beacon_supported setup checks representation created _ before inner called
  change RegistrationNativePlatformIdentityNativeBundle.reply inner.1=.ok (some bytes) at returned
  rw [valueEq] at returned
  cases answer : raw.1.1.1 with
  | fail error | div => simp only [RegistrationNativePlatformIdentityNativeBundle.reply,answer] at returned; cases returned
  | ok optional => cases optional with
    | none => simp only [RegistrationNativePlatformIdentityNativeBundle.reply,answer] at returned; cases returned
    | some encoded => exact Bundle.bundle_declines setup index writer before.1.beacons _ before.2 encoded closed raw possible answer

/-- Every adaptive free source program retains all existing closed owner positions. -/
theorem free_program (work : OracleComp TypedSpec A)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (result : A × (RegistrationNativeIdentityMain.State n KemSK source × Platform))
    (reached : result ∈ support ((simulateQ frontend work).run before)) :
    Keeps before.1.beacons result.2.1.beacons := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at reached
    cases reached
    exact Keeps.refl _
  | query_bind query next ih =>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at reached
    obtain ⟨middle,first,last⟩ := reached
    exact (ih middle.1 middle.2 result last).trans
      (free_handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before middle first)

/-- Closing the real private source retains the same one-use phase policy without an ownership or security premise. -/
theorem handler (query : TypedSpec.Domain)
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : TypedSpec.Range query × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (frontend query)).run before)) :
    Keeps before.1.1.beacons result.2.1.1.beacons := by
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret,StateT.run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  apply free_handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1 inner.1
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

/-- Every real interpreted adaptive program retains the phase policy on all failure and success paths. -/
theorem program (work : OracleComp TypedSpec A)
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : A × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (simulateQ frontend work)).run before)) :
    Keeps before.1.1.beacons result.2.1.1.beacons := by
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret,StateT.run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  apply free_program setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work before.1 inner.1
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called


omit primitives in
/-- The actual closed private source retains the successful bundle's one-use phase without an ownership or initialization premise. -/
theorem source_bundle_closed (index : Nat)
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (bytes : Pqxdh.Bytes) (returned : result.1=.ok (some bytes))
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before)) :
    Closed index result.2.1.1.beacons := by
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret,StateT.run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  apply free_bundle_closed setup checks representation created writer index before.1 inner.1 bytes returned
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

omit primitives in
/-- Real private-source interpretation cannot reopen an already pending or terminal owner for another successful bundle. -/
theorem source_bundle_declines (index : Nat)
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (bytes : Pqxdh.Bytes) (closed : Closed index before.1.1.beacons)
    (reached : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before)) :
    result.1≠.ok (some bytes) := by
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret,StateT.run,support_map] at reached
  obtain ⟨inner,called,rfl⟩ := reached
  apply free_bundle_declines setup checks representation created writer index before.1 inner.1 bytes closed
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Keeps.refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Keeps.refl
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Keeps.trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Keeps.trans
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Keeps.closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Keeps.closed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.current
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Bundle.bundle_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Bundle.bundle_closed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Bundle.bundle_declines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.Bundle.bundle_declines
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.free_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.free_handler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.free_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.free_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.handler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.free_bundle_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.free_bundle_closed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.free_bundle_declines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.free_bundle_declines
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.source_bundle_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.source_bundle_closed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.source_bundle_declines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase.source_bundle_declines
