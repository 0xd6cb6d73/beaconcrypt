import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedNative
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun
import BeaconcryptCore.Computational.RegistrationNativePlatformWriterKeyPolicy
/-! Current dynamic Init publication signs only the captured owner fixed prekey, its PQ field or tagged retry one-time keys. The pure indexed policy lifts through the same arbitrary stateful source writer, preserving every P poststate and partial signing history before later failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformIdentityProgram (M native external)
open RegistrationNativePlatformIdentityFixedNative (Fixed At Inv)
variable {n : Nat} {I KemSK Auxiliary Platform E Value Next : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

def Preserves (invariant : RegistrationNativeIdentityFrontend.State source → Prop)
    (work : M n KemSK Auxiliary Platform source Value) : Prop :=
  ∀ owners env previous result, invariant owners → result ∈ support (((work.run owners).run env).run previous) → invariant result.1.1.2

theorem pure_preserves (invariant : RegistrationNativeIdentityFrontend.State source → Prop) (value : Value) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) invariant (pure value) := by
  intro owners env previous result prior supported
  simp only [StateT.run_pure,mem_support_pure_iff] at supported
  cases supported
  exact prior

theorem bind_preserves (invariant : RegistrationNativeIdentityFrontend.State source → Prop)
    (work : M n KemSK Auxiliary Platform source Value) (next : Value → M n KemSK Auxiliary Platform source Next)
    (first : Preserves invariant work) (later : ∀ value, Preserves invariant (next value)) : Preserves invariant (work >>= next) := by
  intro owners env previous result prior supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,reached,continued⟩ := supported
  exact later middle.1.1.1 middle.1.1.2 middle.1.2 middle.2 result (first owners env previous middle prior reached) continued

theorem native_preserves (invariant : RegistrationNativeIdentityFrontend.State source → Prop)
    (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (law : RegistrationNativePlatformIdentityFixedNative.Preserves invariant work) : Preserves (Platform := Platform) invariant (native work) := by
  intro owners env previous result prior supported
  simp only [native,StateT.run,support_map] at supported
  obtain ⟨inner,reached,equal⟩ := supported
  cases equal
  exact law owners env inner prior (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached)

theorem external_preserves (invariant : RegistrationNativeIdentityFrontend.State source → Prop) (work : StateT Platform ProbComp Value) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) invariant (external work) := by
  intro owners env previous result prior supported
  simp only [external,StateT.run,support_map] at supported
  obtain ⟨inner,_reached,equal⟩ := supported
  cases equal
  exact prior

private theorem allowed (prekey : PqxdhEd25519EufCma.X25519PublicKey) (pq : MlKem768PublicKey) (query : RegistrationBeaconInitExecutor.Spec.Domain)
    (good : RegistrationNativePlatformWriterKeyPolicy.AllowedQuery (E := E) prekey pq (.inl query)) :
    RegistrationNativeEdSigningBounds.AllowedQuery prekey query := by
  cases query with
  | inl query => trivial
  | inr request =>
    rcases good with first | second | third
    · exact Or.inl first
    · exact Or.inr (Or.inl ⟨pq,second⟩)
    · exact Or.inr (Or.inr third)

theorem query_preserves (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformWriter.Spec E).Domain)
    (good : RegistrationNativePlatformWriterKeyPolicy.AllowedQuery (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.kemPublic query) :
    Preserves (n := n) (Auxiliary := Auxiliary) (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic))
      (RegistrationNativePlatformIdentityPublication.callback setup index owner writer query) := by
  cases query with
  | inl query => exact native_preserves _ _ (RegistrationNativePlatformIdentityFixedNative.outgoing_preserves setup source index owner query (allowed _ _ query good))
  | inr query => exact external_preserves _ (writer query)

theorem program_preserves {Index : Type} {spec : OracleSpec Index} (invariant : RegistrationNativeIdentityFrontend.State source → Prop)
    (implementation : QueryImpl spec (M n KemSK Auxiliary Platform source)) (allowed : Index → Prop)
    (step : ∀ query, allowed query → Preserves invariant (implementation query))
    (work : OracleComp spec Value) (bounded : work.AllQueriesSatisfy allowed) : Preserves invariant (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_preserves invariant value
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at bounded
    rw [simulateQ_bind,simulateQ_spec_query]
    exact bind_preserves invariant _ _ (step query bounded.1) (fun reply => ih reply (bounded.2 reply))

private theorem publication_preserves (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (n := n) (Auxiliary := Auxiliary) (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic))
      (simulateQ (RegistrationNativePlatformIdentityPublication.callback setup index owner writer)
        (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)) := by
  apply program_preserves _ _ (RegistrationNativePlatformWriterKeyPolicy.AllowedQuery _ _)
    (query_preserves setup index owner writer)
  apply RegistrationNativePlatformWriterKeyPolicy.begin_all (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.kemPublic
    ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin (setup.dh.publicKey oneTime)
  · rfl
  · exact PqxdhRootTableInitialization.rootArray_bytes _
  · simp [RegistrationNativeIdentityFrontend.inputs,RegistrationNativeBeaconFrontend.pqArray,PqxdhRefinement.absBytes,List.map_map,Function.comp_def]

private theorem next_preserves (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RegistrationNativePlatformIdentityBundle.Reply) :
    Preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic))
      (RegistrationNativePlatformIdentityBundle.next index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact pure_preserves _ _
  | ok result => cases result with
    | Err error => exact pure_preserves _ _
    | Ok published =>
      exact bind_preserves _ _ _
        (native_preserves _ _ (RegistrationNativePlatformIdentityFixedNative.phase_preserves index _ _))
        (fun _ => bind_preserves _ _ _ (native_preserves _ _ (RegistrationNativePlatformIdentityFixedNative.lift_preserves _ _)) (fun _ => pure_preserves _ _))

private theorem bundled_preserves (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (n := n) (Auxiliary := Auxiliary) (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic))
      (RegistrationNativePlatformIdentityBundle.bundled setup index owner oneTime writer) :=
  bind_preserves _ _ _ (publication_preserves setup index owner oneTime writer) (next_preserves index owner oneTime)

private theorem start_preserves (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (n := n) (Auxiliary := Auxiliary) (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic))
      (RegistrationNativePlatformIdentityBundleRun.start setup index owner writer) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start,phase]
    exact bind_preserves _ _ _ (native_preserves _ _ (RegistrationNativePlatformIdentityFixedNative.sample_preserves _ _))
      (fun oneTime => bundled_preserves setup index owner oneTime writer)
  | freshWithCoins oneTime =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start,phase,pure_bind] using bundled_preserves setup index owner oneTime writer
  | initSent pending oneTime | established completed | aborted aborted =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start,phase] using
      (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic))
        (.ok none : RustM (Option (alloc.vec.Vec U8))))

/-- Full current common-P Init publication keeps each indexed owner's fixed-prekey signing history, including failed source writers after successful Ed calls. -/
theorem bundle_fixed (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (n := n) (Auxiliary := Auxiliary) (source := source) Fixed (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer) := by
  intro owners env previous result prior supported
  simp only [RegistrationNativePlatformIdentityBundleRun.bundle,StateT.run_bind,StateT.run_get,pure_bind] at supported
  cases found : owners[index]? with
  | none =>
    simp only [found,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact prior
  | some owner =>
    simp only [found] at supported
    have initial : Inv index (PqxdhPhase2InputBytes.word owner.prekeyPublic) owners := by
      refine ⟨?_,prior⟩
      intro current located
      cases Option.some.inj (located.symm.trans found)
      rfl
    exact (start_preserves setup index owner writer owners env previous result initial supported).2
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.pure_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.pure_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.bind_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.bind_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.native_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.native_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.external_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.external_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.query_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.query_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.program_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.program_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.bundle_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedCore.bundle_fixed
