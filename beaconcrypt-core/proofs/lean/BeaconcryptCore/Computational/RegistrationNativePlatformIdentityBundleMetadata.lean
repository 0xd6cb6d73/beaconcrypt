-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata

/-! The literal effectful opaque-Ed bundle preserves the credential handle/public identity and fixed prekey/PQ fields at every owner index. The proof is structural for all trusted and platform replies, including failed signing/allocation, and introduces no source ownership or security premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeIdentityMetadata (keys)
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
theorem pure_preserves (value : Value) : Preserves (pure value : M n KemSK Auxiliary Platform source Value) := by
  intro current env previous result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

theorem get_preserves : Preserves (get : M n KemSK Auxiliary Platform source (RegistrationNativeIdentityFrontend.State source)) := by
  intro current env previous result supported
  simp only [StateT.run_get, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

/-- Complete adaptive continuation preserves metadata only after the actual reached first operation. -/
theorem bind_preserves (work : M n KemSK Auxiliary Platform source Value) (next : Value → M n KemSK Auxiliary Platform source Next)
    (first : Preserves work) (later : ∀ value, Preserves (next value)) : Preserves (work >>= next) := by
  intro current env previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (later middle.1.1.1 middle.1.1.2 middle.1.2 middle.2 result continued).trans (first current env previous middle reached)

/-- Existing all-reply metadata preservation lifts through the native request branch without changing P. -/
theorem native_preserves (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source Value)
    (preserves : RegistrationNativeIdentityMetadata.Preserves work) :
    Preserves (RegistrationNativePlatformIdentityProgram.native (Platform := Platform) work) := by
  intro current env previous result supported
  simp only [RegistrationNativePlatformIdentityProgram.native, StateT.run, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  cases returned
  exact preserves current env inner (support_simulate_subset _ _ reached)

/-- The actual stateful serializer has no access to owner metadata, including all failed prefixes. -/
theorem external_preserves (work : StateT Platform ProbComp Value) :
    Preserves (RegistrationNativePlatformIdentityProgram.external (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) := by
  intro current env previous result supported
  simp only [RegistrationNativePlatformIdentityProgram.external, StateT.run, support_map] at supported
  obtain ⟨inner, _reached, returned⟩ := supported
  cases returned
  rfl

theorem simulate_preserves {κ : Type} {spec : OracleSpec κ}
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
        (native_preserves _ (RegistrationNativeIdentityMetadata.phase_preserves index _))
        (fun _ => bind_preserves _ _ (native_preserves _ (RegistrationNativeIdentityMetadata.lift_preserves _)) (fun _ => pure_preserves _))

private theorem bundled_preserves (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := Auxiliary) setup index owner oneTime writer) := by
  apply bind_preserves _ _ (simulate_preserves _ ?_ _)
  · exact next_preserves index owner oneTime
  · intro request
    cases request with
    | inl request => exact native_preserves _ (RegistrationNativeIdentityMetadata.outgoing_preserves setup index owner request)
    | inr request => exact external_preserves _

private theorem start_preserves (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (RegistrationNativePlatformIdentityBundleRun.start (n := n) (Auxiliary := Auxiliary) setup index owner writer) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
    exact bind_preserves _ _ (native_preserves _ (RegistrationNativeIdentityMetadata.sample_preserves _))
      (fun scalar => bundled_preserves setup index owner scalar writer)
  | freshWithCoins scalar =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind] using bundled_preserves setup index owner scalar writer
  | initSent pending scalar | established completed | aborted previous =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase] using
      (pure_preserves (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) (.ok none : RustM (Option (alloc.vec.Vec U8))))

/-- Complete actual stateful bundle lookup and all optional writer results retain the actual immutable credential roster. -/
theorem bundle_preserves (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Preserves (RegistrationNativePlatformIdentityBundleRun.bundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer) := by
  apply bind_preserves _ _ get_preserves
  intro current
  cases current[index]? with
  | none => exact pure_preserves _
  | some owner => exact start_preserves setup index owner writer

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.pure_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.pure_preserves
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.get_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.get_preserves
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.bind_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.bind_preserves
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.native_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.native_preserves
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.external_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.external_preserves
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.simulate_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.simulate_preserves
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.bundle_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata.bundle_preserves
