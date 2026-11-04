-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSampleCoins
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation

/-! Actual native sampling has the same complete source execution in both private interpretations. Only uniform observations can append: the public selection mode, generated rows, canonical/template memos and successful signing history remain unchanged. Native true counters are retained by the literal sample body. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected : Nat) (placeholder : Ed25519Signature)
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "sample(" work ")" => RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
  (RegistrationNativePlatformIdentityProgram.native
    (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
      (source := mlSource) work))

private def close (result : ((A × (RegistrationNativeIdentityMain.State n KemSK mlSource × Platform)) ×
    RegistrationNativeIdentityCensorCompiler.Mode) × RegistrationNativeIdentityCensorSource.State) : A × FullState :=
  (result.1.1.1, ((result.1.1.2, result.1.2), result.2))

private theorem closed (censored : Bool) (work : ProbComp A) (before : FullState) :
    (interpret setup.joint selected placeholder censored (sample(work))).run before =
      close <$> RegistrationNativeIdentityCensorMldsaOutgoingSource.run setup.joint selected placeholder censored
        ((sample(work)).run before.1.1) before.1.2 before.2 := by
  simp only [interpret, StateT.run, RegistrationNativeIdentityCensorMldsaOutgoingSource.run, bind_pure_comp]
  rfl

/-- Actual supplied independent sampling retains the complete same reply and native/private/platform result under real and censored source interpreters. -/
theorem paired (work : ProbComp A) (before : FullState) :
    (interpret setup.joint selected placeholder false (sample(work))).run before =
      (interpret setup.joint selected placeholder true (sample(work))).run before := by
  rw [closed, closed,
    RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_equal setup.joint selected placeholder _
      (RegistrationNativePlatformIdentityCtxSampleCoins.sample setup checks representation created work before.1.1)]

/-- Only uniform transcript observations may append during the literal native sampler; the complete Mode and every other private field are exact. -/
theorem frame (censored : Bool) (work : ProbComp A) (before : FullState) (result : A × FullState)
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored (sample(work))).run before)) :
    RegistrationNativeIdentityCensorMldsaOutgoingSource.stable result.2.1.2 result.2.2 =
      RegistrationNativeIdentityCensorMldsaOutgoingSource.stable before.1.2 before.2 := by
  rw [closed, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_frame setup.joint selected placeholder censored _
    (RegistrationNativePlatformIdentityCtxSampleCoins.sample setup checks representation created work before.1.1)
    before.1.2 before.2 inner reached

/-- Generated rows and the literal successful signing history survive the actual sampler, so fresh source messages stay fresh before the bundled body. -/
theorem history (censored : Bool) (work : ProbComp A) (before : FullState) (result : A × FullState)
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored (sample(work))).run before)) :
    result.2.1.2 = before.1.2 ∧ result.2.2.pool.seeds = before.2.pool.seeds ∧
      ∀ handle, RegistrationNativeIdentityHistory.history handle result.2.2.pool.transcript =
        RegistrationNativeIdentityHistory.history handle before.2.pool.transcript := by
  have same := frame setup checks representation created selected placeholder censored work before result supported
  have mode := congrArg Prod.fst same
  have pool := congrArg (fun value => value.2.pool) same
  change RegistrationNativeIdentityCompiler.poolView result.2.2.pool =
    RegistrationNativeIdentityCompiler.poolView before.2.pool at pool
  refine ⟨mode, ?_, ?_⟩
  · exact congrArg (fun value => value.seeds) pool
  · intro handle
    have actual := congrArg (fun value => RegistrationNativeIdentityHistory.history handle value.transcript) pool
    simpa only [RegistrationNativeIdentityHistoryObservation.pool_view_history] using actual

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource.paired
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource.frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource.history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource.history
