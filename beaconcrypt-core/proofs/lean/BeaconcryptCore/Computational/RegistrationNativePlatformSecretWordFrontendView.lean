-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpenMap
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish
/-! Individual local-query and external-coin embeddings retain the complete shared platform state under the checked Word interpreter. These equations connect the corrected callback bodies without a whole frontend correspondence premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView
open RegistrationNativePlatformPublicFrontend (Base)
variable {n : Nat} {KemSK Platform A : Type}

def wordLocal (selected : Bool) : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)
    (StateT Platform (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))) :=
  fun query => StateT.lift (RegistrationNativeSecretWordInterface.liftLocal selected query)

private theorem lifted_program {I : Type} {spec : OracleSpec I} {J : Type} {target : OracleSpec J}
    (implementation : QueryImpl spec (OracleComp target)) (work : OracleComp spec A) :
    simulateQ (fun query => (StateT.lift (implementation query) : StateT Platform (OracleComp target) _)) work =
      StateT.lift (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    funext previous
    simp only [StateT.monad_bind_def, StateT.bind, StateT.lift,
      bind_assoc, pure_bind]

private theorem lift_apply {J : Type} {spec : OracleSpec J} (work : OracleComp spec A) (before : Platform) :
    (StateT.lift work : StateT Platform (OracleComp spec) A) before = (fun value => (value, before)) <$> work :=
  bind_pure_comp _ _

/-- Removing only the new external-coin envelope on a local protocol request yields its literal existing routed query. -/
theorem local_embedding (selected : Bool) :
    RegistrationNativePlatformPublicCoinEmbedding.embed ∘ₛ
      (RegistrationNativePlatformPublicFrontend.embedLocal ∘ₛ RegistrationNativePlatformPublicFrontend.localQuery (n := n) (KemSK := KemSK) selected) =
      RegistrationNativePublicFrontend.liftLocal selected := by
  funext query
  rcases query with message | common | kem
  · rfl
  · rfl
  · simp only [QueryImpl.apply_compose, RegistrationNativePlatformPublicFrontend.localQuery,
      RegistrationNativePublicFrontend.liftLocal, ← QueryImpl.simulateQ_compose]
    congr 1

variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)

def nativeBase {A : Type} (work : Base n KemSK Platform A) :
    StateT Platform (OracleComp (RegistrationNativeSecretWordCheckedFrontend.Spec n KemSK)) A :=
  RegistrationNativePlatformInterpret.state
    (RegistrationNativeSecretWordCheckedFrontend.native source inside candidate input ∘ₛ
      (RegistrationNativePlatformPublicCoinEmbedding.embed ∘ₛ RegistrationNativePlatformPublicFrontend.embedLocal)) work

def wordBase {A : Type}
    (work : StateT Platform (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)) A) :
    StateT Platform (OracleComp (RegistrationNativeSecretWordCheckedFrontend.Spec n KemSK)) A :=
  RegistrationNativePlatformInterpret.state (RegistrationNativeSecretWordCheckedFrontend.implementation source inside candidate input) work

def target (selected : Bool) : QueryImpl (RegistrationNativeSecretWordChecked.Spec n KemSK)
    (StateT Platform (OracleComp (RegistrationNativeSecretWordCheckedFrontend.Spec n KemSK))) :=
  fun query => StateT.lift (RegistrationNativeSecretWordCheckedFrontend.localLift selected query)

/-- The complete native local base interpretation preserves pure and bind, including mutable platform poststates. -/
theorem native_hom : Cslib.IsMonadHom (Base n KemSK Platform)
    (StateT Platform (OracleComp (RegistrationNativeSecretWordCheckedFrontend.Spec n KemSK)))
    (nativeBase source inside candidate input) := RegistrationNativePlatformBuildInterpret.state_hom _

/-- The complete Word base interpretation preserves pure and bind on that same platform state. -/
theorem word_hom : Cslib.IsMonadHom
    (StateT Platform (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)))
    (StateT Platform (OracleComp (RegistrationNativeSecretWordCheckedFrontend.Spec n KemSK)))
    (wordBase source inside candidate input) := RegistrationNativePlatformBuildInterpret.state_hom _

/-- Every actual indexed local source query keeps the same checked global request and complete platform state. -/
theorem native_local (selected : Bool) (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain) :
    nativeBase source inside candidate input (RegistrationNativePlatformPublicFrontend.localHandler selected query) =
      (target (n := n) (KemSK := KemSK) (Platform := Platform) selected ∘ₛ RegistrationNativeSecretWordChecked.native source inside candidate input) query := by
  rw [QueryImpl.apply_compose]
  unfold target
  rw [lifted_program]
  funext previous
  simp only [nativeBase, RegistrationNativePlatformInterpret.state, RegistrationNativePlatformPublicFrontend.localHandler,
    StateT.run_lift, lift_apply, bind_pure_comp, simulateQ_map]
  congr 1
  have embedded := congrArg (simulateQ (RegistrationNativeSecretWordCheckedFrontend.native
    (n := n) (KemSK := KemSK) source inside candidate input)) (congrFun (local_embedding (n := n) (KemSK := KemSK) selected) query)
  simp only [QueryImpl.apply_compose] at embedded
  have original := RegistrationNativeSecretWordCheckedFrontendLift.native_program source inside candidate input selected
    ((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _)
  simp only [simulateQ_spec_query] at original
  simpa only [QueryImpl.simulateQ_compose] using embedded.trans original

/-- Every symbolic local leaf uses that same global interpreter, including selected getter routing. -/
theorem word_local (selected : Bool) (query : (RegistrationNativeSecretWordInterface.LocalSpec n KemSK).Domain) :
    wordBase source inside candidate input (wordLocal selected query) =
      (target (n := n) (KemSK := KemSK) (Platform := Platform) selected ∘ₛ RegistrationNativeSecretWordChecked.implementation source inside candidate input) query := by
  rw [QueryImpl.apply_compose]
  unfold target
  rw [lifted_program]
  funext previous
  simp only [wordBase, RegistrationNativePlatformInterpret.state, wordLocal, StateT.run_lift, lift_apply,
    bind_pure_comp, simulateQ_map]
  congr 1
  simpa only [simulateQ_spec_query] using RegistrationNativeSecretWordCheckedFrontendLift.symbolic_program source inside candidate input selected
    ((RegistrationNativeSecretWordInterface.LocalSpec n KemSK).query query : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) _)

/-- A real shared-state external sampler is forwarded through the same Word environment coin, with its entire poststate retained. -/
theorem platform (work : StateT Platform ProbComp A) :
    nativeBase (n := n) (KemSK := KemSK) source inside candidate input (RegistrationNativePlatformPublicFrontend.platform work) =
      wordBase source inside candidate input (RegistrationNativePlatformSecretWordOrdinary.platform work) := by
  funext previous
  simp only [nativeBase, wordBase, RegistrationNativePlatformInterpret.state,
    RegistrationNativePlatformPublicFrontend.platform, RegistrationNativePlatformSecretWordOrdinary.platform,
    StateT.run, ← QueryImpl.simulateQ_compose]
  apply congrArg (fun implementation => simulateQ implementation (work.run previous))
  funext coin
  simp only [QueryImpl.apply_compose, RegistrationNativePlatformPublicFrontend.localCoin,
    RegistrationNativePlatformPublicFrontend.embedLocal, RegistrationNativePlatformPublicFrontend.publicCoin,
    RegistrationNativePlatformPublicCoinEmbedding.embed, simulateQ_spec_query]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.local_embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.local_embedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.native_hom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.native_hom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.word_hom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.word_hom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.native_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.native_local

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.word_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.word_local

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView.platform
