-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix
/-! Concrete source leaf instantiation for the actual post-agreement Beacon suffix. Material addresses are evaluated before the same selective demand; hidden, known and refused choices and every stateful World continuation remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World Symbolic frame)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolicProvider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "actualProvider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate
local notation "symbolic" => RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused symbolicProvider
local notation "actual" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate actualProvider
local notation "wordLocal" => symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false
local notation "nativeLocal" => wordLocal ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate
local notation "actualLocal" => actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false

local notation "reified" => RegistrationNativePlatformLorCtxRealization.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge

variable {Platform A : Type}
open RegistrationNativePlatformLorIdealStateLift (interpret)
abbrev NativeState (n : Nat) (KemSK : Type) :=
  RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase
noncomputable def nativeBase : QueryImpl (RegistrationNativePlatformPublicFrontend.LocalSpec n KemSK) (StateT (NativeState n KemSK) (World n)) :=
  actual ∘ₛ (RegistrationNativePlatformPublicCoinEmbedding.embed ∘ₛ RegistrationNativePlatformPublicFrontend.embedLocal)
noncomputable def native (routed : Bool) : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
    (StateT (Platform × NativeState n KemSK) (World n)) := fun query =>
  interpret (nativeBase setup wire sign seed scalar candidate selected pairs publicKey challenge)
    (RegistrationNativePlatformPublicFrontend.localHandler routed query)
noncomputable def word (routed : Bool) : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)
    (StateT (Platform × Symbolic n KemSK) (World n)) := fun query =>
  interpret symbolic (RegistrationNativePlatformSecretWordFrontendView.wordLocal routed query)

theorem word_program (routed : Bool) (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) A)
    (previous : Platform) (before : Symbolic n KemSK) :
    (simulateQ (word setup wire sign seed scalar candidate unused selected pairs publicKey challenge routed) work).run (previous,before) =
      (fun result => (result.1,(previous,result.2))) <$>
        (simulateQ symbolic (simulateQ (RegistrationNativeSecretWordInterface.liftLocal routed) work)).run before := by
  unfold word
  rw [←RegistrationNativePlatformLorIdealStateLift.simulate,RegistrationNativePlatformLorIdealStateLift.run]
  have threaded : (simulateQ (RegistrationNativePlatformSecretWordFrontendView.wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) routed) work).run previous =
      (fun value => (value,previous)) <$> simulateQ (RegistrationNativeSecretWordInterface.liftLocal routed) work :=
    RegistrationNativePlatformLorIdealStateLift.thread (RegistrationNativeSecretWordInterface.liftLocal routed) work previous
  rw [threaded]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map]

theorem native_program (routed : Bool) (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A)
    (previous : Platform) (before : NativeState n KemSK) :
    (simulateQ (native (n := n) (Platform := Platform) setup wire sign seed scalar candidate selected pairs publicKey challenge routed) work).run (previous,before) =
      (fun result => (result.1,(previous,result.2))) <$>
        (simulateQ actual (simulateQ (RegistrationNativePublicFrontend.liftLocal routed) work)).run before := by
  unfold native
  rw [←RegistrationNativePlatformLorIdealStateLift.simulate,RegistrationNativePlatformLorIdealStateLift.run]
  have threaded : (simulateQ (RegistrationNativePlatformPublicFrontend.localHandler (n := n) (KemSK := KemSK) (Platform := Platform) routed) work).run previous =
      (fun value => (value,previous)) <$> simulateQ (RegistrationNativePlatformPublicFrontend.localQuery routed) work :=
    RegistrationNativePlatformLorIdealStateLift.thread (RegistrationNativePlatformPublicFrontend.localQuery routed) work previous
  rw [threaded]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map,nativeBase,QueryImpl.simulateQ_compose]
  rw [←QueryImpl.simulateQ_compose RegistrationNativePlatformPublicFrontend.embedLocal (RegistrationNativePlatformPublicFrontend.localQuery routed),
    ←QueryImpl.simulateQ_compose RegistrationNativePlatformPublicCoinEmbedding.embed,
    RegistrationNativePlatformSecretWordFrontendView.local_embedding]

def project : Platform × Symbolic n KemSK → Platform × NativeState n KemSK := Prod.map id (frame candidate)

theorem native_leaf (routed : Bool) (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain)
    (before : Platform × Symbolic n KemSK) :
    Prod.map id (project candidate) <$>
      (simulateQ (word setup wire sign seed scalar candidate unused selected pairs publicKey challenge routed)
        (RegistrationNativeSecretWordServerSource.realize candidate query)).run before =
      ((native (Platform := Platform) setup wire sign seed scalar candidate selected pairs publicKey challenge routed) query).run (project candidate before) := by
  rcases before with ⟨previous,before⟩
  rw [word_program]
  have threaded := native_program (n := n) (Platform := Platform) setup wire sign seed scalar candidate selected pairs publicKey challenge routed
    (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) previous (frame candidate before)
  simp only [simulateQ_spec_query] at threaded
  change _ = ((native setup wire sign seed scalar candidate selected pairs publicKey challenge routed) query).run (previous,frame candidate before)
  rw [threaded]
  have sourceEq := RegistrationNativePlatformLorCtxRealization.local_program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge routed
    (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) before
  have lifted := congrArg (Functor.map (fun result => (result.1,(previous,result.2)))) sourceEq
  simpa only [simulateQ_spec_query,QueryImpl.simulateQ_compose,QueryImpl.apply_compose,Functor.map_map,project,Prod.map_def,id_eq] using lifted

theorem prepare (routed : Bool) (message : RegistrationNativeSecretWordMessage.Message)
    (before : Platform × Symbolic n KemSK) :
    Prod.map (Option.map (RegistrationNativeSecretWordMessage.eval candidate)) (project candidate) <$>
      (simulateQ (word setup wire sign seed scalar candidate unused selected pairs publicKey challenge routed)
        (RegistrationNativeSecretWordInterface.prepare message)).run before =
      (simulateQ (native (Platform := Platform) setup wire sign seed scalar candidate selected pairs publicKey challenge routed)
        (RegistrationBeaconReferenceCompiler.prepare (RegistrationNativeSecretWordMessage.eval candidate message))).run (project candidate before) := by
  rcases before with ⟨previous,before⟩
  rw [word_program,native_program]
  have sourceEq := RegistrationNativePlatformLorCtxLeaves.prepare_source setup wire sign seed scalar candidate unused symbolicProvider actualProvider message before
  have lifted := congrArg (Functor.map (fun result => (result.1,(previous,result.2)))) sourceEq
  simpa only [RegistrationNativeSecretWordInterface.prepare,RegistrationBeaconReferenceCompiler.prepare,
    simulateQ_spec_query,RegistrationNativeSecretWordInterface.liftLocal,RegistrationNativePublicFrontend.liftLocal,
    Functor.map_map,project,Prod.map_def,id_eq] using lifted

theorem leaves (routed : Bool) : RegistrationNativePlatformLorIdealAcceptCore.Leaves candidate
    (native (Platform := Platform) setup wire sign seed scalar candidate selected pairs publicKey challenge routed)
    (word setup wire sign seed scalar candidate unused selected pairs publicKey challenge routed) (project candidate) :=
  ⟨native_leaf setup wire sign seed scalar candidate unused selected pairs publicKey challenge routed,
    prepare setup wire sign seed scalar candidate unused selected pairs publicKey challenge routed⟩

noncomputable def wordReserve (reserve : StateT Platform ProbComp Bool) : StateT (Platform × Symbolic n KemSK) (World n) Bool :=
  interpret symbolic (RegistrationNativePlatformSecretWordOrdinary.platform reserve)
noncomputable def nativeReserve (reserve : StateT Platform ProbComp Bool) : StateT (Platform × NativeState n KemSK) (World n) Bool :=
  interpret (nativeBase setup wire sign seed scalar candidate selected pairs publicKey challenge) (RegistrationNativePlatformPublicFrontend.platform reserve)

theorem reserve_source (reserve : StateT Platform ProbComp Bool) (before : Platform × Symbolic n KemSK) :
    Prod.map id (project candidate) <$>
      (wordReserve setup wire sign seed scalar candidate unused selected pairs publicKey challenge reserve).run before =
      (nativeReserve (n := n) setup wire sign seed scalar candidate selected pairs publicKey challenge reserve).run (project candidate before) := by
  rcases before with ⟨previous,before⟩
  have coinSource : ∀ (coin : unifSpec.Domain) (current : Symbolic n KemSK),
      Prod.map id (frame candidate) <$>
        (simulateQ symbolic (RegistrationNativeSecretWordFrontend.effect (.inl coin))).run current =
        (simulateQ (nativeBase setup wire sign seed scalar candidate selected pairs publicKey challenge)
          (RegistrationNativePlatformPublicFrontend.localCoin coin)).run (frame candidate current) := by
    intro coin current
    have same := RegistrationNativePlatformLorCtxLeaves.effect_query_source setup wire sign seed scalar candidate unused symbolicProvider actualProvider (.inl coin) current
    simpa only [RegistrationNativeSecretWordFrontend.effect,RegistrationNativePlatformPublicFrontend.localCoin,
      simulateQ_spec_query,nativeBase,QueryImpl.apply_compose,RegistrationNativePlatformPublicCoinEmbedding.embed,
      RegistrationNativePlatformPublicFrontend.embedLocal,RegistrationNativePlatformPublicFrontend.publicCoin,
      RegistrationNativePublicFrontend.effect,RegistrationNativePublicFrontend.liftLocal] using same
  have sampled := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun coin => simulateQ symbolic (RegistrationNativeSecretWordFrontend.effect (.inl coin)))
    (fun coin => simulateQ (nativeBase setup wire sign seed scalar candidate selected pairs publicKey challenge)
      (RegistrationNativePlatformPublicFrontend.localCoin coin)) (frame candidate) coinSource (reserve.run previous) before
  change Prod.map id (frame candidate) <$>
      (simulateQ (symbolic ∘ₛ (fun coin => RegistrationNativeSecretWordFrontend.effect (.inl coin))) (reserve.run previous)).run before =
      (simulateQ (nativeBase setup wire sign seed scalar candidate selected pairs publicKey challenge ∘ₛ
        RegistrationNativePlatformPublicFrontend.localCoin) (reserve.run previous)).run (frame candidate before) at sampled
  simp only [QueryImpl.simulateQ_compose] at sampled
  have lifted := congrArg (Functor.map (fun result => (result.1.1,(result.1.2,result.2)))) sampled
  simp only [wordReserve,nativeReserve,project,Prod.map_apply,id_eq]
  rw [RegistrationNativePlatformLorIdealStateLift.run,RegistrationNativePlatformLorIdealStateLift.run]
  simp only [StateT.run,RegistrationNativePlatformSecretWordOrdinary.platform,RegistrationNativePlatformPublicFrontend.platform]
  simp only [StateT.run,Functor.map_map,Prod.map_def,id_eq] at lifted ⊢
  convert lifted using 1

theorem accept_source (checks : PqxdhServerAuthExperiment.Checks) (reserve : StateT Platform ProbComp Bool)
    (routed : Bool) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (server : RegistrationNativeSecretWordMessage.ServerState) (env : RegistrationServerReferenceCompiler.Environment)
    (previous : Platform) (before : Symbolic n KemSK) :
    (fun result => (((((result.1.1.1.1,result.1.1.1.2.eval candidate),result.1.1.2),result.1.2)),frame candidate result.2)) <$>
      (simulateQ symbolic
        ((((RegistrationNativePlatformSecretWordOpen.accept
          (RegistrationNativePlatformSecretWordFrontendView.wordLocal routed)
          (RegistrationNativePlatformSecretWordOrdinary.platform reserve) setup checks verify packet).run server).run env).run previous)).run before =
      (simulateQ (nativeBase setup wire sign seed scalar candidate selected pairs publicKey challenge)
        ((((RegistrationNativePlatformServerOpenControl.accept
          (RegistrationNativePlatformPublicFrontend.localHandler routed)
          (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet).run (server.eval candidate)).run env).run previous)).run (frame candidate before) := by
  have core := RegistrationNativePlatformLorIdealAccept.accept_source candidate
    (native (Platform := Platform) setup wire sign seed scalar candidate selected pairs publicKey challenge routed)
    (word setup wire sign seed scalar candidate unused selected pairs publicKey challenge routed) (project candidate)
    (leaves setup wire sign seed scalar candidate unused selected pairs publicKey challenge routed) setup checks
    (nativeReserve setup wire sign seed scalar candidate selected pairs publicKey challenge reserve)
    (wordReserve setup wire sign seed scalar candidate unused selected pairs publicKey challenge reserve)
    (reserve_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge reserve)
    verify packet server env (previous,before)
  have wordNatural := RegistrationNativePlatformSecretWordOpenMap.accept
    (RegistrationNativePlatformLorIdealStateLift.hom (P := Platform) symbolic)
    (RegistrationNativePlatformSecretWordFrontendView.wordLocal routed)
    (RegistrationNativePlatformSecretWordOrdinary.platform reserve) setup checks verify packet server env
  have nativeNatural := RegistrationNativePlatformSecretWordOpenMap.native_accept (n := n)
    (RegistrationNativePlatformLorIdealStateLift.hom (P := Platform) (nativeBase (n := n) setup wire sign seed scalar candidate selected pairs publicKey challenge))
    (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks
    (RegistrationNativePlatformPublicFrontend.localHandler routed) verify packet (server.eval candidate) env
  change _ = _ at core
  change interpret symbolic _ = _ at wordNatural
  change interpret (nativeBase setup wire sign seed scalar candidate selected pairs publicKey challenge) _ = _ at nativeNatural
  unfold word wordReserve at core
  rw [←wordNatural] at core
  unfold native nativeReserve at core
  rw [←nativeNatural] at core
  have restored := congrArg (Functor.map (fun result => ((result.1,result.2.1),result.2.2))) core
  simp only [RegistrationNativePlatformLorIdealStateLift.run,Functor.map_map,project,Prod.map_def,id_eq] at restored
  simpa only [Functor.map_map,id_map'] using restored
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.word_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.word_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.native_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.native_leaf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.prepare

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.leaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.reserve_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.reserve_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptLift.accept_source
