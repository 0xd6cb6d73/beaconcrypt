-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The same source agreement receipt and literal replay insertion derive live returned-Server material and the exact moved registration token/session slot. Private source values and full caller RNG remain in the source witness. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAgreementPost
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementInterpreter (Capture)
open AdapterPublicServerAgreementReceipt (Receipt Word)
open AdapterPublicServerAgreementRetention (Standard retained project)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}

noncomputable def Returned {R : Type}
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (word : Word R) (native : RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK mlSource) : Prop :=
  AdapterPublicWrapperState.Server view views created credential word.2.1 native.2.server ∧
    match word.1, native.1 with
    | .None, .ok none => True
    | .Some token, .ok (some index) => ∃ consumed,
        AdapterPublicWrapperState.Token token consumed ∧ native.2.server.sessions[index]? = some (some consumed)
    | _, _ => False

variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]

theorem replay {R : Type} (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource) (self : beaconcrypt_public_wrapper.server.Server)
    (before current afterRole : RegistrationNativeExperiment.State n KemSK mlSource)
    (related : AdapterPublicWrapperState.Server view views created credential self afterRole.server)
    (standard : Standard (n := n) (KemSK := KemSK) (mlSource := mlSource) (m := m) views self)
    (receipt : Receipt R) (effect : RustM agreement.AgreementEffect)
    (restored : AdapterPublicAgreementNativeWorldInterpreter.restore view before (receipt, current) = .ok (effect, afterRole)) :
    ∃ result : RustM (Word R), AdapterPublicServerAgreementReceipt.replay (n := n) (KemSK := KemSK) (source := mlSource) (m := m) self receipt = pure result ∧
      match result with
      | .ok word => Returned view views created credential word (retained effect afterRole)
      | _ => True := by
  cases receipt with
  | fail error =>
    change RustM.fail error = .ok (effect, afterRole) at restored
    cases restored
  | div =>
    change RustM.div = .ok (effect, afterRole) at restored
    cases restored
  | ok pair =>
    rcases pair with ⟨⟨originalEffect, journal⟩, capture⟩
    have same : originalEffect = effect := congrArg Prod.fst (RustM.ok.inj restored)
    cases same
    cases effect with
    | fail error =>
      refine ⟨.fail error, ?_, trivial⟩
      simp only [AdapterPublicServerAgreementReceipt.replay, RustT.run_bind, RustT.run_liftRust, pure_bind]
    | div =>
      refine ⟨.div, ?_, trivial⟩
      simp only [AdapterPublicServerAgreementReceipt.replay, RustT.run_bind, RustT.run_liftRust, pure_bind]
    | ok effect =>
      cases effect <;> try {
        refine ⟨.ok (.None, self, capture.rng), ?_, related, trivial⟩
        simp only [AdapterPublicServerAgreementReceipt.replay, RustT.run_bind, RustT.run_liftRust,
          pure_bind, AdapterPublicServerAcceptBody.record, RustT.run_pure] }
      case ServerComplete completed =>
        rcases standard with ⟨insertion⟩
        obtain ⟨reply, operation, footprint⟩ := insertion completed
        have sourceResult := AdapterPublicServerRetain.source view views created credential self afterRole.server
          capture.rng completed reply related operation footprint
        refine ⟨.ok (AdapterPublicServerToken.result self capture.rng completed reply.1 reply.2), ?_, ?_⟩
        · simp only [AdapterPublicServerAgreementReceipt.replay, RustT.run_bind, RustT.run_liftRust,
            pure_bind, sourceResult.1, RustT.run_pure]
        · refine ⟨sourceResult.2, ?_⟩
          have token := AdapterPublicServerRetain.token self capture.rng afterRole.server completed reply
            (AdapterPublicServerRetain.inserted_flag views self afterRole.server completed reply related.replay footprint)
          cases returned : (AdapterPublicServerToken.result self capture.rng completed reply.1 reply.2).1 <;>
            cases slot : AdapterPublicServerRetain.handle afterRole.server completed <;>
            simp only [retained, returned, slot] at token ⊢
          exact ⟨⟨completed⟩, token⟩


variable [original : CryptoOperations (RustT ProbComp)]

theorem program {PlatformState R E : Type}
    (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E) (keys : AdapterPublicAgreementFields.Keys)
    (self : beaconcrypt_public_wrapper.server.Server)
    (work : OracleComp Spec (RustM agreement.AgreementEffect)) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource)
    [ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (standard : Standard (n := n) (KemSK := KemSK) (mlSource := mlSource) (m := StateT PlatformState ProbComp) views self)
    (receipt : Receipt R) (word : Word R) (previous next : PlatformState)
    (supported : (((receipt, .ok word), after), next) ∈ support
      (((AdapterPublicServerAgreementReceipt.program coins generator keys self work rng).run before).run previous)) :
    ∃ handle nativeAfter, project view before ((receipt, .ok word), after) = .ok (.ok handle, nativeAfter) ∧
      Returned view views created credential word (.ok handle, nativeAfter) := by
  simp only [AdapterPublicServerAgreementReceipt.program, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨captured, middle⟩, between⟩, called, continued⟩ := supported
  cases captured with
  | fail error | div =>
    simp only [AdapterPublicServerAgreementReceipt.replay, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at continued
    obtain ⟨_, rfl, returned⟩ := continued
    simp only [Prod.mk.injEq, reduceCtorEq, and_false, false_and] at returned
  | ok pair =>
    rcases pair with ⟨⟨effect, journal⟩, capture⟩
    let world := (RegistrationAgreementWorldTrace.restore before.server.world
      (((effect, journal), AdapterPublicAgreementServerWorld.project view capture), middle.server.world.world.1)).2
    let afterRole := { before with server := { before.server with world := world } }
    have restored : AdapterPublicAgreementNativeWorldInterpreter.restore view before
        (.ok ((effect, journal), capture), middle) = .ok (effect, afterRole) := rfl
    have materialAfter := AdapterPublicAgreementNativeSourceFrame.platform_restored_material
      coins generator keys work rng view views created credential self before middle afterRole related
      (.ok ((effect, journal), capture)) previous between called effect restored
    obtain ⟨result, operation, post⟩ := replay view views created credential self before middle afterRole
      materialAfter standard (.ok ((effect, journal), capture)) effect restored
    rw [operation] at continued
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
    obtain ⟨_, rfl, returned⟩ := continued
    rcases Prod.mk.inj returned with ⟨sameNativePair, _sameOuter⟩
    rcases Prod.mk.inj sameNativePair with ⟨sameReceiptWord, sameNative⟩
    rcases Prod.mk.inj sameReceiptWord with ⟨sameReceipt, sameWord⟩
    change after = middle at sameNative
    change .ok word = result at sameWord
    subst receipt
    subst after
    subst result
    have step := AdapterPublicServerAgreementRetention.replay_step view views created credential self
      before middle afterRole materialAfter standard (.ok ((effect, journal), capture)) effect restored
    rw [operation, StateT.run_pure, map_pure] at step
    have ran := congrArg (fun action => action.run between) step
    simp only [StateT.run_pure] at ran
    have valueEq := congrArg support ran
    simp only [support_pure] at valueEq
    have sameValue : (project view before ((.ok ((effect, journal), capture), .ok word), middle), between) =
        (.ok (retained effect afterRole), between) := by
      apply Set.mem_singleton_iff.mp
      rw [← valueEq]
      exact Set.mem_singleton _
    have projection := congrArg Prod.fst sameValue
    cases retainedEq : retained effect afterRole with
    | mk logical nativeAfter =>
      cases logical with
      | fail error | div =>
        unfold Returned at post
        rw [retainedEq] at post
        apply False.elim
        have impossible := post.2
        cases option : word.1 <;> simp only [option] at impossible
      | ok handle =>
        refine ⟨handle, nativeAfter, ?_, ?_⟩
        · simpa only [retainedEq] using projection
        · simpa only [retainedEq] using post


end BeaconcryptCore.Refinement.AdapterPublicServerAgreementPost

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementPost.replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementPost.replay

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementPost.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementPost.program
