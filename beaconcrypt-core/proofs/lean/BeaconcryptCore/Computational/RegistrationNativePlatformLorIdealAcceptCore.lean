-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource
/-! Free Server collector and root preparation correspondence under separate persistent states. The only contracts are individual interpreted queries and evaluated preparation replies; the source agreement and complete private-state relation are derived. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady Message)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {I KemSK NativePrivate WordPrivate A : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

structure Leaves (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (native : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT NativePrivate m))
    (symbolic : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT WordPrivate m))
    (frame : WordPrivate → NativePrivate) : Prop where
  native_leaf : ∀ query before, Prod.map id frame <$>
    (simulateQ symbolic (RegistrationNativeSecretWordServerSource.realize candidate query)).run before =
      (native query).run (frame before)
  prepare : ∀ message before, Prod.map (Option.map (RegistrationNativeSecretWordMessage.eval candidate)) frame <$>
    (simulateQ symbolic (RegistrationNativeSecretWordInterface.prepare message)).run before =
      (simulateQ native (RegistrationBeaconReferenceCompiler.prepare (RegistrationNativeSecretWordMessage.eval candidate message))).run (frame before)

variable (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (native : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT NativePrivate m))
    (symbolic : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT WordPrivate m))
    (frame : WordPrivate → NativePrivate) (leaves : Leaves candidate native symbolic frame)

include leaves

theorem effects_program (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) (before : WordPrivate) :
    Prod.map id frame <$> (simulateQ (RegistrationNativePlatformSecretWordOpen.effects symbolic) work).run before =
      (simulateQ (RegistrationNativePlatformServerOpenControl.effects native) work).run (frame before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ frame _ work before
  intro query state
  have leaf := leaves.native_leaf (.inr (.inl (.inr (.inr query)))) state
  simpa only [RegistrationNativePlatformSecretWordOpen.effects,RegistrationNativePlatformServerOpenControl.effects,
    QueryImpl.compose,RegistrationBeaconReferenceCompiler.effect,RegistrationNativeSecretWordInterface.effect,
    RegistrationNativeSecretWordServerSource.realize,RegistrationNativeSecretWordInterface.common,simulateQ_spec_query] using leaf

theorem collect_source (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (env : Environment) (before : WordPrivate) :
    Prod.map (Prod.map (Option.map (RegistrationNativeSecretWordServerCollect.eval candidate)) id) frame <$>
      (simulateQ symbolic ((RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated).run env)).run before =
      (simulateQ native ((RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated).run env)).run (frame before) := by
  have lifted := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (symbolic ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate) native frame
    leaves.native_leaf ((RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated).run env) before
  have syntaxLaw := congrArg (fun work => (simulateQ symbolic work).run before)
    (RegistrationNativeSecretWordServerSource.collector_source setup checks candidate packet authenticated env)
  simp only [←QueryImpl.simulateQ_compose,simulateQ_map,StateT.run_map] at syntaxLaw
  rw [syntaxLaw] at lifted
  simpa only [Functor.map_map,Prod.map_def,id_eq] using lifted

theorem root_source (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (before : WordPrivate) :
    Prod.map (RegistrationNativeSecretWordServerRoot.restore candidate) frame <$>
      (simulateQ symbolic (simulateQ RegistrationNativeSecretWordInterface.prepare
        (RegistrationNativeSecretWordServerRoot.client binding collected))).run before =
      (simulateQ native (simulateQ RegistrationBeaconReferenceCompiler.prepare
        (RegistrationServerReferenceRoot.client binding (RegistrationNativeSecretWordServerCollect.eval candidate collected)))).run (frame before) := by
  classical
  simp only [RegistrationNativeSecretWordServerRoot.client,RegistrationServerReferenceRoot.client,
    RegistrationNativeSecretWordServerRoot.nonzero_eval]
  split
  · simp only [simulateQ_pure,StateT.run_pure,map_pure,RegistrationNativeSecretWordServerRoot.restore,Option.map_none,Prod.map_def]
  · simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_pure,StateT.run_bind,StateT.run_pure,map_bind]
    rw [←RegistrationNativeSecretWordServerRoot.message_eval candidate collected]
    rw [←leaves.prepare (RegistrationNativeSecretWordServerRoot.message collected) before,bind_map_left]
    simp only [map_pure]
    apply bind_congr
    rintro ⟨reference,after⟩
    cases reference <;> rfl

theorem agreement_source (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (server : ServerState) (env : Environment) (before : WordPrivate) :
    Prod.map (fun result => ((RegistrationNativeSecretWordServerRoot.restore candidate result.1.1,result.1.2.eval candidate),result.2)) frame <$>
      ((((RegistrationNativePlatformSecretWordOpen.agreement symbolic setup checks packet authenticated).run server).run env).run before) =
      ((((RegistrationNativePlatformServerOpenKernel.agreement native setup checks packet authenticated).run (server.eval candidate)).run env).run (frame before)) := by
  change Prod.map (fun result => ((RegistrationNativeSecretWordServerRoot.restore candidate result.1.1,result.1.2.eval candidate),result.2)) frame <$>
    (simulateQ symbolic (((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run server).run env)).run before =
    (simulateQ native (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run (server.eval candidate)).run env)).run (frame before)
  simp only [RegistrationServerOpenReferenceCompiler.agreement,
    RegistrationNativeSecretWordServerCompiler.agreement,StateT.run_bind,StateT.run_lift,
    simulateQ_bind,StateT.run_bind,map_bind]
  have collected := collect_source candidate native symbolic frame leaves setup checks packet authenticated env before
  rw [←collected,bind_map_left]
  simp only [StateT.run_pure,simulateQ_pure,pure_bind,bind_assoc]
  apply bind_congr
  rintro ⟨⟨collected,envAfter⟩,after⟩
  cases collected with
  | none =>
    simp only [Prod.map_apply,id_eq,Option.map_none,StateT.run_pure,simulateQ_pure,map_pure,
      RegistrationNativeSecretWordServerRoot.restore]
  | some input =>
    simp only [Prod.map_apply,id_eq,Option.map_some,StateT.run_lift,bind_pure_comp,simulateQ_map,
      StateT.run_map,Functor.map_map]
    have rooted := root_source candidate native symbolic frame leaves authenticated.binding input after
    have lifted := congrArg (Functor.map (fun result => (((result.1,server.eval candidate),envAfter),result.2))) rooted
    simpa only [Functor.map_map,Prod.map_def,id_eq] using lifted

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore.effects_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore.effects_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore.collect_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore.root_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore.agreement_source
