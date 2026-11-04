-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorInitialized
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The source initializer executes the actual checked caller-RNG constructor and actual Server authentication_pin continuation. The receipt retains even constructor errors and the same returned source Self/RNG. Native initialization is its proved projection, with no caller startup/profile equation. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorRunner
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open BeaconcryptCore.Computational
variable {n : Nat} {I KemSK R Error : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [AdapterServerConstructorPrimitive.Standard]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations
  (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [localOps : LocalOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [crypto : CryptoOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [children : ChildOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
local notation "World"  =>  PqxdhRecordLiftWorld.State n
local notation "M"  =>  StateT World ProbComp

structure Receipt (n : Nat) (KemSK R : Type) (mlSource : RegistrationNativeMldsa.Source) where
  constructor : RustM (AdapterServerConstructorBody.Outcome R)
  ready : Option (AdapterServerConstructorInitialized.Ready n KemSK R mlSource)

def nativeView (receipt : Receipt n KemSK R mlSource) : Option (RegistrationNativeExperiment.Initial n KemSK mlSource) :=
  receipt.ready.map AdapterServerConstructorInitialized.Ready.initial

noncomputable def run (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : MaterialView mlSource KemSK) (identityIndex : Nat) (identifier : U64)
    (generator : rand_core.TryCryptoRng R Error) (rng : R) : M (Receipt n KemSK R mlSource) := do
  let called←(beaconcrypt_server_constructor_request.server.Server.try_new_with_rng (m:=RustT M)
    generator identifier .None .None rng).run
  match called with
  | .ok (.Ok self,nextRng) => do
    let ready←AdapterServerConstructorInitialized.finish setup view identityIndex identifier self nextRng
    pure ⟨called,ready⟩
  | _ => pure ⟨called,none⟩

noncomputable def game (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : MaterialView mlSource KemSK) (identityIndex : Nat) (identifier : U64)
    (generator : rand_core.TryCryptoRng R Error) (rng : R) : ProbComp (Receipt n KemSK R mlSource) :=
  Prod.fst <$> (run setup view identityIndex identifier generator rng).run PqxdhRecordLiftWorld.initial

variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (generator : rand_core.TryCryptoRng R Error) (view : MaterialView mlSource KemSK)
variable (views : Views) (objects : AdapterServerConstructorObjects.Leaves views)
variable (ensureInit : StateT Unit ProbComp Bool)
local notation "edSample"  =>  PqxdhRecordLiftWorld.sampled (n:=n) (AdapterServerConstructorStartup.edCore ensureInit)
local notation "mlSample"  =>  PqxdhRecordLiftWorld.sampled (n:=n) (RegistrationNativeMldsa.generate mlSource)
variable (ed : AdapterServerConstructorJoint.EdContract generator view setup.joint
  (PqxdhRecordLiftWorld.sampled (n:=n) (AdapterServerConstructorStartup.edCore ensureInit)))
variable (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view
  (PqxdhRecordLiftWorld.sampled (n:=n) (RegistrationNativeMldsa.generate mlSource)))
variable (edGetter : ∀key,(crypto.edPublicBytes key).run=pure (.ok (view.edPublic key)))
variable (mlGetter : ∀identity,(localOps.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey))
variable (hashLeaf : ∀request,(children.executeHash request).run=RegistrationNativeServerPinRecompute.nativeHash request)

include views objects ed ml edGetter mlGetter hashLeaf

theorem native_program (identityIndex : Nat) (identifier : U64) (rng : R) :
    nativeView <$>run setup view identityIndex identifier generator rng=(do
      let prepared←AdapterServerConstructorStartup.keys (n:=n) mlSource ensureInit
      match prepared with
      | none => pure none
      | some prepared => AdapterServerConstructorStartup.finish setup mlSource identityIndex identifier prepared) := by
  have keyLaw : Prod.fst <$>AdapterServerConstructorJoint.joint generator view setup.joint edSample ed mlSample ml rng=
      AdapterServerConstructorStartup.keys (n:=n) mlSource ensureInit := by
    rw [AdapterServerConstructorJoint.native generator view setup.joint edSample ed mlSample ml]
    rfl
  unfold run
  rw [AdapterServerConstructorJoint.source_program generator view views objects setup.joint edSample ed mlSample ml identifier rng]
  simp only [RustT.run_lift,map_bind,Functor.map_map,bind_map_left]
  rw [←keyLaw]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨prepared,nextRng⟩
  cases prepared with
  | none => simp only [AdapterServerConstructorJoint.sourceResult,map_pure,nativeView,Option.map_none]
  | some prepared =>
    simp only [AdapterServerConstructorJoint.sourceResult,map_bind,map_pure,nativeView]
    apply StateT.ext
    intro before
    simp only [bind_pure_comp]
    rw [StateT.run_map]
    exact AdapterServerConstructorInitialized.native setup generator view views objects edSample ed mlSample ml
      identityIndex identifier prepared nextRng before edGetter mlGetter hashLeaf

theorem native (identityIndex : Nat) (identifier : U64) (rng : R) :
    nativeView <$>game setup view identityIndex identifier generator rng=
      RegistrationNativeExperiment.start (n:=n) setup mlSource ensureInit identityIndex identifier := by
  rw [AdapterServerConstructorStartup.native]
  have law:=congrArg (fun work => Prod.fst <$>work.run PqxdhRecordLiftWorld.initial)
    (native_program setup generator view views objects ensureInit ed ml edGetter mlGetter hashLeaf identityIndex identifier rng)
  have matched (generated : Option (AdapterServerConstructorJoint.Prepared mlSource)×World) :
      Prod.fst <$> (match generated.1 with
        | none => (pure none : M (Option (RegistrationNativeExperiment.Initial n KemSK mlSource)))
        | some prepared => AdapterServerConstructorStartup.finish setup mlSource identityIndex identifier prepared).run generated.2=
      (match generated.1 with
        | none => pure none
        | some prepared => Prod.fst <$>(AdapterServerConstructorStartup.finish setup mlSource identityIndex identifier prepared).run generated.2) := by
    rcases generated with ⟨prepared,world⟩
    cases prepared <;> simp only [StateT.run_pure,map_pure]
  simp only [StateT.run_map,Functor.map_map,StateT.run_bind,map_bind,matched] at law
  simp only [game,Functor.map_map]
  refine law.trans ?_
  apply bind_congr
  rintro ⟨prepared,world⟩
  cases prepared <;> rfl
end BeaconcryptCore.Refinement.AdapterServerConstructorRunner

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorRunner.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorRunner.native_program

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorRunner.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorRunner.native
