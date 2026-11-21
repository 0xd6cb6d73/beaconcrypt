-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorObjects
import BeaconcryptCore.Refinement.AdapterBeaconConstructorGeneration
import BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Joint constructor sampling follows the literal Ed-before-ML source order and retains caller RNG. Only individual foreign key-generation and std getter/container operations are contracts. Initialization refusal is kept as an optional primitive result rather than erased. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorJoint
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open BeaconcryptCore.Computational
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [AdapterServerConstructorPrimitive.Standard]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK R Error : Type}

structure EdContract (generator : rand_core.TryCryptoRng R Error)
    (view : MaterialView source KemSK) (jointKeys : PqxdhJointIdentity.Primitives)
    (sample : m (Option PqxdhJointIdentity.IdentitySeed)) where
  joint : R → m (Option PqxdhJointIdentity.IdentitySeed × R)
  nativeMarginal : ∀ rng,Prod.fst  <$> joint rng=sample
  realize : PqxdhJointIdentity.IdentitySeed → beaconcrypt_crypto.crypto_sign.KeyPair
  privateView : ∀ seed,view.edSecret (realize seed).secret_key=seed
  publicView : ∀ seed,view.edPublic (realize seed).public_key=
    PqxdhRootTableInitialization.rootArray (jointKeys.publicKeys seed).ed25519
  failure : primitive.Error
  operation : ∀ rng,generators.edGenerate generator rng= RustT.lift
    ((fun reply => (match reply.1 with | none => .Err failure | some seed => .Ok (realize seed),reply.2))  <$> joint rng)

structure Prepared (source : RegistrationNativeMldsa.Source) where
  seed : PqxdhJointIdentity.IdentitySeed
  credential : RegistrationNativeMldsa.Credential source

variable (generator : rand_core.TryCryptoRng R Error)
variable (view : MaterialView source KemSK) (views : Views)
variable (objects : AdapterServerConstructorObjects.Leaves views)
variable (jointKeys : PqxdhJointIdentity.Primitives)
variable (edSample : m (Option PqxdhJointIdentity.IdentitySeed))
variable (ed : EdContract generator view jointKeys edSample)
variable (mlSample : m (Option (RegistrationNativeMldsa.Credential source)))
variable (ml : AdapterServerConstructorGeneration.MldsaContract generator view mlSample)

noncomputable def joint (rng : R) : m (Option (Prepared source) ×R) := do
  let generated ← ed.joint rng
  match generated.1 with
  | none => pure (none,generated.2)
  | some seed =>
    let identity ← ml.joint generated.2
    pure (identity.1.map (fun credential => ⟨seed,credential⟩),identity.2)

noncomputable def object (identifier : U64) (prepared : Prepared source) : beaconcrypt_public_wrapper.server.Server :=
  AdapterServerConstructorObjects.stored views objects identifier (ed.realize prepared.seed) (ml.realize prepared.credential)

noncomputable def sourceResult (identifier : U64) (result : Option (Prepared source)×R) : AdapterServerConstructorBody.Outcome R :=
  (match result.1 with | none => .Err () | some prepared => .Ok (object generator view views objects jointKeys edSample ed mlSample ml identifier prepared),result.2)

omit material platform primitive [AdapterServerConstructorPrimitive.Standard] generators in
private theorem marginal_bind {A B : Type} (work : m (A×R)) (sample : m A)
    (marginal : Prod.fst  <$> work=sample) (next : A×R→m B) (target : A→m B)
    (step : ∀value rng,next (value,rng)=target value) :
    (do let value←work;next value)=(do let value←sample;target value) := by
  have same : next=fun value => target value.1 := by funext value;exact step value.1 value.2
  rw [same,←bind_map_left,marginal]

omit views objects platform [AdapterServerConstructorPrimitive.Standard] in
theorem native (rng : R) :
    Prod.fst  <$> joint generator view jointKeys edSample ed mlSample ml rng=(do
      let generated←edSample
      match generated with
      | none => pure none
      | some seed =>
        let identity←mlSample
        pure (identity.map (fun credential => (⟨seed,credential⟩ : Prepared source)))) := by
  simp only [joint,map_bind]
  apply marginal_bind _ _ (ed.nativeMarginal rng)
  intro generated nextRng
  cases generated with
  | none => simp only [map_pure]
  | some seed =>
    simp only [map_bind]
    apply marginal_bind _ _ (ml.nativeMarginal nextRng)
    intro credential finalRng
    simp only [map_pure]

theorem source_program (identifier : U64) (rng : R) :
    beaconcrypt_server_constructor_request.server.Server.try_new_with_rng (m:= RustT m) generator identifier .None .None rng=
      RustT.lift (sourceResult generator view views objects jointKeys edSample ed mlSample ml identifier  <$>
        joint generator view jointKeys edSample ed mlSample ml rng) := by
  rw [AdapterServerConstructorBody.honest]
  unfold AdapterServerConstructorBody.source
  rw [ed.operation]
  apply RustT.ext
  simp only [RustT.run_bind,RustT.run_lift,bind_map_left,joint,map_bind]
  apply bind_congr
  rintro ⟨generated,nextRng⟩
  cases generated with
  | none => simp only [RustT.run_pure,map_pure,sourceResult]
  | some seed =>
    dsimp only
    rw [ml.operation]
    simp only [RustT.run_bind,RustT.run_lift,bind_map_left,map_bind,map_pure]
    apply bind_congr
    rintro ⟨credential,finalRng⟩
    cases credential with
    | none => simp only [RustT.run_pure,sourceResult,Option.map_none]
    | some credential =>
      dsimp only
      rw [AdapterServerConstructorObjects.assemble views objects]
      simp only [RustT.run_pure,pure_bind,sourceResult,object,Option.map_some]

omit [LawfulMonad m] in
theorem identity (identifierIndex : Nat) (identifier : U64) (prepared : Prepared source) :
    ServerIdentity view (platform.arcView (object generator view views objects jointKeys edSample ed mlSample ml identifier prepared).identity)
      (PqxdhLiveServerConstruction.initialized jointKeys identifierIndex identifier .generated prepared.seed)
      prepared.credential := by
  exact AdapterServerConstructorObjects.identity view views objects
    (PqxdhLiveServerConstruction.initialized jointKeys identifierIndex identifier .generated prepared.seed)
    prepared.credential (ed.realize prepared.seed) (ml.realize prepared.credential)
    (ed.publicView prepared.seed) (ed.privateView prepared.seed) (ml.privateView prepared.credential)
end BeaconcryptCore.Refinement.AdapterServerConstructorJoint

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorJoint.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorJoint.native

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorJoint.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorJoint.source_program

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorJoint.identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorJoint.identity
