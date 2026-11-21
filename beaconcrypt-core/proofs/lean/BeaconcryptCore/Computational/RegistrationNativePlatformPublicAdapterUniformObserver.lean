-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementMonadCrypto
import BeaconcryptCore.Refinement.AdapterPublicAgreementGeneration
/-! A source primitive's original probabilistic request tree is interpreted through one explicit uniform observer. The same actual Rust result, private object and caller RNG are retained; source coin effects and true uniform costs are observed together. Primitive sampling/representation contracts are mapped from the original contract, rather than assumed again for an instrumented source dictionary. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable {m : Type→Type} [Monad m] [LawfulMonad m] {A B : Type}
variable (uniform : QueryImpl unifSpec m)

def observe (work : RustT ProbComp A) : RustT m A :=⟨simulateQ uniform work.run⟩

omit [LawfulMonad m] in
theorem pure_observe (value : A) : observe uniform (pure value)=pure value := by
  apply RustT.ext
  exact simulateQ_pure uniform (RustM.ok value)

theorem bind_observe (work : RustT ProbComp A) (next : A→RustT ProbComp B) :
    observe uniform (work >>=next)=(observe uniform work >>=fun value=>observe uniform (next value)) := by
  apply RustT.ext
  simp only [observe,RustT.run_bind,simulateQ_bind]
  apply bind_congr
  intro result
  cases result <;> simp only [simulateQ_pure]

omit [LawfulMonad m] in
theorem rust_observe (result : RustM A) :
    observe uniform (AdapterRecordRequestMonad.liftRust result)=AdapterRecordRequestMonad.liftRust result := by
  apply RustT.ext
  exact simulateQ_pure uniform result

theorem lift_observe (work : ProbComp A) :
    observe uniform (RustT.lift work)=RustT.lift (simulateQ uniform work) := by
  apply RustT.ext
  simp only [observe,RustT.run_lift,simulateQ_map]

theorem map_observe (f : A→B) (work : RustT ProbComp A) :
    observe uniform (f <$>work)=f <$>observe uniform work := by
  rw [←bind_pure_comp,bind_observe]
  simp only [pure_observe,bind_pure_comp]

@[instance_reducible] def transformation : AdapterPublicAgreementMonadMap.Transformation ProbComp m where
  transform:=observe uniform
  lawful:=Cslib.IsMonadHom.mk' (pure_observe uniform) (bind_observe uniform)
  lift:=rust_observe uniform

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
@[instance_reducible] def operations (original : CryptoOperations (RustT ProbComp)) : CryptoOperations (RustT m) :=
  let : AdapterPublicAgreementMonadMap.Transformation ProbComp m:=transformation uniform
  AdapterPublicAgreementMonadCrypto.operations original

variable [original : CryptoOperations (RustT ProbComp)]
noncomputable def generation {R Error KemSK : Type} {source : RegistrationNativeMldsa.Source}
    (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (publicKey : PqxdhJointGapDh.ScalarBytes→Std.Array U8 32#usize) (sample : ProbComp PqxdhJointGapDh.ScalarBytes)
    (contract : AdapterPublicAgreementGeneration.Contract generator view publicKey sample) :
    let : CryptoOperations (RustT m):=operations uniform original
    AdapterPublicAgreementGeneration.Contract generator view publicKey (simulateQ uniform sample) := by
  let : CryptoOperations (RustT m):=operations uniform original
  refine {realize:=contract.realize,privateView:=contract.privateView,publicView:=contract.publicView,operation:=?_}
  intro rng
  change observe uniform (original.kxGenerate generator rng)=_
  rw [contract.operation,lift_observe,simulateQ_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.pure_observe' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.pure_observe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.bind_observe' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.bind_observe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.rust_observe' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.rust_observe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.lift_observe' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.lift_observe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.map_observe' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.map_observe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.transformation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.transformation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver.generation
