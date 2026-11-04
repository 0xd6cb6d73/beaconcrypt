-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto
/-! Individual original source methods and their actual continuations commute with erasing the passive indexed KEM log. The closure laws are algebraic; each concrete source program derives its leaf frames internally. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open AdapterPublicWrapperRustT (RustT)
variable {n : Nat} {KemSK A B I : Type} {spec : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def Compatible (work : StateT (Backend n KemSK) m A) : Prop :=
  ∀before,Prod.map id erase <$>work.run before=work.run (erase before)

theorem pure_frame (value : A) : Compatible (n:=n) (KemSK:=KemSK) (pure value :StateT (Backend n KemSK) m A) :=by
  intro before
  simp only [StateT.run_pure,map_pure]
  rfl

theorem lift_frame (work : m A) : Compatible (n:=n) (KemSK:=KemSK) (StateT.lift work) :=by
  intro before
  simp only [StateT.run_lift,bind_pure_comp,Functor.map_map]
  rfl

theorem bind_frame (work : StateT (Backend n KemSK) m A) (next : A → StateT (Backend n KemSK) m B)
    (first : Compatible work) (later : ∀value,Compatible (next value)) : Compatible (work >>=next) :=by
  intro before
  rw [StateT.run_bind,map_bind,StateT.run_bind,←first before,bind_map_left]
  apply bind_congr
  rintro ⟨value,current⟩
  exact later value current

theorem map_frame (observe : A → B) (work : StateT (Backend n KemSK) m A) (first : Compatible work) :
    Compatible (observe <$>work) :=by
  intro before
  have same:=congrArg (fun computation=>Prod.map observe id <$>computation) (first before)
  simp only [StateT.run_map,Functor.map_map,Prod.map,id_eq] at same ⊢
  exact same

theorem program_frame (implementation : QueryImpl spec (StateT (Backend n KemSK) m))
    (leaves : ∀query,Compatible (implementation query)) (work : OracleComp spec A) :
    Compatible (simulateQ implementation work) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq implementation implementation erase leaves work

omit [Monad m] [LawfulMonad m] in
theorem world_frame (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp A) :
    Compatible (RegistrationNativePlatformPublicAdapterCrypto.world (KemSK:=KemSK) work) :=by
  intro before
  simp only [RegistrationNativePlatformPublicAdapterCrypto.world,StateT.run,erase,Functor.map_map]
  rfl

omit [Monad m] [LawfulMonad m] in
theorem transform_frame (work : RustT ProbComp A) :
    Compatible (RegistrationNativePlatformPublicAdapterCrypto.transform (n:=n) (KemSK:=KemSK) work).run :=
  world_frame _

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT ProbComp)]

omit [Monad m] [LawfulMonad m] in
theorem captured_frame {R Error Value : Type} (generator : rand_core.TryCryptoRng R Error)
    (keys : AdapterPublicAgreementFields.Keys) (work : OracleComp RegistrationAgreementExecutor.Spec Value) (rng : R) :
    Compatible (RegistrationNativePlatformPublicAdapterCrypto.captured (n:=n) (KemSK:=KemSK) generator keys work rng).run :=by
  rw [RegistrationNativePlatformPublicAdapterCrypto.captured_source]
  exact transform_frame _

omit material ed original in
theorem interpret_frame (coins : QueryImpl unifSpec m) (work : StateT (Backend n KemSK) ProbComp A)
    (held : Compatible work) :
    Compatible (fun before=>simulateQ coins (work.run before) :StateT (Backend n KemSK) m A) :=by
  intro before
  change Prod.map id erase <$>simulateQ coins (work.run before)=simulateQ coins (work.run (erase before))
  rw [←simulateQ_map,held before]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.pure_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.pure_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.lift_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.lift_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.bind_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.bind_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.map_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.map_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.program_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.program_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.world_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.world_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.transform_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.transform_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.captured_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.captured_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.interpret_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame.interpret_frame
