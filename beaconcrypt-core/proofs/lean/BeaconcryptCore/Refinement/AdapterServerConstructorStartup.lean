-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorJoint
import BeaconcryptCore.Computational.RegistrationNativeExperiment
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Literal current native startup is exposed at its existing Ed then ML sampler boundary. The exact sampled interpreter retains every coin charge; no startup distribution or initialized-state law is assumed. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorStartup
open BeaconcryptCore.Computational
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I}

def edCore (ensureInit : StateT Unit ProbComp Bool) : ProbComp (Option PqxdhJointIdentity.IdentitySeed) := do
  let ready←ensureInit.run ()
  if ready.1 then some <$>PqxdhJointIdentity.sampleSeed else pure none

theorem construct (joint : PqxdhJointIdentity.Primitives) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (identifier : U64) :
    (PqxdhLiveServerConstruction.construct (P:=Std.Array U8 151#usize) joint ensureInit identityIndex identifier none).run ()=
      (fun seed=>(seed.map (PqxdhLiveServerConstruction.initialized joint identityIndex identifier .generated),())) <$>
        edCore ensureInit := by
  unfold PqxdhLiveServerConstruction.construct edCore
  simp only [StateT.run,map_bind]
  apply bind_congr
  rintro ⟨ready,⟨⟩⟩
  cases ready <;> simp only [Bool.false_eq_true,ite_false,ite_true,map_pure,Functor.map_map,Option.map_none,Option.map_some]

private theorem sampled_map {A B : Type} (f : A→B) (work : ProbComp A)
    (before : PqxdhRecordLiftWorld.State n) :
    (PqxdhRecordLiftWorld.sampled (f <$>work)).run before=
      (fun result=>(f result.1,result.2)) <$> (PqxdhRecordLiftWorld.sampled work).run before := by
  simp only [PqxdhRecordLiftWorld.sampled,StateT.run,simulateQ_map,map_bind,map_pure]
  have mapped : (f <$>simulateQ PqxdhRecordLiftWorld.countCoin work) before.primitive.1.uniform=
      (fun result=>(f result.1,result.2)) <$>(simulateQ PqxdhRecordLiftWorld.countCoin work).run before.primitive.1.uniform := by
    simpa only [StateT.run] using StateT.run_map f (simulateQ PqxdhRecordLiftWorld.countCoin work) before.primitive.1.uniform
  rw [mapped,bind_map_left]
  rfl

noncomputable def keys (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool) :
    StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option (AdapterServerConstructorJoint.Prepared source)) := do
  let seed←PqxdhRecordLiftWorld.sampled (edCore ensureInit)
  match seed with
  | none=>pure none
  | some seed=>
    let credential←PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.generate source)
    pure (credential.map (fun credential=>(⟨seed,credential⟩ : AdapterServerConstructorJoint.Prepared source)))

noncomputable def finish (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (identityIndex : Nat) (identifier : U64)
    (prepared : AdapterServerConstructorJoint.Prepared source) :
    StateT (PqxdhRecordLiftWorld.State n) ProbComp (Option (RegistrationNativeExperiment.Initial n KemSK source)) := fun before=>do
  let created:=PqxdhLiveServerConstruction.initialized setup.joint identityIndex identifier .generated prepared.seed
  let initialized←(RegistrationWorldServerFrontend.start created prepared.credential.publicKey RegistrationServerRoleBackend.empty).run before
  pure ((match initialized.1 with
    | .ok (.Some native)=>some ⟨created,prepared.credential,⟨RegistrationServerFrontendCompiler.erase native,[],PqxdhLiveKemBirth.empty,0⟩⟩
    | _=>none),initialized.2)

theorem native (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (identifier : U64) :
    RegistrationNativeExperiment.start (n:=n) setup source ensureInit identityIndex identifier=(do
      let generated←(keys source ensureInit).run PqxdhRecordLiftWorld.initial
      match generated.1 with
      | none=>pure none
      | some prepared=>Prod.fst <$>(finish setup source identityIndex identifier prepared).run generated.2) := by
  unfold RegistrationNativeExperiment.start
  rw [construct,sampled_map]
  simp only [bind_map_left]
  unfold keys
  simp only [StateT.run_bind,bind_assoc]
  apply bind_congr
  intro generated
  cases seed:generated.1 with
  | none=>simp only [Option.map_none,StateT.run_pure,pure_bind]
  | some seed=>
    simp only [Option.map_some,StateT.run_bind,StateT.run_pure,bind_assoc]
    simp only [pure_bind]
    apply bind_congr
    intro credential
    cases selected:credential.1 with
    | none=>simp only [Option.map_none]
    | some selected=>
      simp only [Option.map_some,finish,StateT.run,map_bind,map_pure]
      apply bind_congr
      rintro ⟨reply,world⟩
      cases reply with
      | fail error | div=>rfl
      | ok value=>cases value <;> rfl
end BeaconcryptCore.Refinement.AdapterServerConstructorStartup

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorStartup.construct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorStartup.construct

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorStartup.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorStartup.native
