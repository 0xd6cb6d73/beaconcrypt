-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
import BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore
/-! Selected scalar and public-prekey restoration commutes with actual local phase/history updates in a common primitive/platform monad. Writer callbacks receive the signed view only and retain their complete external poststates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicOwnerRestore (mask)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhJointIdentity (PeerEncoding)
variable {n : Nat} {KemSK Auxiliary A B : Type} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m]

def alter (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding) (index : Nat) (owner : Owner source) : Owner source :=
  if index = selected then {owner with prekeyScalar := scalar, prekeyPublic := PqxdhRootTableInitialization.rootArray publicPrekey} else owner

def Equivariant (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (work : RegistrationNativePlatformGenericBundle.M source Auxiliary m A) : Prop :=
  ∀ owners env, Prod.map (Prod.map id (mask selected scalar publicPrekey)) id <$> (work.run owners).run env =
    (work.run (mask selected scalar publicPrekey owners)).run env

theorem lookup (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) (index : Nat) :
    (mask selected scalar publicPrekey owners)[index]? = (owners[index]?).map (alter selected scalar publicPrekey index) :=
  List.getElem?_mapIdx

theorem set (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) (index : Nat) (owner : Owner source) :
    mask selected scalar publicPrekey (owners.set index owner) =
      (mask selected scalar publicPrekey owners).set index (alter selected scalar publicPrekey index owner) :=
  List.mapIdx_set

variable [LawfulMonad m]

theorem pure_equivariant (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding) (value : A) :
    Equivariant selected scalar publicPrekey (pure value : RegistrationNativePlatformGenericBundle.M source Auxiliary m A) := by
  intro owners env
  simp only [StateT.run_pure, map_pure, Prod.map_def, id_eq]

theorem bind_equivariant (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (work : RegistrationNativePlatformGenericBundle.M source Auxiliary m A)
    (next : A → RegistrationNativePlatformGenericBundle.M source Auxiliary m B)
    (first : Equivariant selected scalar publicPrekey work)
    (later : ∀ value, Equivariant selected scalar publicPrekey (next value)) :
    Equivariant selected scalar publicPrekey (work >>= next) := by
  intro owners env
  simp only [StateT.run_bind, map_bind]
  rw [← first owners env, bind_map_left]
  apply bind_congr
  intro middle
  exact later middle.1.1 middle.1.2 middle.2

theorem lift_equivariant (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (work : StateT (EnvState Auxiliary) m A) :
    Equivariant selected scalar publicPrekey (StateT.lift work : RegistrationNativePlatformGenericBundle.M source Auxiliary m A) := by
  intro owners env
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map]
  rfl

theorem current_equivariant (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (index : Nat) (update : Owner source → Owner source)
    (commutes : ∀ owner, alter selected scalar publicPrekey index (update owner) = update (alter selected scalar publicPrekey index owner)) :
    Equivariant selected scalar publicPrekey ((modify fun owners => match owners[index]? with
      | none => owners | some owner => owners.set index (update owner)) : RegistrationNativePlatformGenericBundle.M source Auxiliary m Unit) := by
  intro owners env
  simp only [StateT.run_modify, StateT.run_pure, map_pure, Prod.map_def, id_eq, lookup]
  cases found : owners[index]? with
  | none => rfl
  | some owner => simp only [Option.map_some, set, commutes]

theorem legacy_lift (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (implementation : QueryImpl (Trusted n KemSK) m)
    (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) A) :
    Equivariant selected scalar publicPrekey
      (RegistrationNativePlatformGenericBundle.liftLegacy implementation (StateT.lift work :
        RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A)) := by
  intro owners env
  unfold RegistrationNativePlatformGenericBundle.liftLegacy
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, simulateQ_map]
  change Prod.map (Prod.map id (mask selected scalar publicPrekey)) id <$>
    ((fun reply => ((reply.1, owners), reply.2)) <$> simulateQ implementation (work.run env)) =
      (fun reply => ((reply.1, mask selected scalar publicPrekey owners), reply.2)) <$> simulateQ implementation (work.run env)
  rw [Functor.map_map]
  rfl

omit [LawfulMonad m] in
theorem legacy_modify (implementation : QueryImpl (Trusted n KemSK) m)
    (update : RegistrationNativeBeaconFrontend.State source → RegistrationNativeBeaconFrontend.State source) :
    RegistrationNativePlatformGenericBundle.liftLegacy implementation
      (modify update : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Unit) =
      (modify update : RegistrationNativePlatformGenericBundle.M source Auxiliary m Unit) := by
  funext owners env
  rfl

theorem legacy_program {I : Type} {spec : OracleSpec I}
    (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (implementation : QueryImpl (Trusted n KemSK) m)
    (handler : QueryImpl spec (RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary))
    (allowed : ∀ query, Equivariant selected scalar publicPrekey
      (RegistrationNativePlatformGenericBundle.liftLegacy implementation (handler query)))
    (work : OracleComp spec A) :
    Equivariant selected scalar publicPrekey (RegistrationNativePlatformGenericBundle.liftLegacy implementation (simulateQ handler work)) := by
  rw [RegistrationNativePlatformGenericBundle.liftLegacy_simulate]
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_equivariant selected scalar publicPrekey value
  | query_bind query next ih =>
      simpa only [simulateQ_bind, simulateQ_spec_query] using bind_equivariant selected scalar publicPrekey _ _ (allowed query) ih

theorem legacy_sample (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (implementation : QueryImpl (Trusted n KemSK) m) (work : ProbComp A) :
    Equivariant selected scalar publicPrekey (RegistrationNativePlatformGenericBundle.liftLegacy implementation
      (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work)) :=
  legacy_program selected scalar publicPrekey implementation _ (fun _ => legacy_lift selected scalar publicPrekey implementation _) work

variable {I : Type} {base : OracleSpec I}
theorem outgoing (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (implementation : QueryImpl (Trusted n KemSK) m) (index : Nat) (owner : Owner source)
    (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Equivariant selected scalar publicPrekey (RegistrationNativePlatformGenericBundle.liftLegacy implementation
      (RegistrationNativeBeaconFrontend.outgoing (Auxiliary := Auxiliary) setup source index owner query)) := by
  rcases query with (hashRequest | signRequest) | edRequest
  · exact legacy_lift selected scalar publicPrekey implementation _
  · rw [RegistrationNativeBeaconFrontend.outgoing, RegistrationNativePlatformGenericBundle.liftLegacy_pure]
    exact pure_equivariant selected scalar publicPrekey _
  · simp only [RegistrationNativeBeaconFrontend.outgoing]
    split
    · rw [RegistrationNativePlatformGenericBundle.liftLegacy_bind]
      apply bind_equivariant selected scalar publicPrekey
      · rw [RegistrationNativeBeaconFrontend.logEd, legacy_modify]
        apply current_equivariant selected scalar publicPrekey index
        intro current
        by_cases chosen : index = selected <;> simp only [alter, chosen, ite_true, ite_false]
      · intro changed
        rw [RegistrationNativePlatformGenericBundle.liftLegacy_pure]
        exact pure_equivariant selected scalar publicPrekey _
    · rw [RegistrationNativePlatformGenericBundle.liftLegacy_pure]
      exact pure_equivariant selected scalar publicPrekey _

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.lookup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.set

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.pure_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.pure_equivariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.bind_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.bind_equivariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.lift_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.lift_equivariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.current_equivariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.current_equivariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.legacy_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.legacy_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.legacy_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.legacy_modify

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.legacy_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.legacy_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.legacy_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.legacy_sample

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask.outgoing

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask
