-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters
/-! Actual Init publication and the complete public-owner bundle use at most one concrete source writer reservation cap. Every native hash/sign/scalar query remains old/global; only the actual writer sampler adds external coins. Source phase lookup, retries, optional primitive replies, writer rejection, owner commit and full P poststates remain in the tree. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend (Base trusted writer)
open RegistrationNativePlatformPublicExternalLocal (IsLocalExternal trusted_zero)
variable {n : Nat} {I KemSK Auxiliary Platform A B Encoded E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev Work (A : Type) := RegistrationNativePlatformGenericBundle.M source Auxiliary (Base n KemSK Platform) A

def Bounded (work : Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) A) (cap : Nat) : Prop :=
  ∀ owners env before, (((work.run owners).run env).run before).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) cap

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem pure_bound (value : A) (cap : Nat) :
    Bounded (pure value : Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) A) cap := by
  intro owners env before
  simp only [StateT.run_pure]
  trivial
private theorem bind_bound
    (work : Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) A)
    (next : A → Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) B)
    (firstCap laterCap : Nat) (first : Bounded work firstCap) (later : ∀ value, Bounded (next value) laterCap) :
    Bounded (work >>= next) (firstCap + laterCap) := by
  intro owners env before
  simp only [StateT.run_bind]
  exact isQueryBoundP_bind (first owners env before)
    (fun result _ => later result.1.1.1 result.1.1.2 result.1.2 result.2)
private theorem bind_zero
    (work : Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) A)
    (next : A → Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) B)
    (cap : Nat) (first : Bounded work 0) (later : ∀ value, Bounded (next value) cap) :
    Bounded (work >>= next) cap := by
  simpa only [Nat.zero_add] using bind_bound work next 0 cap first later
private theorem bind_tail_zero
    (work : Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) A)
    (next : A → Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) B)
    (cap : Nat) (first : Bounded work cap) (later : ∀ value, Bounded (next value) 0) :
    Bounded (work >>= next) cap := by
  simpa only [Nat.add_zero] using bind_bound work next cap 0 first later

section Publication
open RegistrationNativePlatformBeaconPublication
variable (implementation : QueryImpl RegistrationBeaconInitExecutor.Spec
  (Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source)))
variable (encode : registration.SignedInitView → Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) (RustM (core.option.Option Encoded)))
variable (cap : Nat) (native : ∀ query, Bounded (implementation query) 0) (encoded : ∀ view, Bounded (encode view) cap)
attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.BeaconEd25519Signing.resume registration.begin_beacon_init

private theorem continue_bound {Input : Type} (action : RustM Input)
    (next : Input → Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source)
      (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (cost : Nat) (bounded : ∀ value, Bounded (next value) cost) :
    Bounded (continueWith action next) cost := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => exact pure_bound _ cost
include encoded in
private theorem ready_bound (pending : registration.BeaconInitReady) : Bounded (ready encode pending) cap := by
  unfold ready
  apply continue_bound
  intro view
  exact bind_tail_zero _ _ cap (encoded view) (fun _ => pure_bound _ 0)
include native encoded in
private theorem signing_bound (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) : Bounded (fromSigning implementation encode payload digest pending) cap := by
  unfold fromSigning
  apply continue_bound
  intro request
  apply bind_zero _ _ cap (native _)
  intro reply
  apply continue_bound
  intro effect
  cases effect with
  | Ready selected => exact ready_bound encode cap encoded selected
  | _ => exact pure_bound _ cap
include native encoded in
private theorem hash_bound (pending : registration.BeaconInitHash) : Bounded (fromHash implementation encode pending) cap := by
  unfold fromHash
  apply continue_bound
  intro request
  apply bind_zero _ _ cap (native _)
  intro digest
  apply continue_bound
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing_bound implementation encode cap native encoded _ _ selected
  | _ => exact pure_bound _ cap
include native encoded in
private theorem fingerprint_bound (pending : registration.BeaconFingerprint) : Bounded (fromFingerprint implementation encode pending) cap := by
  unfold fromFingerprint
  apply continue_bound
  intro request
  apply bind_zero _ _ cap (native _)
  intro digest
  apply continue_bound
  intro effect
  cases effect with
  | HashRequested selected => exact hash_bound implementation encode cap native encoded selected
  | _ => exact pure_bound _ cap
include native encoded in
private theorem ed_bound (pending : registration.BeaconEd25519Signing) : Bounded (fromEd implementation encode pending) cap := by
  rw [fromEd.eq_def]
  apply continue_bound
  intro request
  apply bind_zero _ _ cap (native _)
  intro reply
  cases actual : pending.resume reply with
  | fail error | div => exact pure_bound _ cap
  | ok effect => cases effect with
    | Ed25519SigningRequested next => exact ed_bound next
    | FingerprintRequested selected => exact fingerprint_bound implementation encode cap native encoded selected
    | _ => exact pure_bound _ cap
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next actual

include native encoded in
/-- All actual source signing and hashing prefixes pay only the one reached external encoder allowance, with every optional failure retained. -/
theorem begin_bound (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    Bounded (begin implementation encode control inputs coins pin mldsa) cap := by
  unfold begin
  apply continue_bound
  intro effect
  cases effect with
  | Ed25519SigningRequested selected => exact ed_bound implementation encode cap native encoded selected
  | _ => exact pure_bound _ cap
end Publication

private theorem legacy_zero
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A) :
    Bounded (RegistrationNativePlatformGenericBundle.liftLegacy (trusted (Platform := Platform)) work) 0 := by
  intro owners env before
  simp only [RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run]
  exact trusted_zero _ before

/-- Actual source encoding of the signed Init has its single public capacity sampler cap inside the full owner/Env/P stack. -/
theorem encoder_bound (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (cap : Nat) (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound cap) (view : registration.SignedInitView) :
    Bounded (RegistrationNativePlatformGenericBundle.encoderWith
      (writer (n := n) (KemSK := KemSK) (RegistrationNativePlatformConcreteSource.writer reserve)) view :
        Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) (RustM (core.option.Option (alloc.vec.Vec U8)))) cap := by
  intro owners env before
  simp only [RegistrationNativePlatformGenericBundle.encoderWith, StateT.run_lift, StateT.run_map,
    bind_pure_comp, Functor.map_map, isQueryBoundP_map_iff]
  exact RegistrationNativePlatformPublicExternalWriters.init_bound reserve cap bounded view before

private theorem get_zero :
    Bounded (get : Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source)
      (RegistrationNativeBeaconFrontend.State source)) 0 := by
  intro owners env before
  simp only [StateT.run_get, StateT.run_pure]
  trivial

/-- Every actual bundle path has at most the concrete Init writer's one public reservation allowance; all native sampling/signing remains in the separate bill. -/
theorem bundle_bound (setup : Setup base KemSK)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (cap : Nat) (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound cap) (index : Nat) :
    Bounded (RegistrationNativePlatformGenericBundle.bundle
      (trusted (n := n) (KemSK := KemSK) (Platform := Platform)) setup source
      (RegistrationNativePlatformGenericBundle.encoderWith
        (writer (n := n) (KemSK := KemSK) (RegistrationNativePlatformConcreteSource.writer reserve))) index :
        Work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source)
          (RustM (Option (alloc.vec.Vec U8)))) cap := by
  unfold RegistrationNativePlatformGenericBundle.bundle
  apply bind_zero _ _ cap get_zero
  intro owners
  cases found : owners[index]? with
  | none => exact pure_bound _ cap
  | some owner =>
    cases phase : owner.phase <;> simp only [phase]
    all_goals first
      | exact pure_bound _ cap
      | apply bind_zero _ _ cap
        · first | exact legacy_zero _ | exact pure_bound _ 0
        · intro oneTime
          apply bind_tail_zero _ _ cap
          · exact begin_bound _ _ cap (fun _ => legacy_zero _) (encoder_bound reserve cap bounded) _ _ _ _ _
          · intro published
            cases published with
            | fail error | div => exact pure_bound _ 0
            | ok result => cases result with
              | Err previous => exact pure_bound _ 0
              | Ok finished =>
                exact bind_zero _ _ 0 (legacy_zero _) (fun _ => bind_zero _ _ 0 (legacy_zero _) (fun _ => pure_bound _ 0))

/-- The public restored-owner wrapper keeps the same actual writer/P cap without a canonical-owner or old-profile premise. -/
theorem owner_bundle_bound (setup : Setup base KemSK)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (cap : Nat) (bounded : ∀ amount before, ((reserve amount).run before).IsTotalQueryBound cap)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (before : Platform) :
    ((((RegistrationNativePlatformPublicOwners.bundle (trusted (n := n) (KemSK := KemSK))
      (writer (RegistrationNativePlatformConcreteSource.writer reserve)) setup source selected publicPrekey index).run owners).run env).run before).IsQueryBoundP
      (IsLocalExternal (KemSK := KemSK)) cap := by
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, isQueryBoundP_map_iff]
  exact bundle_bound setup reserve cap bounded index (owners.map RegistrationNativePublicOwners.restore) env before
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication.begin_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication.encoder_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication.encoder_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication.bundle_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication.owner_bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication.owner_bundle_bound
