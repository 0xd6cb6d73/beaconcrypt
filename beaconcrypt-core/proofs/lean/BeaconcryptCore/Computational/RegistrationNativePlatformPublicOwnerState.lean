-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerFinish
/-! Canonical scalar masking and pending coherence follow the actual public owner callbacks with shared platform state. Constructors and effectful bundle writers pack every output; corrected finish retains its original scalar mask and public prekey on every outcome. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicOwners (Owner State)
open RegistrationNativePublicOwnerMask (Canonical At)
open RegistrationNativePublicInvariantOwners (Coherent)
variable {n : Nat} {ι κ KemSK Auxiliary Platform Value E : Type} {base : OracleSpec ι} {target : OracleSpec κ}
variable {source : RegistrationNativeMldsa.Source}

def Valid (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (owners : State source) : Prop :=
  Canonical selected publicPrekey owners ∧ Coherent owners

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem interpreted_support {Q X : Type} {spec : OracleSpec Q}
    (implementation : QueryImpl spec (StateT Platform (OracleComp target))) (work : OracleComp spec X)
    (before after : Platform) (value : X)
    (present : (value, after) ∈ support ((simulateQ implementation work).run before)) : value ∈ support work := by
  apply OracleComp.support_simulateQ_run'_subset implementation work before
  rw [StateT.run'_eq, support_map]
  exact ⟨(value, after), present, rfl⟩

/-- Packing is canonical on all shared-state paths, including failed allocation/encoding outcomes. -/
theorem executeLocal_canonical (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativePlatformGenericBundle.M source Auxiliary (StateT Platform (OracleComp target)) Value)
    (owners : State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((Value × State source) × EnvState Auxiliary) × Platform)
    (present : result ∈ support ((((RegistrationNativePlatformPublicOwners.executeLocal selected publicPrekey work).run owners).run env).run previous)) :
    Canonical selected publicPrekey result.1.1.2 := by
  simp only [RegistrationNativePlatformPublicOwners.executeLocal, StateT.run, state_map_apply, support_map] at present
  obtain ⟨inner, _called, rfl⟩ := present
  exact RegistrationNativePublicOwnerMask.packed selected publicPrekey inner.1.1.2

private theorem restored_holds (owners : State source) (valid : Coherent owners) :
    RegistrationNativeBeaconCoherence.Holds (owners.map RegistrationNativePublicOwners.restore) := by
  exact (RegistrationNativePublicInvariantOwners.restored_holds RegistrationNativePublicOwners.dummy owners).mp valid

/-- Actual birth preserves all old pending capabilities and adds only a fresh owner. -/
theorem create_coherent (implementation : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Platform (OracleComp target)))
    (setup : Setup base KemSK) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (Option Nat) × State source) × EnvState Auxiliary) × Platform)
    (prior : Coherent owners)
    (present : result ∈ support ((((RegistrationNativePlatformPublicOwners.create implementation setup source selected publicPrekey edPin mlPin keyId).run owners).run env).run previous)) :
    Coherent result.1.1.2 := by
  simp only [RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, state_map_apply, support_map] at present
  obtain ⟨inner, called, rfl⟩ := present
  have original := interpreted_support implementation
    (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run (owners.map RegistrationNativePublicOwners.restore)).run env)
    previous inner.2 inner.1 called
  exact RegistrationNativePublicInvariantOwners.packed_holds selected publicPrekey inner.1.1.2
    (RegistrationNativeBeaconCoherence.create_keeps setup edPin mlPin keyId _ env inner.1 (restored_holds owners prior) original)

/-- Actual source publication and the shared effectful Init writer preserve every old or newly installed pending equation. -/
theorem bundle_coherent (implementation : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Platform (OracleComp target)))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform (OracleComp target)))
    (setup : Setup base KemSK) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × State source) × EnvState Auxiliary) × Platform)
    (prior : Coherent owners)
    (present : result ∈ support ((((RegistrationNativePlatformPublicOwners.bundle implementation writer setup source selected publicPrekey index).run owners).run env).run previous)) :
    Coherent result.1.1.2 := by
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, state_map_apply, support_map] at present
  obtain ⟨inner, called, rfl⟩ := present
  let combined : QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (StateT Platform (OracleComp target))
    | .inl query => implementation query
    | .inr query => writer query
  have original : inner.1 ∈ support
      (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run (owners.map RegistrationNativePublicOwners.restore)).run env) := by
    apply interpreted_support combined _ previous inner.2 inner.1
    have equation := RegistrationNativePlatformGenericBundle.program_evaluate (Auxiliary := Auxiliary) combined setup source index
    have invoked := congrArg (fun work => (((work.run (owners.map RegistrationNativePublicOwners.restore)).run env).run previous)) equation
    change inner ∈ support (((RegistrationNativePlatformGenericBundle.evaluate combined
      (RegistrationNativePlatformGenericBundle.program (n := n) E setup source index)).run (owners.map RegistrationNativePublicOwners.restore)).run env |>.run previous)
    rw [invoked]
    exact called
  exact RegistrationNativePublicInvariantOwners.packed_holds selected publicPrekey inner.1.1.2
    (RegistrationNativePlatformBundleCoherence.program (n := n) setup index _ env (restored_holds owners prior) inner.1 original)

private theorem set_valid (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : State source) (index : Nat) (owner : Owner source)
    (found : owners[index]? = some owner) (prior : Valid selected publicPrekey owners)
    (view : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (same : view.prekeyPublic = owner.view.prekeyPublic) (coherent : RegistrationNativeBeaconCoherence.PhaseCoherent view.phase) :
    Valid selected publicPrekey (owners.set index {owner with view}) := by
  constructor
  · intro position current stored
    by_cases equal : position = index
    · subst position
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, Option.some.injEq] at stored
      subst current
      simpa only [At, same] using prior.1 index owner found
    · rw [List.getElem?_set_ne (Ne.symm equal)] at stored
      exact prior.1 position current stored
  · intro position current stored
    by_cases equal : position = index
    · subst position
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, Option.some.injEq] at stored
      subst current
      exact coherent
    · rw [List.getElem?_set_ne (Ne.symm equal)] at stored
      exact prior.2 position current stored

/-- The actual corrected scalar-free or ordinary finish retains canonical masking and coherence, with arbitrary earlier record logs. -/
theorem finish_valid (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (selected : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : State source) (env : EnvState RegistrationServerRoleBackend.State) (previous : Platform)
    (result : ((RustM (Option Pqxdh.Bytes) × State source) × EnvState RegistrationServerRoleBackend.State) × Platform)
    (prior : Valid selected publicPrekey owners)
    (present : result ∈ support ((((RegistrationNativePlatformPublicFrontend.finish (n := n) setup wire source index packet).run owners).run env).run previous)) :
    Valid selected publicPrekey result.1.1.2 := by
  simp only [RegistrationNativePlatformPublicFrontend.finish, StateT.run] at present
  cases found : owners[index]? with
  | none =>
    simp only [found, state_pure_apply, support_pure, Set.mem_singleton_iff] at present
    cases present
    exact prior
  | some owner =>
    simp only [found, state_map_apply, support_map] at present
    obtain ⟨inner, called, rfl⟩ := present
    have original : inner.1 ∈ support (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner.view).run env) := by
      have raw := interpreted_support (RegistrationNativePlatformPublicFrontend.localHandler false) _ previous inner.2 inner.1 called
      cases scalarEq : owner.scalar with
      | none => simpa only [scalarEq, StateT.run] using raw
      | some scalar =>
        apply RegistrationNativePublicSourceSupport.simulate_support (RegistrationNativePublicOwners.ordinary setup scalar)
        simpa only [scalarEq, StateT.run] using raw
    have kept := RegistrationNativePlatformPublicOwnerFinish.finish setup wire packet owner.view env inner.1 (prior.2 index owner found) original
    exact set_valid selected publicPrekey owners index owner found prior inner.1.1.2 kept.1 kept.2

/-- The actual empty owner roster initializes both internal representation properties. -/
theorem empty (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) :
    Valid selected publicPrekey ([] : State source) := by
  refine ⟨RegistrationNativePublicOwnerMask.empty selected publicPrekey, ?_⟩
  intro index owner present
  simp at present

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState.executeLocal_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState.executeLocal_canonical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState.create_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState.create_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState.bundle_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState.bundle_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState.finish_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState.finish_valid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState.empty
