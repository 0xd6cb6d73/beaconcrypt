-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainTyped
import BeaconcryptCore.Computational.RegistrationNativeIdentityLifecycleOwned

/-! The whole ordinary joint-service native client derives its generated-credential invariant from the literal source. Private seed ownership survives every actual typed failure and success; it is never a public event premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State M)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativeIdentityMainSource (interpret Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Ordinary native work retains the whole public frontend and private seed table after only extra joint-game uniform transcript entries are projected. -/
theorem ordinary_execution (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (Context n KemSK) ProbComp Value) (before : State n KemSK mlSource × SourceState) :
    Prod.map id RegistrationNativeIdentityMainBeacon.poolProjection <$>
      (interpret joint (RegistrationNativeIdentityMain.ordinary work)).run before =
      (fun result => (result.1, ({ before.1 with context := result.2 }, RegistrationNativeIdentityCompiler.poolView before.2))) <$>
        work.run before.1.context := by
  have law := congrArg (fun distribution => (fun result => (result.1.1,
    ({ before.1 with context := result.1.2 }, result.2))) <$> distribution)
    (RegistrationNativeIdentityMainSource.coins_source joint (work.run before.1.context) before.2)
  simp only [interpret, RegistrationNativeIdentityMain.ordinary, StateT.run, simulateQ_map,
    RegistrationNativeIdentityMainOrdinary.map_apply, Functor.map_map, Prod.map, id_eq,
    RegistrationNativeIdentityMainBeacon.poolProjection] at law ⊢
  exact law

/-- Actual ordinary SDK and World operations leave every generated credential genuinely owned. -/
theorem ordinary_owned (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (Context n KemSK) ProbComp Value) (before : State n KemSK mlSource × SourceState)
    (result : Value × (State n KemSK mlSource × SourceState)) (owned : Owned joint before)
    (reached : result ∈ support ((interpret joint (RegistrationNativeIdentityMain.ordinary work)).run before)) :
    Owned joint result.2 := by
  have viewed := Set.mem_image_of_mem (Prod.map id RegistrationNativeIdentityMainBeacon.poolProjection) reached
  rw [← support_map, ordinary_execution, support_map] at viewed
  obtain ⟨inner, _supported, same⟩ := viewed
  cases result with
  | mk reply after =>
      have retained : Owned joint ({ before.1 with context := inner.2 }, RegistrationNativeIdentityCompiler.poolView before.2) := owned
      have shifted := congrArg (fun output => Owned joint output.2) same
      exact shifted ▸ retained

private theorem beacon_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State mlSource Value)
    (preserves : ∀ current env prior next,
      RegistrationNativeIdentityRealization.Owned setup.joint prior.identities current →
      next ∈ support ((simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := mlSource)
        setup checks representation created) ((work.run current).run env)).run prior) →
      RegistrationNativeIdentityRealization.Owned setup.joint next.2.identities next.1.1.2)
    (before : State n KemSK mlSource × SourceState) (result : Value × (State n KemSK mlSource × SourceState))
    (owned : Owned setup.joint before)
    (reached : result ∈ support
      ((interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created work)).run before)) :
    Owned setup.joint result.2 := by
  have viewed := Set.mem_image_of_mem (Prod.map id RegistrationNativeIdentityMainBeacon.poolProjection) reached
  rw [← support_map, RegistrationNativeIdentityMainBeacon.beacon_execution, support_map] at viewed
  obtain ⟨inner, supported, same⟩ := viewed
  have retained := preserves before.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)
    ⟨before.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ inner owned supported
  change Owned setup.joint (RegistrationNativeIdentityMainBeacon.assemble inner).2 at retained
  rw [same] at retained
  exact retained

/-- Complete actual creation derives new ownership and preserves all prior generated credentials. -/
theorem create_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK mlSource × SourceState)
    (result : RustM (Option Nat) × (State n KemSK mlSource × SourceState)) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created
      (RegistrationNativeIdentityFrontend.create setup mlSource edPin mlPin keyId))).run before)) :
    Owned setup.joint result.2 := by
  apply beacon_owned setup checks representation created _ _ before result owned reached
  intro current env prior next assumed supported
  exact RegistrationNativeIdentitySourceCreateOwned.create_owned setup checks representation created
    edPin mlPin keyId current env prior next assumed supported

/-- Every actual outgoing bundle outcome preserves the generated credential invariant. -/
theorem bundle_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before : State n KemSK mlSource × SourceState)
    (result : RustM (Option Pqxdh.Bytes) × (State n KemSK mlSource × SourceState)) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created
      (RegistrationNativeIdentityFrontend.bundle setup mlSource wire index))).run before)) :
    Owned setup.joint result.2 := by
  apply beacon_owned setup checks representation created _ _ before result owned reached
  intro current env prior next assumed supported
  exact RegistrationNativeIdentityLifecycleOwned.bundle_owned setup checks representation created wire index
    current env prior next.2 next.1 assumed supported

/-- Every actual terminal finish path preserves ownership, including failed authentication, open or insertion. -/
theorem finish_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) (before : State n KemSK mlSource × SourceState)
    (result : RustM (Option Pqxdh.Bytes) × (State n KemSK mlSource × SourceState)) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created
      (RegistrationNativeIdentityFrontend.finish setup mlSource wire index packet))).run before)) :
    Owned setup.joint result.2 := by
  apply beacon_owned setup checks representation created _ _ before result owned reached
  intro current env prior next assumed supported
  exact RegistrationNativeIdentityLifecycleOwned.finish_owned setup checks representation created wire index packet
    current env prior next.2 next.1 assumed supported

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned.ordinary_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned.ordinary_execution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned.ordinary_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned.ordinary_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned.create_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned.create_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned.bundle_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned.bundle_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned.finish_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned.finish_owned
