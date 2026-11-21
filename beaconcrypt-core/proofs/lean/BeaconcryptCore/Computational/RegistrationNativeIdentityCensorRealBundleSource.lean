-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBeginSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOriginalPublication
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal

/-! Full captured selected bundles have their literal honest-source marginal. Publication and terminal commit use the actual scoped Main dictionary, with all pin/sign/writer failures and the charged World owner operation retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBundleSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" work ")" => interpret setup.joint selected placeholder false work
local notation "original(" work ")" => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint work
local notation "publication(" scalar ")" => Main (simulateQ
  (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
    setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
  (RegistrationNativePlatformWriter.begin E (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
    (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) owner.pin))
local notation "body(" scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar (RegistrationNativePlatformConcreteSource.writer reserve))
local notation "next(" scalar "," reply ")" => Main (RegistrationNativePlatformIdentityBundle.next index owner scalar reply)

private theorem terminal (scalar : PqxdhJointGapDh.ScalarBytes) (reply : RegistrationNativePlatformIdentityBundle.Reply)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(next(scalar, reply))).run before =
      (original(next(scalar, reply))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  apply RegistrationNativeIdentityCensorRealSigning.main
  rw [RegistrationNativeIdentityCensorBundleTerminal.next_run setup checks representation created index owner scalar reply before.1.1]
  trivial

private theorem first_publication (scalar : PqxdhJointGapDh.ScalarBytes) (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected) (armed : before.1.2.armed = true)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(publication(scalar))).run before =
      (original(publication(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  rw [RegistrationNativeIdentityCensorPublicationSource.source setup checks representation created selected index owner placeholder reserve false,
    RegistrationNativeIdentityCensorOriginalPublication.source setup checks representation created index owner reserve]
  exact RegistrationNativeIdentityCensorRealBeginSource.begin setup checks representation created index owner
    (RegistrationNativeIdentityCensorConcreteWriter.encode reserve) selected placeholder _ _ _ _ started built rfl
    before seed handle armed held sourceTarget fresh found

/-- The complete actual first selected captured body restores the honest source, including original failed publication and the precise terminal native phase/World effect. -/
theorem first (scalar : PqxdhJointGapDh.ScalarBytes) (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected) (armed : before.1.2.armed = true)
    (held : before.1.2.target = none) (sourceTarget : before.2.target = none)
    (fresh : absBytes started.message.one_time_key ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.2.pool.transcript))
    (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(body(scalar))).run before =
      (original(body(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  simp only [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold, RegistrationNativeIdentityCensorSourceFold.bind_source,
    RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind, map_bind]
  rw [← first_publication setup checks representation created selected index owner placeholder reserve scalar started built before seed handle armed held sourceTarget fresh found,
    bind_map_left]
  apply bind_congr
  intro result
  simpa only [Prod.map, id_eq] using terminal setup checks representation created selected index owner placeholder scalar result.1 result.2

private theorem repeated_publication (scalar : PqxdhJointGapDh.ScalarBytes) (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = some (absBytes started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(publication(scalar))).run before =
      (original(publication(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  rw [RegistrationNativeIdentityCensorPublicationSource.source setup checks representation created selected index owner placeholder reserve false,
    RegistrationNativeIdentityCensorOriginalPublication.source setup checks representation created index owner reserve]
  exact RegistrationNativeIdentityCensorRealBeginSource.repeated_begin setup checks representation created index owner
    (RegistrationNativeIdentityCensorConcreteWriter.encode reserve) selected placeholder _ _ _ _ started built rfl
    before seed handle held sourceTarget found

/-- Every matching repeated captured source bundle retains the full literal honest-source marginal without freshness or rearming. -/
theorem repeated (scalar : PqxdhJointGapDh.ScalarBytes) (started : pqxdh.BeaconStart)
    (built : pqxdh.beacon_start (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (seed : PqxdhJointIdentity.IdentitySeed)
    (handle : owner.identity.handle = selected)
    (held : before.1.2.target = some (absBytes started.message.one_time_key))
    (sourceTarget : before.2.target = some (absBytes started.message.one_time_key))
    (found : before.2.pool.seeds[selected]? = some seed) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$> (source(body(scalar))).run before =
      (original(body(scalar))).run (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  simp only [RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold, RegistrationNativeIdentityCensorSourceFold.bind_source,
    RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind, map_bind]
  rw [← repeated_publication setup checks representation created selected index owner placeholder reserve scalar started built before seed handle held sourceTarget found,
    bind_map_left]
  apply bind_congr
  intro result
  simpa only [Prod.map, id_eq] using terminal setup checks representation created selected index owner placeholder scalar result.1 result.2

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBundleSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBundleSource.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBundleSource.first

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBundleSource.repeated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealBundleSource.repeated
