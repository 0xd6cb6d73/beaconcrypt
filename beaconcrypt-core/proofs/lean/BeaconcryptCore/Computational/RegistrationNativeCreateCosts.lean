-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTrustedCosts

/-! Constructor callback bill. The current Beacon constructor (Rust: no Beacon ML-DSA credential, fixed-size native Server pin) draws a 32-byte identity and a 32-byte prekey (`prepare_exact_bound`, exact bill `preparedBill`), then performs the indexed KEM birth and the owner allocation (`append_bound`). The exported `prepareBill`/`createBill` keep their original ML-generation and hash cells, so they over-approximate the exact bill (`prepare_bound`, `create_bound`, `frontend_bound`). Each source failure stops at its original position and retains every earlier draw. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeCreateCosts
open PqxdhRecordLiftInterface (EffectKind effectKind)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePublicationCosts (hashCost)
open RegistrationNativeTrustedCosts (bill sample_bound effect_bound kem_bound)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_mono)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

def administrativeCost : EffectKind → Nat
  | .administrative => 1
  | .coin | .hash => 0

def prepareBill (qGenerate : Nat) (kind : EffectKind) := coinCost qGenerate kind + (hashCost kind + (coinCost 32 kind + coinCost 32 kind))
def createBill (qGenerate qKem : Nat) (kind : EffectKind) := prepareBill qGenerate kind + (coinCost qKem kind + administrativeCost kind)

attribute [local irreducible] registration.begin_server_pin

/-- The exact bill of the current constructor preflight: one 32-byte identity draw and one 32-byte prekey draw. The fixed-size Server pin is computed natively; the Beacon performs no ML generation and no pin-fingerprint hash. -/
def preparedBill (kind : EffectKind) := coinCost 32 kind + coinCost 32 kind

/-- All source constructor preflights retain the exact identity/prekey bill. -/
theorem prepare_exact_bound (source : RegistrationNativeMldsa.Source) (qKem : Nat)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (kind : EffectKind) :
    Weighted (bill (n := n) qKem kind) (((RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env)
      (preparedBill kind) := by
  simp only [RegistrationNativeBeaconFrontend.prepare]
  cases started : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | fail error => simp only [StateT.run_pure]; trivial
  | div => simp only [StateT.run_pure]; trivial
  | ok pin =>
      simp only [StateT.run_bind]
      apply weighted_bind _ _ _ _ _ (sample_bound source qKem kind _ 32 PqxdhJointIdentity.sampleSeed_uniform_bound owners env)
      intro identity
      rcases identity with ⟨⟨identity, afterIdentity⟩, identityEnvironment⟩
      rw [← Nat.add_zero (coinCost 32 kind)]
      apply weighted_bind _ _ _ _ _
        (sample_bound source qKem kind _ 32 PqxdhJointGapDh.sampleScalar_uniform afterIdentity identityEnvironment)
      intro prekey
      trivial

/-- All source constructor preflights stay within the original ML/hash/identity/prekey bill, which over-approximates the exact bill `preparedBill` now that the Beacon performs no ML generation and no pin-fingerprint hash. -/
theorem prepare_bound (source : RegistrationNativeMldsa.Source) (qGenerate qKem : Nat)
    (_generation : source.generate.IsTotalQueryBound qGenerate)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (kind : EffectKind) :
    Weighted (bill (n := n) qKem kind) (((RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env)
      (prepareBill qGenerate kind) :=
  weighted_mono _ _ _ _ (prepare_exact_bound source qKem edPin mlPin keyId owners env kind)
    (by simp only [preparedBill, prepareBill]; omega)


/-- The admitted constructor suffix performs the real indexed key generation before one public owner allocation. -/
theorem append_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (qKem : Nat) (edPin : Std.Array U8 32#usize) (keyId : U64) (pin : session.ServerAuthenticationPin)
    (identity : PqxdhJointIdentity.IdentitySeed)
    (prekey : PqxdhJointGapDh.ScalarBytes) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (kind : EffectKind) :
    Weighted (bill (n := n) qKem kind)
      (((RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId pin identity prekey).run owners).run env)
      (coinCost qKem kind + administrativeCost kind) := by
  simp only [RegistrationNativeBeaconFrontend.appendBorn, StateT.run_bind]
  apply weighted_bind _ _ _ _ _ (kem_bound source qKem kind (.inr (.inl .create)) owners env)
  intro born
  rcases born with ⟨⟨born, current⟩, environment⟩
  rw [← Nat.add_zero (administrativeCost kind)]
  apply weighted_bind _ _ _ _ _ (by
    cases kind <;> exact effect_bound (n := n) (KemSK := KemSK) source qKem _ (.inr (.appendOwner keyId edPin .fresh)) current environment)
  intro appended
  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  trivial


/-- Every actual constructor path is billed by its source primitive calls, with no desired callback-frame premise. -/
theorem create_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (qGenerate qKem : Nat) (generation : source.generate.IsTotalQueryBound qGenerate)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (kind : EffectKind) :
    Weighted (bill (n := n) qKem kind) (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run owners).run env)
      (createBill qGenerate qKem kind) := by
  simp only [RegistrationNativeBeaconFrontend.create, StateT.run_bind, createBill]
  apply weighted_bind _ _ _ _ _ (prepare_bound source qGenerate qKem generation edPin mlPin keyId owners env kind)
  intro prepared
  rcases prepared with ⟨⟨prepared, current⟩, environment⟩
  cases prepared with
  | fail error => trivial
  | div => trivial
  | ok prepared =>
      cases prepared with
      | none => trivial
      | some prepared => exact append_bound setup source qKem edPin keyId prepared.pin prepared.identity prepared.prekey current environment kind

/-- The concrete public-reference create callback inherits the source constructor bill after its unchanged owner/address embedding. -/
theorem frontend_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (qGenerate qSign qKem : Nat) (generation : source.generate.IsTotalQueryBound qGenerate)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativePublicFrontend.State source) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeRestrictedCosts.bill qSign qKem query kind)
      ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.create edPin mlPin keyId))).run before) (createBill qGenerate qKem kind) := by
  have actual := RegistrationNativeTrustedCosts.embedded_program qSign qKem kind _ _
    (create_bound (n := n) setup source qGenerate qKem generation edPin mlPin keyId
      (before.beacons.map RegistrationNativePublicOwners.restore) before.environment kind)
  simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon,
    RegistrationNativePublicOwners.create, RegistrationNativePublicOwners.executeLocal, StateT.run,
    simulateQ_map, Weighted, isQueryBound_map_iff] using actual

end BeaconcryptCore.Computational.RegistrationNativeCreateCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCreateCosts.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCreateCosts.prepare_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCreateCosts.prepare_exact_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCreateCosts.prepare_exact_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCreateCosts.append_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCreateCosts.append_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCreateCosts.create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCreateCosts.create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCreateCosts.frontend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCreateCosts.frontend_bound
