-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTrustedCosts

/-! Literal constructor callback bill: actual ML generation, pin fingerprint,32-byte identity,32-byte prekey, indexed KEM birth and owner allocation. Each optional source failure stops at its original position and retains every earlier draw. -/

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

/-- All source constructor preflights retain the literal ML/hash/identity/prekey bill. -/
theorem prepare_bound (source : RegistrationNativeMldsa.Source) (qGenerate qKem : Nat)
    (generation : source.generate.IsTotalQueryBound qGenerate)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (kind : EffectKind) :
    Weighted (bill (n := n) qKem kind) (((RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env)
      (prepareBill qGenerate kind) := by
  simp only [RegistrationNativeBeaconFrontend.prepare, StateT.run_bind]
  apply weighted_bind _ _ _ _ _ (sample_bound source qKem kind _ qGenerate (RegistrationNativePrimitiveCosts.generation_bound source qGenerate generation) owners env)
  intro generated
  rcases generated with ⟨⟨generated, current⟩, environment⟩
  cases generated with
  | none => trivial
  | some credentials =>
      cases started : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error => simp only [StateT.run_pure]; trivial
      | div => simp only [StateT.run_pure]; trivial
      | ok pending =>
          cases requested : pending.request with
          | fail error => simp only [requested, StateT.run_pure]; trivial
          | div => simp only [requested, StateT.run_pure]; trivial
          | ok request =>
              simp only [requested, RegistrationNativeBeaconFrontend.hash, StateT.run_bind]
              apply weighted_bind _ _ _ _ _ (by
                cases kind <;> exact effect_bound source qKem _
                  (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))) current environment)
              intro digest
              rcases digest with ⟨⟨digest, afterHash⟩, afterEnvironment⟩
              cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
              | fail error => simp only [StateT.run_pure]; trivial
              | div => simp only [StateT.run_pure]; trivial
              | ok pin =>
                  cases pin with
                  | none => simp only [StateT.run_pure]; trivial
                  | some pin =>
                      simp only [StateT.run_bind]
                      apply weighted_bind _ _ _ _ _ (sample_bound source qKem kind _ 32 PqxdhJointIdentity.sampleSeed_uniform_bound afterHash afterEnvironment)
                      intro identity
                      rcases identity with ⟨⟨identity, afterIdentity⟩, identityEnvironment⟩
                      rw [← Nat.add_zero (coinCost 32 kind)]
                      apply weighted_bind _ _ _ _ _
                        (sample_bound source qKem kind _ 32 PqxdhJointGapDh.sampleScalar_uniform afterIdentity identityEnvironment)
                      intro prekey
                      trivial


/-- The admitted constructor suffix performs the real indexed key generation before one public owner allocation. -/
theorem append_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (qKem : Nat) (edPin : Std.Array U8 32#usize) (keyId : U64) (pin : session.ServerAuthenticationPin)
    (credentials : RegistrationNativeMldsa.Credential source) (identity : PqxdhJointIdentity.IdentitySeed)
    (prekey : PqxdhJointGapDh.ScalarBytes) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (kind : EffectKind) :
    Weighted (bill (n := n) qKem kind)
      (((RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId pin credentials identity prekey).run owners).run env)
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
      | some prepared => exact append_bound setup source qKem edPin keyId prepared.pin prepared.credentials prepared.identity prepared.prekey current environment kind

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
