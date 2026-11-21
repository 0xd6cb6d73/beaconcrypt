-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerGetter
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCompiler

/-! The actual symbolic Beacon collector reads its authenticated response literally. These finite callback equations retain the full current environment and every original public conversion request. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordBeaconCompiler (prefixImpl ordinaryPrefix)
open PqxdhBeaconPhase2Preparation (Word32)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Decoding in the ordered collector retains the actual prior mandatory-authentication result. -/
theorem decode (setup : Setup base KemSK) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (raw : Pqxdh.Bytes) (before : EnvState Auxiliary) :
    (prefixImpl (n := n) setup owner oneTime authenticated (.decode raw)).run before = pure (some authenticated, before) := by
  rfl

/-- The collector's ciphertext is the literal authenticated packet field. -/
theorem ciphertext (setup : Setup base KemSK) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated response : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    (prefixImpl (n := n) setup owner oneTime authenticated (.ciphertext response)).run before =
      pure (some response.packet.public.kem_cipher_text, before) := by
  rfl

/-- The collector's first-DH pin operand is the literal authenticated Server identity field. -/
theorem serverIdentity (setup : Setup base KemSK) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated response : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    (prefixImpl (n := n) setup owner oneTime authenticated (.serverIdentity response)).run before =
      pure (some response.packet.public.identity_key, before) := by
  rfl

/-- Public conversion is the original source conversion and retains its actual request log. -/
theorem publicConversion (setup : Setup base KemSK) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (key : Word32) (before : EnvState Auxiliary) :
    (prefixImpl (n := n) setup owner oneTime authenticated (.publicConversion key)).run before =
      pure (RegistrationAgreementRoot.option (RegistrationPublicConversion.convert setup.source.crypto key),
        { before with requests := before.requests ++ RegistrationWorldAgreement.recorded (.convertPublic key) }) := by
  rfl
/-- The authenticated ephemeral operand is retained literally before any private KEM callback. -/
theorem ephemeral (setup : Setup base KemSK) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated response : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    (prefixImpl (n := n) setup owner oneTime authenticated (.ephemeral response)).run before =
      pure (some response.packet.public.ephemeral_key, before) := by
  rfl

/-- The actual locally owned identity conversion has its source validity and original request log. -/
theorem privateConversion (setup : Setup base KemSK) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    (prefixImpl (n := n) setup owner oneTime authenticated (.privateConversion ())).run before =
      pure ((if RegistrationServerRoleBackend.selectedConversion setup.source.crypto (setup.secretOfSeed owner.identitySeed) then some () else none),
        { before with requests := before.requests ++ RegistrationWorldAgreement.recorded (.convertSecret .LocalIdentity) }) := by
  rfl

/-- The entire six-callback public prefix is a literal pure optional header, retaining both conversion requests and the actual authenticated packet. -/
theorem beforeDecap (setup : Setup base KemSK) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((simulateQ (prefixImpl (n := n) setup owner oneTime authenticated)
      (simulateQ RegistrationNativeSecretWordBeaconCollect.ordinary
        (RegistrationNativeSecretWordBeaconPrefix.beforeDecap () []))).run before) =
      pure (match RegistrationAgreementRoot.option (RegistrationPublicConversion.convert setup.source.crypto authenticated.packet.public.identity_key) with
        | none => (none, { before with requests := before.requests ++ RegistrationWorldAgreement.recorded (.convertPublic authenticated.packet.public.identity_key) })
        | some converted =>
          ((if RegistrationServerRoleBackend.selectedConversion setup.source.crypto (setup.secretOfSeed owner.identitySeed) then
            some ⟨authenticated, authenticated.packet.public.kem_cipher_text, authenticated.packet.public.ephemeral_key,
              authenticated.packet.public.identity_key, converted, ()⟩ else none),
            { before with requests := (before.requests ++ RegistrationWorldAgreement.recorded (.convertPublic authenticated.packet.public.identity_key)) ++
              RegistrationWorldAgreement.recorded (.convertSecret .LocalIdentity) })) := by
  simp only [RegistrationNativeSecretWordBeaconPrefix.beforeDecap, OptionT.run_bind, OptionT.run_mk,
    OptionT.run_pure, Option.elimM, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativeSecretWordBeaconCollect.ordinary, StateT.run_bind]
  rw [decode setup owner oneTime authenticated [] before]
  simp only [pure_bind, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativeSecretWordBeaconCollect.ordinary, StateT.run_bind]
  rw [ciphertext]
  simp only [pure_bind, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativeSecretWordBeaconCollect.ordinary, StateT.run_bind]
  rw [ephemeral]
  simp only [pure_bind, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativeSecretWordBeaconCollect.ordinary, StateT.run_bind]
  rw [serverIdentity]
  simp only [pure_bind, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativeSecretWordBeaconCollect.ordinary, StateT.run_bind]
  rw [publicConversion]
  simp only [pure_bind]
  cases converted : RegistrationAgreementRoot.option (RegistrationPublicConversion.convert setup.source.crypto authenticated.packet.public.identity_key) with
  | none => simp only [Option.elim_none, simulateQ_pure, StateT.run_pure]
  | some key =>
      simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeSecretWordBeaconCollect.ordinary, StateT.run_bind]
      rw [privateConversion]
      simp only [pure_bind]
      split <;> simp only [Option.elim_none, Option.elim_some, simulateQ_pure, StateT.run_pure]
/-- Successful public-prefix interpretation retains the exact authenticated header and the source public-conversion equation. -/
theorem header (setup : Setup base KemSK) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before after : EnvState Auxiliary)
    (value : RegistrationNativeSecretWordBeaconPrefix.Header Unit registration.AuthenticatedResponse)
    (supported : (some value, after) ∈ support
      ((simulateQ (prefixImpl (n := n) setup owner oneTime authenticated)
        (simulateQ RegistrationNativeSecretWordBeaconCollect.ordinary
          (RegistrationNativeSecretWordBeaconPrefix.beforeDecap () []))).run before)) :
    value.response = authenticated ∧ value.ciphertext = authenticated.packet.public.kem_cipher_text ∧
      value.server = authenticated.packet.public.identity_key ∧
      setup.source.crypto.xpkConv (absBytes value.server) = some (absBytes value.serverConverted) := by
  rw [beforeDecap] at supported
  cases converted : RegistrationAgreementRoot.option (RegistrationPublicConversion.convert setup.source.crypto authenticated.packet.public.identity_key) with
  | none => simp only [converted, mem_support_pure_iff] at supported; cases supported
  | some key =>
      simp only [converted] at supported
      split at supported
      · simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at supported
        obtain ⟨rfl, rfl⟩ := supported
        refine ⟨rfl, rfl, rfl, ?_⟩
        apply RegistrationPublicConversion.convert_sound
        cases actual : RegistrationPublicConversion.convert setup.source.crypto authenticated.packet.public.identity_key <;>
          simp only [RegistrationAgreementRoot.option, actual, Option.some.injEq] at converted
        all_goals cases converted
        rfl
      · rw [mem_support_pure_iff] at supported
        cases supported
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.decode
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.ciphertext
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.serverIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.serverIdentity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.publicConversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.publicConversion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.ephemeral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.ephemeral
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.privateConversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.privateConversion
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.beforeDecap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.beforeDecap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix.header
