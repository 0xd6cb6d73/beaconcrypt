-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhPhase2DhMetadata

/-! The actual selected-DH Beacon collector uses its decapsulated shared secret only in the retained root-input field. All later DH callbacks, optional exits, assigned ID and metadata admission are independent of its value. These finite source equations support opaque KEM words without changing the actual controller order or pin checks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrefix
open PqxdhBeaconPhase2Preparation (Bytes Word32 Ciphertext)
open PqxdhPhase2GapDhSource (PrefixSpec Inputs)
variable {I D K X Response : Type}

def setShared (shared : Word32) (inputs : Inputs Response) : Inputs Response := { inputs with shared := shared }

structure Header (X Response : Type) where
  response : Response
  ciphertext : Ciphertext
  ephemeral : Word32
  server : Word32
  serverConverted : Word32
  identityConverted : X

def beforeDecap (identity : I) (raw : Bytes) : OracleComp (PrefixSpec I D K X Response) (Option (Header X Response)) := OptionT.run do
  let response ← OptionT.mk ((PrefixSpec I D K X Response).query (.decode raw))
  let ciphertext ← OptionT.mk ((PrefixSpec I D K X Response).query (.ciphertext response))
  let ephemeral ← OptionT.mk ((PrefixSpec I D K X Response).query (.ephemeral response))
  let server ← OptionT.mk ((PrefixSpec I D K X Response).query (.serverIdentity response))
  let converted ← OptionT.mk ((PrefixSpec I D K X Response).query (.publicConversion server))
  let identityConverted ← OptionT.mk ((PrefixSpec I D K X Response).query (.privateConversion identity))
  pure ⟨response, ciphertext, ephemeral, server, converted, identityConverted⟩

def afterDecap (oneTime : D) (header : Header X Response) (shared : Word32) :
    OracleComp (PrefixSpec I D K X Response) (Option (Inputs Response)) := OptionT.run do
  let first ← OptionT.mk ((PrefixSpec I D K X Response).query (.selected header.serverConverted))
  let second ← OptionT.mk ((PrefixSpec I D K X Response).query (.dhIdentity header.identityConverted header.ephemeral))
  let third ← OptionT.mk ((PrefixSpec I D K X Response).query (.selected header.ephemeral))
  let fourth ← OptionT.mk ((PrefixSpec I D K X Response).query (.dhPair oneTime header.ephemeral))
  let assigned ← liftM ((PrefixSpec I D K X Response).query (.assignedId header.response))
  pure ⟨header.response, header.ciphertext, header.ephemeral, header.server, header.serverConverted,
    assigned, first, second, third, fourth, shared⟩

/-- The actual native collector has its original six-callback prefix, one decapsulation, and the exact shared-value-independent suffix. -/
theorem collect_split (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    PqxdhPhase2GapDhSource.collect (X := X) (Response := Response) identity oneTime kem raw =
      (do
        let initial ← beforeDecap identity raw
        match initial with
        | none => pure none
        | some header =>
            let shared ← (PrefixSpec I D K X Response).query (.decapsulate header.ciphertext kem)
            match shared with
            | none => pure none
            | some shared => afterDecap oneTime header shared) := by
  simp only [PqxdhPhase2GapDhSource.collect, beforeDecap, afterDecap, OptionT.run_bind,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_assoc]
  repeat' first
    | rfl
    | (congr 1; funext reply; cases reply)
    | (simp only [Option.elim_some, pure_bind, bind_assoc])

/-- Changing the actual decapsulation value changes only the retained shared-secret field, with every optional DH failure and callback unchanged. -/
theorem afterDecap_frame (oneTime : D) (header : Header X Response) (first second : Word32) :
    afterDecap (I := I) (K := K) oneTime header second =
      Option.map (setShared second) <$> afterDecap (I := I) (K := K) oneTime header first := by
  simp only [afterDecap, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
    Option.elimM, map_bind]
  repeat' first
    | rfl
    | (congr 1; funext reply; cases reply)
    | (simp only [Option.elim_some, map_bind, ])

/-- Actual raw pin equality, local DH zero checks, assigned ID and populated associated data do not inspect the decapsulated secret. -/
theorem admitted_setShared (control : beaconcrypt_core.pqxdh.BeaconInitSent) (inputs : Inputs Response) (shared : Word32) :
    PqxdhPhase2DhMetadata.admitted control (setShared shared inputs) = PqxdhPhase2DhMetadata.admitted control inputs := rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrefix.collect_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrefix.collect_split
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrefix.afterDecap_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrefix.afterDecap_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrefix.admitted_setShared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrefix.admitted_setShared
