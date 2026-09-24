import BeaconcryptCore.Computational.PqxdhJointDhExtractRoot
import BeaconcryptCore.Computational.PqxdhProtocolAcceptance

/-!
The Server's ordered optional registration prefix, before extracted acceptance and root derivation. Raw field getters and attached verification are separate callbacks in their production order. Source parsing, curve admission, allocation, ephemeral generation, KEM encapsulation and conversions retain their original optional exits. Only the static-DH reply type is parameterized for a later unavailable-Server-seed compiler; all other DH/KEM material is actual local source data.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerRootPreparation
open PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhBeaconPhase2Preparation (Bytes Word32 Ciphertext)
open PqxdhRootTableInitialization (rootArray)

structure Ephemeral (E : Type) where
  secret : E
  publicKey : Word32

inductive Query (Reader E : Type) where
  | decode : Bytes → Query Reader E
  | identity : Reader → Query Reader E
  | identityPoint : Ed25519PublicKey → Query Reader E
  | pqField : Reader → Query Reader E
  | preField : Reader → Query Reader E
  | oneField : Reader → Query Reader E
  | verify : Ed25519PublicKey → Bytes → Query Reader E
  | registrationStatus : Bytes → Query Reader E
  | reserveRegistration : Query Reader E
  | parseDh : Word32 → Query Reader E
  | generate : Query Reader E
  | parseKem : MlKem768PublicKey → Query Reader E
  | encapsulate : MlKem768PublicKey → Query Reader E
  | publicConversion : Ed25519PublicKey → Query Reader E
  | privateConversion : Query Reader E
  | staticDh : Word32 → Query Reader E
  | ephemeralDh : E → Word32 → Query Reader E

abbrev Spec (Reader E Shared : Type) : OracleSpec (Query Reader E)
  | .decode _ => Option Reader
  | .identity _ | .pqField _ | .preField _ | .oneField _ | .verify _ _ => Option Bytes
  | .identityPoint _ | .reserveRegistration | .parseDh _ | .parseKem _ | .privateConversion => Bool
  | .registrationStatus _ => pqxdh.RegistrationStatus
  | .generate => Option (Ephemeral E)
  | .encapsulate _ => Option (Ciphertext × Word32)
  | .publicConversion _ | .ephemeralDh _ _ => Option Word32
  | .staticDh _ => Option Shared

/-- Full signed fields are retained alongside their actual verified typed payloads. -/
structure Verified (Reader : Type) where
  reader : Reader
  candidate : Phase1Candidate
  identity : Ed25519PublicKey
  keys : Phase1KeyTuple

/-- Identity width/tag admission and native point checks precede the PQ, prekey and one-time field/verification pairs. Core width/tag checks occur only after all three signatures succeed. -/
def verifyInput {Reader E Shared : Type} (raw : Bytes) :
    OracleComp (Spec Reader E Shared) (Option (Verified Reader)) := do
  let reader ← (Spec Reader E Shared).query (.decode raw)
  match reader with
  | none => pure none
  | some reader =>
    let encoded ← (Spec Reader E Shared).query (.identity reader)
    match encoded with
    | none => pure none
    | some encoded =>
      match parseIdentity encoded with
      | none => pure none
      | some identity =>
        let valid ← (Spec Reader E Shared).query (.identityPoint identity)
        if !valid then pure none else do
          let pqSigned ← (Spec Reader E Shared).query (.pqField reader)
          match pqSigned with
          | none => pure none
          | some pqSigned =>
            let pqPayload ← (Spec Reader E Shared).query (.verify identity pqSigned)
            match pqPayload with
            | none => pure none
            | some pqPayload =>
              let preSigned ← (Spec Reader E Shared).query (.preField reader)
              match preSigned with
              | none => pure none
              | some preSigned =>
                let prePayload ← (Spec Reader E Shared).query (.verify identity preSigned)
                match prePayload with
                | none => pure none
                | some prePayload =>
                  let oneSigned ← (Spec Reader E Shared).query (.oneField reader)
                  match oneSigned with
                  | none => pure none
                  | some oneSigned =>
                    let onePayload ← (Spec Reader E Shared).query (.verify identity oneSigned)
                    match onePayload with
                    | none => pure none
                    | some onePayload =>
                      pure (do
                        let prekey ← parsePrekeyMessage prePayload
                        let oneTime ← parseOneTimeMessage onePayload
                        let pqKey ← parsePqMessage pqPayload
                        pure ⟨reader, ⟨encoded, preSigned, oneSigned, pqSigned⟩, identity, ⟨prekey, oneTime, pqKey⟩⟩)

structure Inputs (Reader E Shared : Type) where
  verified : Verified Reader
  ephemeral : Ephemeral E
  ciphertext : Ciphertext
  convertedIdentity : Word32
  first : Shared
  second : Word32
  third : Word32
  fourth : Word32
  kem : Word32

/-- The source registration identifier is the exact identity/one-time concatenation, without a hash query. -/
def registrationId {Reader : Type} (verified : Verified Reader) : Bytes :=
  verified.identity.toList ++ verified.keys.oneTime.toList

/-- All source effects after typed verification occur in production order: freshness and reservation, two point constructors, ephemeral generation, KEM constructor and encapsulation, conversions, then DH1 through DH4. -/
def collectVerified {Reader E Shared : Type} (verified : Verified Reader) :
    OracleComp (Spec Reader E Shared) (Option (Inputs Reader E Shared)) := OptionT.run do
  let status ← (Spec Reader E Shared).query (.registrationStatus (registrationId verified))
  match status with
  | .Consumed => failure
  | .Fresh => do
    let reserved ← (Spec Reader E Shared).query .reserveRegistration
    if !reserved then failure else do
      let prekey := rootArray verified.keys.prekey
      let oneTime := rootArray verified.keys.oneTime
      let validPrekey ← (Spec Reader E Shared).query (.parseDh prekey)
      if !validPrekey then failure else do
        let validOneTime ← (Spec Reader E Shared).query (.parseDh oneTime)
        if !validOneTime then failure else do
          let ephemeral ← OptionT.mk ((Spec Reader E Shared).query .generate)
          let validKem ← (Spec Reader E Shared).query (.parseKem verified.keys.pqKey)
          if !validKem then failure else do
            let encapsulated ← OptionT.mk ((Spec Reader E Shared).query (.encapsulate verified.keys.pqKey))
            let converted ← OptionT.mk ((Spec Reader E Shared).query (.publicConversion verified.identity))
            let privateConverted ← (Spec Reader E Shared).query .privateConversion
            if !privateConverted then failure else do
              let first ← OptionT.mk ((Spec Reader E Shared).query (.staticDh prekey))
              let second ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret converted))
              let third ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret prekey))
              let fourth ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret oneTime))
              pure ⟨verified, ephemeral, encapsulated.1, converted, first, second, third, fourth, encapsulated.2⟩

/-- No cryptographic, allocation or freshness failure becomes a successful typed input. Every earlier callback effect remains in its original interpreter. -/
def collect {Reader E Shared : Type} (raw : Bytes) :
    OracleComp (Spec Reader E Shared) (Option (Inputs Reader E Shared)) := do
  let verified ← verifyInput raw
  match verified with
  | none => pure none
  | some verified => collectVerified verified

/-- Nine maximum source callbacks retain every getter and the three original verification positions. Pure width/tag rejection cannot add a callback. -/
theorem verifyInput_bound {Reader E Shared : Type} (raw : Bytes) :
    (verifyInput (Reader := Reader) (E := E) (Shared := Shared) raw).IsTotalQueryBound 9 := by
  unfold verifyInput
  repeat' first
    | trivial
    | (rw [isTotalQueryBound_query_bind_iff]; refine ⟨by decide, ?_⟩)
    | intro answer; cases answer
    | split

/-- Thirteen callbacks include the actual ephemeral/KEM generation and all early optional exits, with static DH after both conversions. -/
theorem collectVerified_bound {Reader E Shared : Type} (verified : Verified Reader) :
    (collectVerified (E := E) (Shared := Shared) verified).IsTotalQueryBound 13 := by
  unfold collectVerified
  simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | rw [isTotalQueryBound_query_bind_iff]
    | constructor
    | intro answer; cases answer

/-- Every raw prefix takes at most22 source callback slots, without filtering successful registration or cryptographic branches. -/
theorem collect_bound {Reader E Shared : Type} (raw : Bytes) :
    (collect (Reader := Reader) (E := E) (Shared := Shared) raw).IsTotalQueryBound 22 := by
  apply isTotalQueryBound_bind (verifyInput_bound raw) (n₂ := 13)
  rintro (_ | verified)
  · trivial
  · exact collectVerified_bound verified

end BeaconcryptCore.Computational.PqxdhServerRootPreparation

/-- info: 'BeaconcryptCore.Computational.PqxdhServerRootPreparation.verifyInput_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRootPreparation.verifyInput_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerRootPreparation.collectVerified_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRootPreparation.collectVerified_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerRootPreparation.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRootPreparation.collect_bound
