import BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer

/-!
# The ideal-key branch with the message key first or last (item 2, stage S6)

The ideal-key branch `PqxdhRegistrationJointKemIdealKeys.idealKeysBranch` (H4 of the item 2 plan) draws entry 0's 108 uniform bytes `(key32 ‖ next32 ‖ nonce12, right32)` at once and runs entry 0's distinguisher `entryD` on them. Item 4 (the CTX lift) needs the 32-byte message key `key32` as a separate challenger value. This module restates H4 with the key drawn as a separate value, before or after the 76-byte residual `(nonce12, next32, right32)` (`PqxdhServerAuthCtxMaterial.Residual`), in both cases before the whole game, as equalities of output distributions:

- `idealKeys_key_first`: the key is drawn first, then the residual, and `entryD` runs on the reassembled 108 bytes (`PqxdhServerAuthCtxMaterial.output`); this is `PqxdhServerAuthCtxMaterial.key_first`. The key comes before everything else, the order of the challenger key of `AdaptiveCtxDynamicKnownKeys.sourceGame`; the draw is written `$ᵗ RootOutput`, as in `key_first`, not `$ᵗ CtxKey`; both types are reducible abbreviations of `List.Vector UInt8 32` (`CtxKey` is `FixedBytes 32`), so a consumer shaped like `sourceGame` passes from one draw to the other by unfolding them, as `PqxdhServerAuthCtxExperiment.stopped_game` does;
- `idealKeys_key_last`: the residual is drawn first and the key after it, both before `entryD` runs. This is not the shape of `PqxdhAdaptiveMessageKeySource.firstPrepare`/`firstIdeal`, which sample the source context first and the key after it: here the prechallenge context is sampled inside `entryD`, after both draws;
- `authenticated_key_first` and `authenticated_key_last`: theorem T8 (`PqxdhRegistrationJointKemKeyTransfer.authenticated_ideal_keys`) with the ideal-key branch in either form.

`nonce12`, `next32` and `right32` stay private simulator data of the distinguisher; the statements say nothing about the independence of an arbitrary source context from the key beyond these distribution equalities. They are equalities and charge nothing.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (RootOutput)
open PqxdhFullSecretInputKdf (SourceFullCorrect)
open PqxdhServerAuthCtxMaterial (Residual output)
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemEntryFactor (entryD)
open PqxdhRegistrationJointKemIdealKeys (idealKeysBranch)
open PqxdhRegistrationJointKemKeyTransfer (idealKeysLoss)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The ideal-key branch with entry 0's 108 bytes drawn as the 32-byte message key first and the 76-byte residual after it. -/
noncomputable def keyFirstBranch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : ProbComp Bool := do
  let key ← $ᵗ RootOutput
  let rest ← $ᵗ Residual
  entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
    (output key rest)

/-- The ideal-key branch with entry 0's 108 bytes drawn as the 76-byte residual first and the 32-byte message key after it, both before `entryD` runs (not the `firstPrepare`/`firstIdeal` shape, whose key follows the source context). -/
noncomputable def keyLastBranch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : ProbComp Bool := do
  let rest ← $ᵗ Residual
  let key ← $ᵗ RootOutput
  entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
    (output key rest)

/-- Stage S6, key first: the ideal-key branch has the output distribution of the game that draws the 32-byte message key before everything else. -/
theorem idealKeys_key_first (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    𝒟[idealKeysBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index] =
      𝒟[keyFirstBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index] :=
  (PqxdhServerAuthCtxMaterial.key_first
    (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index)).evalDist_eq

/-- The key-first and the key-last games have the same output distribution. -/
theorem keyFirst_keyLast (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    𝒟[keyFirstBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index] =
      𝒟[keyLastBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index] :=
  (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ RootOutput) ($ᵗ Residual) (fun key rest =>
    entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
      (output key rest))).evalDist_eq

/-- Stage S6, key last: the ideal-key branch has the output distribution of the game that draws the 32-byte message key after the 76-byte residual, both before `entryD` runs. -/
theorem idealKeys_key_last (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    𝒟[idealKeysBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index] =
      𝒟[keyLastBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index] :=
  (idealKeys_key_first setup codec checks ensureInit supplied decision work runtime count selected index).trans
    (keyFirst_keyLast setup codec checks ensureInit supplied decision work runtime count selected index)

/-- Theorem T8 with the ideal-key branch in key-first shape. One-sided because T5 is; not a secrecy theorem. -/
theorem authenticated_key_first (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (decision : X → Bool) (kemIndex : Fin (count + 1)) (chosenOwner : Nat) (fallback : Pqxdh.Bytes)
    (dynamicFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (letI := Classical.propDecidable; 𝒟[(fun pair =>
        decide (PqxdhRegistrationJointKemRawBridge.Decided decision
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointAcceptOrigin.Protected setup codec checks kemIndex pair.1)) <$>
      PqxdhRegistrationJointAcceptCutReports.split setup codec checks ensureInit supplied (count + 1) work index
        runtime] {true}) ≤
    𝒟[keyFirstBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count kemIndex
        index] {true} +
      ENNReal.ofReal (setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work runtime
          count kemIndex index).toINDCCA +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) +
      ∑ target : Fin (count + 1), advantage setup.joint
        (PqxdhRegistrationJointNativeOriginBound.reduction setup codec checks ensureInit supplied count
          (PqxdhRegistrationJointAcceptCut.selected work index chosenOwner fallback) runtime
          dynamicFallback ordinaryFallback target) +
      ENNReal.ofReal (idealKeysLoss (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        kemIndex index budget) := by
  rw [← idealKeys_key_first]
  exact PqxdhRegistrationJointKemKeyTransfer.authenticated_ideal_keys setup functional codec checks shortRejects
    ensureInit supplied count work runtime index budget certified capacity decision kemIndex chosenOwner fallback
    dynamicFallback ordinaryFallback correct

/-- Theorem T8 with the ideal-key branch in key-last shape. One-sided because T5 is; not a secrecy theorem. -/
theorem authenticated_key_last (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (decision : X → Bool) (kemIndex : Fin (count + 1)) (chosenOwner : Nat) (fallback : Pqxdh.Bytes)
    (dynamicFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (letI := Classical.propDecidable; 𝒟[(fun pair =>
        decide (PqxdhRegistrationJointKemRawBridge.Decided decision
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointAcceptOrigin.Protected setup codec checks kemIndex pair.1)) <$>
      PqxdhRegistrationJointAcceptCutReports.split setup codec checks ensureInit supplied (count + 1) work index
        runtime] {true}) ≤
    𝒟[keyLastBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count kemIndex
        index] {true} +
      ENNReal.ofReal (setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work runtime
          count kemIndex index).toINDCCA +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) +
      ∑ target : Fin (count + 1), advantage setup.joint
        (PqxdhRegistrationJointNativeOriginBound.reduction setup codec checks ensureInit supplied count
          (PqxdhRegistrationJointAcceptCut.selected work index chosenOwner fallback) runtime
          dynamicFallback ordinaryFallback target) +
      ENNReal.ofReal (idealKeysLoss (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        kemIndex index budget) := by
  rw [← idealKeys_key_last]
  exact PqxdhRegistrationJointKemKeyTransfer.authenticated_ideal_keys setup functional codec checks shortRejects
    ensureInit supplied count work runtime index budget certified capacity decision kemIndex chosenOwner fallback
    dynamicFallback ordinaryFallback correct

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst.idealKeys_key_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst.idealKeys_key_first

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst.keyFirst_keyLast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst.keyFirst_keyLast

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst.idealKeys_key_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst.idealKeys_key_last

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst.authenticated_key_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst.authenticated_key_first

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst.authenticated_key_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyFirst.authenticated_key_last
