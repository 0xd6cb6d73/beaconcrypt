-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySymbolicCtx
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture

/-! A new hidden-address token can be installed after an arbitrary legal prefix without giving its physical address to the executable client. Construction copies only its existing known-input cache/journal and starts none empty. The no-recognition receipt justifies that private reindexing changes no earlier cached answer. The complete guarded source coupling retains actual CTX draw costs and source journal, and its loss is the returned recognition witness event. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTokenInstall
open PqxdhEd25519EufCma (Ed25519PublicKey Ed25519Signature)
open RegistrationNativeIdentitySymbolicCtx (ByteCache Cache State HashSpec unitCache realize)
open RegistrationNativeIdentityRecognitionCapture (capture)
variable {Value : Type}

/-- This constructor does not receive the hidden address or its signature. -/
def install (cache : ByteCache) (journal : List Pqxdh.Bytes) : State :=
  (⟨fun input => input.bind cache⟩, journal.map some)

/-- The no-recognition cache-miss receipt makes installation exactly preserve the real reached cache and full input journal. -/
theorem initial (hidden : Pqxdh.Bytes) (cache : ByteCache) (journal : List Pqxdh.Bytes) (fresh : cache hidden = none) :
    realize hidden (install cache journal) = (unitCache cache, journal) := by
  have table : RegistrationNativeIdentitySymbolicRom.project hidden (install cache journal).1 = cache := by
    apply QueryCache.ext
    intro input
    by_cases same : input = hidden
    · subst input
      simpa only [RegistrationNativeIdentitySymbolicRom.project, RegistrationNativeIdentitySymbolicRom.abstractAddress,
        ite_true, install, Option.bind_none] using fresh.symm
    · simp only [RegistrationNativeIdentitySymbolicRom.project, RegistrationNativeIdentitySymbolicRom.abstractAddress,
        same, ite_false, install, Option.bind_some]
  change (unitCache (RegistrationNativeIdentitySymbolicRom.project hidden (install cache journal).1),
    (install cache journal).2.map (RegistrationNativeIdentitySymbolicRom.address hidden)) = _
  rw [table]
  change (unitCache cache, (journal.map some).map (RegistrationNativeIdentitySymbolicRom.address hidden)) = _
  rw [List.map_map]
  change (unitCache cache, journal.map id) = (unitCache cache, journal)
  rw [List.map_id]

def recognize (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) : Option Pqxdh.Bytes → Option Ed25519Signature
  | none => none
  | some input => RegistrationNativeIdentityRecognition.recognize verify publicKey message input

private theorem guarded (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message leading trailing : Pqxdh.Bytes) (signature : Ed25519Signature)
    (valid : verify publicKey message signature = true) (work : OracleComp HashSpec Value) :
    AllQueriesSatisfy (capture (recognize verify publicKey message) work)
      (fun input => input ≠ some (leading ++ signature.toList ++ trailing)) := by
  apply (RegistrationNativeIdentityRecognitionCapture.submitted (recognize verify publicKey message) work).mono
  intro input missing same
  rw [same] at missing
  have detected := RegistrationNativeIdentityRecognition.template_recognized verify publicKey message leading trailing signature valid
  simp only [recognize] at missing
  rw [missing] at detected
  contradiction

/-- Any actual adaptive hash continuation can use the newly installed token; public recognition discharges forbidden-address submission structurally. -/
theorem source (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message leading trailing : Pqxdh.Bytes) (signature : Ed25519Signature)
    (valid : verify publicKey message signature = true) (work : OracleComp HashSpec Value)
    (cache : ByteCache) (journal : List Pqxdh.Bytes) (fresh : cache (leading ++ signature.toList ++ trailing) = none) :
    Prod.map id (realize (leading ++ signature.toList ++ trailing)) <$>
      (simulateQ RegistrationNativeIdentitySymbolicCtx.implementation
        (capture (recognize verify publicKey message) work)).run (install cache journal) =
      (simulateQ (fun input => RegistrationNativePlatformCtxBackend.physical
        (RegistrationNativeIdentitySymbolicRom.address (leading ++ signature.toList ++ trailing) input))
        (capture (recognize verify publicKey message) work)).run (unitCache cache, journal) := by
  have coupled := RegistrationNativeIdentitySymbolicCtx.program (leading ++ signature.toList ++ trailing)
    (capture (recognize verify publicKey message) work) (guarded verify publicKey message leading trailing signature valid work) (install cache journal)
  rw [initial _ cache journal fresh] at coupled
  exact coupled

/-- The literal physical continuation's event is covered by successful symbolic execution or actual extracted signature bytes. The fresh-cache condition is supplied by the earlier same-run no-recognition receipt, not by assuming source/game equality. -/
theorem loss (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message leading trailing : Pqxdh.Bytes) (signature : Ed25519Signature)
    (valid : verify publicKey message signature = true) (work : OracleComp HashSpec Value)
    (cache : ByteCache) (journal : List Pqxdh.Bytes) (fresh : cache (leading ++ signature.toList ++ trailing) = none)
    (event : Value × RegistrationNativePlatformCtxBackend.State → Prop) :
    Pr{let result ← (simulateQ (fun input => RegistrationNativePlatformCtxBackend.physical
      (RegistrationNativeIdentitySymbolicRom.address (leading ++ signature.toList ++ trailing) input)) work).run (unitCache cache, journal)}[event result] ≤
      Pr{let result ← (simulateQ RegistrationNativeIdentitySymbolicCtx.implementation
        (capture (recognize verify publicKey message) work)).run (install cache journal)}[∃ witness, result.1 = .inl witness] +
      Pr{let result ← (simulateQ RegistrationNativeIdentitySymbolicCtx.implementation
        (capture (recognize verify publicKey message) work)).run (install cache journal)}[
          ∃ value, result.1 = .inr value ∧ event (value, realize (leading ++ signature.toList ++ trailing) result.2)] := by
  have upper := RegistrationNativeIdentityRecognitionCapture.cover
    (fun input => RegistrationNativePlatformCtxBackend.physical
      (RegistrationNativeIdentitySymbolicRom.address (leading ++ signature.toList ++ trailing) input))
    (recognize verify publicKey message) work event (unitCache cache, journal)
  rw [← source verify publicKey message leading trailing signature valid work cache journal fresh] at upper
  simpa only [prEvent_map, Prod.map_def, id_eq] using upper

end BeaconcryptCore.Computational.RegistrationNativeIdentityTokenInstall
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTokenInstall.initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTokenInstall.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTokenInstall.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTokenInstall.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTokenInstall.loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTokenInstall.loss
