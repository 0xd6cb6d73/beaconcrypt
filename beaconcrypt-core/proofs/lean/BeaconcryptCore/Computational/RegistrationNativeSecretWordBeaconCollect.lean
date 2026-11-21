-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconPrefix
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage

/-! The executable Beacon collector retains the actual selected-DH references and stores only an opaque KEM word. It runs the original public prefix and shared-value-independent suffix, with a dummy shared value in the private plain record. Evaluation restores only that field and recovers the entire actual collector AST. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect
open PqxdhBeaconPhase2Preparation (Bytes Word32)
open PqxdhPhase2GapDhSource (Query PrefixSpec Inputs)
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordBeaconPrefix (Header beforeDecap afterDecap setShared)
variable {I D K X Response : Type}

abbrev Spec (I D K X Response : Type) : OracleSpec (Query I D K X Response)
  | .decapsulate _ _ => Option Word
  | query => (PrefixSpec I D K X Response).Range query

def zero : Word32 := PqxdhRootTableInitialization.rootArray RegistrationNativeSecretWordMessage.zero

structure Input (Response : Type) where
  plain : Inputs Response
  kem : Word

def eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : Input Response) : Inputs Response :=
  setShared (PqxdhRootTableInitialization.rootArray (input.kem.eval candidate)) input.plain

def ordinary : QueryImpl (PrefixSpec I D K X Response) (OracleComp (Spec I D K X Response))
  | .decapsulate _ _ => pure none
  | .decode raw => (Spec I D K X Response).query (.decode raw)
  | .ciphertext response => (Spec I D K X Response).query (.ciphertext response)
  | .ephemeral response => (Spec I D K X Response).query (.ephemeral response)
  | .serverIdentity response => (Spec I D K X Response).query (.serverIdentity response)
  | .publicConversion key => (Spec I D K X Response).query (.publicConversion key)
  | .privateConversion identity => (Spec I D K X Response).query (.privateConversion identity)
  | .dhPair pair key => (Spec I D K X Response).query (.dhPair pair key)
  | .dhIdentity identity key => (Spec I D K X Response).query (.dhIdentity identity key)
  | .selected point => (Spec I D K X Response).query (.selected point)
  | .assignedId response => (Spec I D K X Response).query (.assignedId response)
  | .eraseShared secrets => (Spec I D K X Response).query (.eraseShared secrets)

def realize (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (PrefixSpec I D K X Response) (OracleComp (Spec I D K X Response))
  | .decapsulate ciphertext kem => Option.map (fun word => PqxdhRootTableInitialization.rootArray (Word.eval candidate word)) <$>
      (Spec I D K X Response).query (.decapsulate ciphertext kem)
  | query => ordinary query

def collect (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    OracleComp (Spec I D K X Response) (Option (Input Response)) := do
  let initial ← simulateQ ordinary (beforeDecap identity raw)
  match initial with
  | none => pure none
  | some header =>
      let shared ← (Spec I D K X Response).query (.decapsulate header.ciphertext kem)
      match shared with
      | none => pure none
      | some shared =>
          Option.map (fun plain => (⟨plain, shared⟩ : Input Response)) <$>
            simulateQ ordinary (afterDecap oneTime header zero)

/-- The original six-callback prefix reaches no decapsulation and therefore has the literal same actual interpretation for every candidate. -/
theorem prefix_source (candidate : PqxdhKemIndCca.MlKemSharedSecret) (identity : I) (raw : Bytes) :
    simulateQ (realize candidate) (beforeDecap (D := D) (K := K) (X := X) (Response := Response) identity raw) =
      simulateQ ordinary (beforeDecap (D := D) (K := K) (X := X) (Response := Response) identity raw) := by
  simp only [beforeDecap, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, Option.elimM,
    simulateQ_bind, simulateQ_spec_query, realize]
  repeat' (
    try simp only [Option.elim_some, Option.elim_none, simulateQ_bind, simulateQ_pure, simulateQ_spec_query, realize]
    first | rfl | (congr 1; funext reply; cases reply))
  all_goals rfl

/-- The actual remaining DH/assigned-ID suffix forwards every callback and restores only its retained shared field. -/
theorem suffix_source (candidate : PqxdhKemIndCca.MlKemSharedSecret) (oneTime : D) (header : Header X Response) (shared : Word32) :
    simulateQ (realize candidate) (afterDecap (I := I) (K := K) oneTime header shared) =
      Option.map (setShared shared) <$> simulateQ ordinary (afterDecap (I := I) (K := K) oneTime header zero) := by
  rw [RegistrationNativeSecretWordBeaconPrefix.afterDecap_frame oneTime header zero shared, simulateQ_map]
  congr 1
  simp only [afterDecap, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM,
    simulateQ_bind, simulateQ_spec_query, realize]
  repeat' (
    try simp only [Option.elim_some, Option.elim_none, simulateQ_bind, simulateQ_map,
      simulateQ_pure, simulateQ_spec_query, realize]
    first | rfl | (congr 1; funext reply; cases reply))
  all_goals rfl

/-- Evaluating the retained opaque word reconstructs the literal entire native collector with every optional failure and reached callback effect. -/
theorem collect_realization (candidate : PqxdhKemIndCca.MlKemSharedSecret) (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    simulateQ (realize candidate) (PqxdhPhase2GapDhSource.collect (X := X) (Response := Response) identity oneTime kem raw) =
      Option.map (eval candidate) <$> collect identity oneTime kem raw := by
  rw [RegistrationNativeSecretWordBeaconPrefix.collect_split]
  simp only [simulateQ_bind, prefix_source, collect, map_bind]
  apply bind_congr
  intro initial
  cases initial with
  | none => simp only [simulateQ_pure, map_pure, Option.map_none]
  | some header =>
      simp only [simulateQ_bind, simulateQ_spec_query, realize, bind_map_left, map_bind]
      apply bind_congr
      intro shared
      cases shared with
      | none => simp only [simulateQ_pure, map_pure, Option.map_none]
      | some word =>
          simp only [Option.map_some]
          rw [suffix_source]
          simp only [Functor.map_map, eval, Function.comp_def, Option.map_map]

/-- An arbitrary subsequent source interpreter retains the entire reached state in the concrete symbolic collector equation. -/
theorem collect_program {m : Type → Type} [Monad m] [LawfulMonad m]
    (implementation : QueryImpl (Spec I D K X Response) m) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    simulateQ (implementation ∘ₛ realize candidate)
      (PqxdhPhase2GapDhSource.collect (X := X) (Response := Response) identity oneTime kem raw) =
      Option.map (eval candidate) <$> simulateQ implementation (collect identity oneTime kem raw) := by
  rw [QueryImpl.simulateQ_compose, collect_realization, simulateQ_map]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect.prefix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect.prefix_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect.suffix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect.suffix_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect.collect_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect.collect_realization
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect.collect_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect.collect_program
