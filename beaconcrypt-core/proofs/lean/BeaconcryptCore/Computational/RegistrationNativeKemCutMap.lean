-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource

/-! Native getter cuts retain complete original observations before a Boolean security decision is applied. This permits structural receipts for the original ledger and reached private source state inside the candidate hybrid. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCutMap
open PqxdhKemIndCca
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemCut (Cut scan)
variable {κ KemSK Value Result : Type} {ambient : OracleSpec κ}

def map (function : Value → Result) : Cut ambient KemSK Value → Cut ambient KemSK Result
  | .complete value => .complete (function value)
  | .pending key next => .pending key (fun reply => function <$> next reply)

/-- Taking the actual native getter cut preserves the entire original result under any later observation. -/
theorem scan_map {m : Type → Type} [Monad m] [LawfulMonad m]
    (implementation : QueryImpl (Spec ambient KemSK) m)
    (work : OracleComp (Spec ambient KemSK) Value) (function : Value → Result) (index : Nat) :
    scan implementation (function <$> work) index = map function <$> scan implementation work index := by
  induction work using OracleComp.inductionOn generalizing index with
  | pure value =>
      simp only [map_pure]
      change pure (Cut.complete (function value)) = map function <$> pure (Cut.complete value)
      rw [map_pure]
      rfl
  | query_bind query next ih =>
      rw [map_bind]
      rcases query with query | (query | key)
      · simp only [RegistrationNativeKemCut.scan_other, map_bind, ih]
      · simp only [RegistrationNativeKemCut.scan_pool, map_bind, ih]
      · cases index with
        | zero =>
            simp only [RegistrationNativeKemCut.scan_target, map_pure, map]
            rfl
        | succ index => simp only [RegistrationNativeKemCut.scan_prior, map_bind, ih]

def resume (publicKey : MlKem768PublicKey) (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    Option (Cut ambient KemSK Value) → OracleComp (Spec ambient KemSK) (Option Value)
  | none => pure none
  | some (.complete value) => pure (some value)
  | some (.pending key next) => some <$> (if key = publicKey then next (ciphertext, candidate)
      else (Spec ambient KemSK).query (.inr (.inr key)) >>= next)

def observe (decision : Value → Bool) (value : Option Value) : Bool := (value.map decision).getD false

/-- The full original observation determines the same total native Boolean continuation, including aborts, completed cuts and unmatched getters. -/
theorem resume_observe (decision : Value → Bool) (publicKey : MlKem768PublicKey)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (cut : Option (Cut ambient KemSK Value)) :
    RegistrationNativeKemTotalGame.continuation publicKey ciphertext candidate (cut.map (map decision)) =
      observe decision <$> resume publicKey ciphertext candidate cut := by
  cases cut with
  | none => rfl
  | some cut =>
      cases cut with
      | complete value => rfl
      | pending key next =>
          by_cases matching : key = publicKey
          · simp only [Option.map_some, map, RegistrationNativeKemTotalGame.continuation,
              resume, matching, ite_true, Functor.map_map]
            rfl
          · simp only [Option.map_some, map, RegistrationNativeKemTotalGame.continuation,
              resume, matching, ite_false, map_bind, Functor.map_map]
            rfl

end BeaconcryptCore.Computational.RegistrationNativeKemCutMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCutMap.scan_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCutMap.scan_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCutMap.resume_observe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCutMap.resume_observe
