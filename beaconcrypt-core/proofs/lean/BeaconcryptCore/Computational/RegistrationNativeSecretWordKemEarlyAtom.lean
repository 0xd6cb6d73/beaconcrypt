-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth

/-! Only the protected private handle and exact challenge ciphertext can return an opaque atom from decapsulation. Only the first matching exposed getter can return an atom from encapsulation; ordinary public encapsulation always returns a literal. These are concrete supported-provider transitions and do not assume a relationship between a roster position and a private handle. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom
open PqxdhKemIndCca
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordKemProvider (State ordinary pool)
open RegistrationNativeSecretWordKemEarly (early)
variable {ι KemSK : Type} {base : OracleSpec ι}

private theorem literal_ne_atom (value : Option MlKemSharedSecret) : Option.map Word.literal value ≠ some Word.atom := by
  cases value <;> simp

/-- An actual atom decapsulation is the protected current private handle on the exact challenge ciphertext, and that handle already exists in the active pool. -/
theorem decapsulate (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge ciphertext : MlKem768Ciphertext) (handle : Nat) (before after : State KemSK)
    (supported : (some Word.atom, after) ∈ support
      ((early baseImpl kem selected pairs publicKey challenge (.inr (.inl (.decapsulate handle ciphertext)))).run before)) :
    handle = selected ∧ ciphertext = challenge ∧ ∃ pair, before.1.keys[handle]? = some pair := by
  have normalized : (early baseImpl kem selected pairs publicKey challenge (.inr (.inl (.decapsulate handle ciphertext)))).run before =
      (fun answer => (answer, (RegistrationNativeSecretWordKemPool.record (.decapsulate handle ciphertext) answer before.1, before.2))) <$>
        (match before.1.keys[handle]? with
        | none => pure none
        | some pair => if handle = selected ∧ challenge = ciphertext then pure (some Word.atom)
            else Option.map Word.literal <$> simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.decaps pair.2 ciphertext)) := by
    rcases before with ⟨before, marker⟩
    cases marker <;> cases found : before.keys[handle]? <;>
      simp only [early, ordinary, pool, StateT.run, found, Option.some.injEq,
        bind_pure_comp, Functor.map_map]
    all_goals split <;> simp only [Functor.map_map, map_pure]
  rw [normalized, support_map] at supported
  obtain ⟨answer, called, returned⟩ := supported
  have reply : answer = some Word.atom := congrArg (fun result => result.1) returned
  cases found : before.1.keys[handle]? with
  | none =>
      simp only [found, mem_support_pure_iff] at called
      subst answer
      contradiction
  | some pair =>
      by_cases chosen : handle = selected ∧ challenge = ciphertext
      · exact ⟨chosen.1, chosen.2.symm, pair, rfl⟩
      · simp only [found, chosen, ite_false, support_map] at called
        obtain ⟨value, _sampled, equal⟩ := called
        exact (literal_ne_atom value (equal.trans reply)).elim

/-- An atom from the exposed getter is necessarily its first matching challenge reply. -/
theorem getter (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey key : MlKem768PublicKey)
    (challenge ciphertext : MlKem768Ciphertext) (before after : State KemSK)
    (supported : ((ciphertext, Word.atom), after) ∈ support
      ((early baseImpl kem selected pairs publicKey challenge (.inr (.inr key))).run before)) :
    before.2 = none ∧ key = publicKey ∧ ciphertext = challenge := by
  rcases before with ⟨before, marker⟩
  cases marker with
  | some value =>
      simp only [early, ordinary, StateT.run, support_map] at supported
      obtain ⟨reply, _called, equal⟩ := supported
      have impossible : Word.literal reply.2 = Word.atom := congrArg (fun result => result.1.2) equal
      cases impossible
  | none =>
      simp only [early, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨_dummy, _drawn, continued⟩ := supported
      by_cases matching : key = publicKey
      · simp only [matching, ite_true, pure_bind, mem_support_pure_iff] at continued
        exact ⟨rfl, matching, (congrArg (fun result => result.1.1) continued)⟩
      · simp only [matching, ite_false, bind_map_left, mem_support_bind_iff] at continued
        obtain ⟨reply, _called, returned⟩ := continued
        simp only [mem_support_pure_iff] at returned
        have impossible : Word.literal reply.2 = Word.atom := (congrArg (fun result => result.1.2) returned).symm
        cases impossible

/-- Ordinary public encapsulation never returns the protected opaque atom. -/
theorem public_getter (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey key : MlKem768PublicKey)
    (challenge ciphertext : MlKem768Ciphertext) (before after : State KemSK) :
    ((ciphertext, Word.atom), after) ∉ support
      ((early baseImpl kem selected pairs publicKey challenge (.inl (.inr key))).run before) := by
  intro supported
  rcases before with ⟨before, marker⟩
  cases marker <;> simp only [early, ordinary, StateT.run, support_map] at supported
  all_goals obtain ⟨reply, _called, equal⟩ := supported
  all_goals have impossible : Word.literal reply.2 = Word.atom := congrArg (fun result => result.1.2) equal
  all_goals cases impossible
end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom.decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom.decapsulate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom.getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom.getter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom.public_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyAtom.public_getter
