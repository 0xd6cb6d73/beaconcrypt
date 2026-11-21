-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource

/-! The native candidate source can execute the complete original program directly. Its private phase changes at the first exposed getter, sampling the challenge pair and candidate there. Before that getter every indexed decapsulation is real; afterwards the exact created selected handle/ciphertext rule applies. The additional phase retains no protocol state of its own. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSwitchSource
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (State)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

abbrev Phase := Option (MlKem768Ciphertext × MlKemSharedSecret)
abbrev Switched (Auxiliary KemSK : Type) := State Auxiliary KemSK × Phase

def carry {Reply : Type} (phase : Phase) (result : Reply × State Auxiliary KemSK) : Reply × Switched Auxiliary KemSK :=
  (result.1, (result.2, phase))

def post (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    QueryImpl (Spec ambient KemSK) (OptionT (StateT (Switched Auxiliary KemSK) ProbComp)) := fun query =>
  OptionT.mk fun before => carry before.2 <$>
    (((RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs challenge candidate query).run).run before.1)

def source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool) :
    QueryImpl (Spec ambient KemSK) (OptionT (StateT (Switched Auxiliary KemSK) ProbComp)) := fun query =>
  OptionT.mk fun before => match before.2 with
  | some pair => ((post baseImpl kem other selected pairs pair.1 pair.2 query).run).run before
  | none => match query with
      | .inr (.inr key) => do
          let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)
          let uniform ← $ᵗ MlKemSharedSecret
          let candidate := if real then pair.2 else uniform
          let reply ← if key = publicKey then pure (pair.1, candidate)
            else simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)
          pure (some reply, (before.1, some (pair.1, candidate)))
      | query => carry none <$>
          (((RegistrationNativeKemGame.stopped baseImpl kem other selected pairs query).run).run before.1)

/-- After the private switch, the full program is exactly the explicit candidate source, retaining every base-state coordinate. -/
theorem post_program (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    (((simulateQ (source baseImpl kem other selected pairs publicKey real) work).run).run (before, some (challenge, candidate))) =
      carry (some (challenge, candidate)) <$>
        (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs challenge candidate) work).run).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind]
      simp only [source, OptionT.run_mk, StateT.run, post, bind_map_left, map_bind, carry]
      congr 1
      funext result
      rcases result with ⟨none | reply, after⟩
      · rfl
      · exact ih reply after

end BeaconcryptCore.Computational.RegistrationNativeKemSwitchSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchSource.post_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchSource.post_program
