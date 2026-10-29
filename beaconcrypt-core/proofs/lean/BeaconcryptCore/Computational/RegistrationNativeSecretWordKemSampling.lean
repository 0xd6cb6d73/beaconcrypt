-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemProviderPrefix
import BeaconcryptCore.Computational.RegistrationNativeSampledMonad

/-! Delaying the independent selected KEM word is compatible with the exact original native sampler instrumentation. The original counted32-byte draw remains at its getter position; the early mathematical candidate is never charged to the shared World. All genuine encapsulation work and later public encapsulation branches retain their actual draws and complete World. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordKemSampling
open PqxdhKemIndCca
open PqxdhRecordLiftWorld (sampled)
open RegistrationNativeSecretWordKemProvider (evalState evalReply provider reference)
variable {n : Nat} {Value First ι KemSK : Type} {base : OracleSpec ι}

/-- An early independent shared secret replaces only the value used by the continuation; the exact native32-byte dummy draw and full World remain at their original point. -/
theorem eager (first : ProbComp First) (before : PqxdhRecordLiftWorld.State n)
    (next : First → MlKemSharedSecret → PqxdhRecordLiftWorld.State n → ProbComp Value) :
    (do let initial ← (sampled first).run before
        let selected ← (sampled ($ᵗ MlKemSharedSecret)).run initial.2
        next initial.1 selected.1 selected.2) =ᵈ
      (do let candidate ← $ᵗ MlKemSharedSecret
          let initial ← (sampled first).run before
          let dummy ← (sampled ($ᵗ MlKemSharedSecret)).run initial.2
          next initial.1 candidate dummy.2) := by
  refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap
    ((sampled first).run before) ($ᵗ MlKemSharedSecret)
    (fun initial candidate => do
      let dummy ← (sampled ($ᵗ MlKemSharedSecret)).run initial.2
      next initial.1 candidate dummy.2))
  apply _root_.EvalDistEq.bind_right
  intro initial
  exact RegistrationNativeSampling.scalar_eager initial.2 (next initial.1)

private theorem reference_first (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey key : MlKem768PublicKey)
    (pool : PqxdhLiveKemBirth.Pool KemSK) :
    (reference baseImpl kem selected pairs publicKey (.inr (.inr key))).run (pool, none) = (do
      let pair ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps publicKey)
      let candidate ← $ᵗ MlKemSharedSecret
      let reply ← if key = publicKey then pure (pair.1, candidate)
        else simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps key)
      pure (reply, (pool, some (pair.1, candidate)))) := by
  by_cases matching : key = publicKey <;>
    simp only [reference, RegistrationNativeKemSwitchReserved.source, StateT.run,
      Bool.false_eq_true, matching, ite_true, ite_false, map_bind, map_pure, pure_bind]

private theorem provider_first (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey key : MlKem768PublicKey)
    (pool : RegistrationNativeSecretWordKemPool.Pool KemSK) :
    (provider baseImpl kem selected pairs publicKey (.inr (.inr key))).run (pool, none) = (do
      let pair ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps publicKey)
      let _ ← $ᵗ MlKemSharedSecret
      let reply ← if key = publicKey then pure (pair.1, RegistrationNativeSecretWord.Word.atom)
        else Prod.map id RegistrationNativeSecretWord.Word.literal <$>
          simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps key)
      pure (reply, (pool, some pair.1))) := rfl

/-- The actual first selected getter has its exact counted eager-word interpretation, including a mismatched getter and the private dummy challenge phase. No condition on getter activation is assumed. -/
theorem first_getter (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey key : MlKem768PublicKey)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (world : PqxdhRecordLiftWorld.State n) :
    ((sampled ((reference baseImpl kem selected pairs publicKey (.inr (.inr key))).run (pool, none))).run world) =ᵈ
      (do let candidate ← $ᵗ MlKemSharedSecret
          (fun result : ((MlKem768Ciphertext × RegistrationNativeSecretWord.Word) × RegistrationNativeSecretWordKemProvider.State KemSK) × PqxdhRecordLiftWorld.State n => ((evalReply candidate (.inr (.inr key)) result.1.1, evalState candidate result.1.2), result.2)) <$>
            (sampled ((provider baseImpl kem selected pairs publicKey (.inr (.inr key))).run
              (RegistrationNativeSecretWordKemPoolLiteral.literal pool, none))).run world) := by
  by_cases matching : key = publicKey
  all_goals rw [reference_first, provider_first]
  all_goals simp only [matching, ite_true, ite_false]
  all_goals simp only [RegistrationNativeSampledMonad.bind, RegistrationNativeSampledMonad.pure, bind_map_left, map_bind, map_pure, pure_bind,
    evalReply, evalState, Option.map_some, Prod.map_def, id_eq,
    RegistrationNativeSecretWordKemPoolLiteral.eval_literal, RegistrationNativeSecretWord.Word.eval]
  all_goals simpa only [matching, ite_true, ite_false, RegistrationNativeSampledMonad.pure, pure_bind, Prod.mk.eta] using (eager (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps publicKey)) world
    (fun pair candidate current => do
      let reply ← (sampled (if key = publicKey then pure (pair.1, candidate)
        else simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps key))).run current
      pure ((reply.1, (pool, some (pair.1, candidate))), reply.2)))

end BeaconcryptCore.Computational.RegistrationNativeSecretWordKemSampling
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemSampling.eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemSampling.eager

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordKemSampling.first_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordKemSampling.first_getter
