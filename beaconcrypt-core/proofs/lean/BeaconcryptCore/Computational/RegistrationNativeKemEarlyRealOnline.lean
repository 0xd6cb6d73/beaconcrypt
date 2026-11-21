-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyOnline

/-! The actual reserved real KEM pool executes the unchanged whole native client with its real selected decapsulations. An explicit independently presampled selected first-getter reply is intercepted online, retaining the complete actual pool and auxiliary transcript. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemEarlyRealOnline
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemReservation (reserved)
open RegistrationNativeKemCut (Cut scan)
open RegistrationNativeKemEarlyGame (intercept)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

abbrev BaseState (Auxiliary KemSK : Type) := Auxiliary × PqxdhLiveKemBirth.Pool KemSK
abbrev State (Auxiliary KemSK : Type) := BaseState Auxiliary KemSK × RegistrationNativeKemSwitchSource.Phase

def carry {Reply : Type} (marker : RegistrationNativeKemSwitchSource.Phase)
    (result : Reply × BaseState Auxiliary KemSK) : Reply × State Auxiliary KemSK :=
  (result.1, (result.2, marker))

noncomputable def online (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    QueryImpl (Spec ambient KemSK) (StateT (State Auxiliary KemSK) ProbComp) := fun query before =>
  match query, before.2 with
  | .inr (.inr key), none => do
      let _ ← $ᵗ MlKemSharedSecret
      let reply ← if key = publicKey then pure (challenge, candidate)
        else simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)
      pure (reply, (before.1, some (challenge, candidate)))
  | query, _ => carry before.2 <$> (reserved baseImpl kem other pairs query).run before.1

/-- After the first getter, arbitrary continuations retain the exact original candidate-pool result and full auxiliary/pool history; the private marker remains literal. -/
theorem post_program (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (marker : MlKem768Ciphertext × MlKemSharedSecret) (work : OracleComp (Spec ambient KemSK) Value)
    (before : BaseState Auxiliary KemSK) :
    (simulateQ (online baseImpl kem other pairs publicKey challenge candidate) work).run (before, some marker) =
      carry (some marker) <$> (simulateQ (reserved baseImpl kem other pairs) work).run before := by
  let embed : BaseState Auxiliary KemSK → State Auxiliary KemSK := fun state => (state, some marker)
  have query : ∀ query state, Prod.map id embed <$>
      (reserved baseImpl kem other pairs query).run state =
      (online baseImpl kem other pairs publicKey challenge candidate query).run (embed state) := by
    intro query state
    rcases query with query | query | key <;> rfl
  change _ = Prod.map id embed <$> _
  exact (OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ embed query work before).symm

private theorem intercept_pure (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (value : Bool) :
    intercept (ambient := ambient) (KemSK := KemSK) publicKey challenge candidate (pure value) = pure value := rfl

private theorem intercept_other (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : ambient.Domain)
    (next : ambient.Range query → OracleComp (Spec ambient KemSK) Bool) :
    intercept publicKey challenge candidate (((Spec ambient KemSK).query (.inl query) : OracleComp (Spec ambient KemSK) _) >>= next) =
      ((Spec ambient KemSK).query (.inl query) : OracleComp (Spec ambient KemSK) _) >>= fun reply => intercept publicKey challenge candidate (next reply) := by
  unfold intercept RegistrationNativeKemGame.expose
  rw [RegistrationNativeKemCut.scan_other, bind_assoc]

private theorem intercept_pool (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : PqxdhLiveKemBirth.Query)
    (next : (PqxdhLiveKemBirth.PoolSpec KemSK).Range query → OracleComp (Spec ambient KemSK) Bool) :
    intercept publicKey challenge candidate (((Spec ambient KemSK).query (.inr (.inl query)) : OracleComp (Spec ambient KemSK) _) >>= next) =
      ((Spec ambient KemSK).query (.inr (.inl query)) : OracleComp (Spec ambient KemSK) _) >>= fun reply => intercept publicKey challenge candidate (next reply) := by
  unfold intercept RegistrationNativeKemGame.expose
  rw [RegistrationNativeKemCut.scan_pool, bind_assoc]

private theorem intercept_getter (publicKey key : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret)
    (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Bool) :
    intercept publicKey challenge candidate (((Spec ambient KemSK).query (.inr (.inr key)) : OracleComp (Spec ambient KemSK) _) >>= next) =
      if key = publicKey then next (challenge, candidate)
      else ((Spec ambient KemSK).query (.inr (.inr key)) : OracleComp (Spec ambient KemSK) _) >>= next := by
  unfold intercept RegistrationNativeKemGame.expose
  rw [RegistrationNativeKemCut.scan_target, pure_bind]
  rfl

private theorem post_erase (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (marker : MlKem768Ciphertext × MlKemSharedSecret) (work : OracleComp (Spec ambient KemSK) Value)
    (before : BaseState Auxiliary KemSK) :
    Prod.map id Prod.fst <$> (simulateQ (online baseImpl kem other pairs publicKey challenge candidate) work).run (before, some marker) =
      (simulateQ (reserved baseImpl kem other pairs) work).run before := by
  rw [post_program]
  simp only [Functor.map_map, carry, Prod.map_def, id_eq, Prod.mk.eta, id_map']

private theorem online_other_run (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (query : ambient.Domain)
    (before : BaseState Auxiliary KemSK) :
    (online baseImpl kem other pairs publicKey challenge candidate (.inl query)).run (before, none) =
      carry none <$> (reserved baseImpl kem other pairs (.inl query)).run before := rfl

private theorem online_pool_run (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (query : PqxdhLiveKemBirth.Query)
    (before : BaseState Auxiliary KemSK) :
    (online baseImpl kem other pairs publicKey challenge candidate (.inr (.inl query))).run (before, none) =
      carry none <$> (reserved baseImpl kem other pairs (.inr (.inl query))).run before := rfl

private theorem online_getter_run (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey key : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (before : BaseState Auxiliary KemSK) :
    (online baseImpl kem other pairs publicKey challenge candidate (.inr (.inr key))).run (before, none) = (do
      let _ ← $ᵗ MlKemSharedSecret
      let reply ← if key = publicKey then pure (challenge, candidate)
        else simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)
      pure (reply, (before, some (challenge, candidate)))) := rfl

private theorem reserved_getter_run (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pairs : List (MlKem768PublicKey × KemSK)) (key : MlKem768PublicKey)
    (_challenge : MlKem768Ciphertext) (_candidate : MlKemSharedSecret) (before : BaseState Auxiliary KemSK) :
    (reserved baseImpl kem other pairs (.inr (.inr key))).run before = (do
      let reply ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)
      pure (reply, before)) := rfl

/-- The unchanged whole native program can execute online from the initial getter marker. Erasing only that private marker gives the ordinary early-CCA intercepted source, with every auxiliary effect, indexed key and reply transcript retained. -/
theorem program_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (Spec ambient KemSK) Bool) (before : BaseState Auxiliary KemSK) :
    (Prod.map id Prod.fst <$> (simulateQ (online baseImpl kem other pairs publicKey challenge candidate) work).run (before, none)) =ᵈ
      (simulateQ (reserved baseImpl kem other pairs)
        (intercept publicKey challenge candidate work)).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [intercept_pure, simulateQ_pure, StateT.run_pure, map_pure]
    exact .rfl
  | query_bind query next ih =>
    rcases query with query | (query | key)
    · rw [intercept_other]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, online_other_run,
        bind_map_left, map_bind, carry]
      exact _root_.EvalDistEq.bind_right _ (fun reached => ih reached.1 reached.2)
    · rw [intercept_pool]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, online_pool_run,
        bind_map_left, map_bind, carry]
      exact _root_.EvalDistEq.bind_right _ (fun reached => ih reached.1 reached.2)
    · rw [intercept_getter]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, online_getter_run, bind_assoc,
        map_bind, pure_bind]
      by_cases matching : key = publicKey
      · simp only [matching, ite_true, pure_bind, post_erase]
        exact OracleComp.EvalDistEq.bind_const ($ᵗ MlKemSharedSecret : ProbComp MlKemSharedSecret) _
      · simp only [matching, ite_false, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          reserved_getter_run, bind_assoc, pure_bind, post_erase]
        exact OracleComp.EvalDistEq.bind_const ($ᵗ MlKemSharedSecret : ProbComp MlKemSharedSecret) _


end BeaconcryptCore.Computational.RegistrationNativeKemEarlyRealOnline
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyRealOnline.post_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyRealOnline.post_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyRealOnline.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyRealOnline.program_source
