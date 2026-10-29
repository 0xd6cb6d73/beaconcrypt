-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyOnline

/-! The complete early candidate KEM source retains the actual lazy108 table under a literal state reassociation. The same external provider is closed through the key compiler's real coin surface; the challenge substitution is active at genuine selected-handle birth and the first-getter marker remains private. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlySource
open PqxdhKemIndCca
open RegistrationNativeOpenKey (Spec Ambient)
open RegistrationNativeOpenKeyKemGame (Table other)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Before (KemSK : Type) := (Table × PqxdhLiveKemBirth.Pool KemSK) × RegistrationNativeKemSwitchSource.Phase

def embed (before : Before KemSK) :
    (PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) × Table :=
  ((before.1.2, before.2), before.1.1)

noncomputable def implementation (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    QueryImpl (Spec KemSK) (StateT (Before KemSK) ProbComp) :=
  RegistrationNativeKemEarlyOnline.online baseImpl kem (other baseImpl kem) selected pairs publicKey challenge candidate ∘ₛ
    RegistrationNativeOpenKey.native

noncomputable def reference (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    QueryImpl (Spec KemSK)
      (StateT ((PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) × Table) ProbComp) :=
  (PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase
    (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins
      (RegistrationNativeSecretWordKemEarly.actual baseImpl kem selected pairs publicKey challenge candidate))).flattenStateT

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem coin_program (work : ProbComp Value) (table : Table) :
    (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
      (simulateQ RegistrationNativeKeyCompiler.coins work)).run table =
      (fun value => (value, table)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : PqxdhRegistrationJointKemSecondEntry.lazyImpl ∘ₛ RegistrationNativeKeyCompiler.coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Table ProbComp) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, table)) = _
  exact bind_pure_comp _ _

/-- Every actual early-candidate callback retains the full lazy table, indexed pool transcript and getter marker under the explicit reassociation. -/
theorem query_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (query : (Spec KemSK).Domain)
    (before : Before KemSK) :
    Prod.map id embed <$> (implementation baseImpl kem selected pairs publicKey challenge candidate query).run before =
      (reference baseImpl kem selected pairs publicKey challenge candidate query).run (embed before) := by
  rcases before with ⟨⟨table, pool⟩, marker⟩
  simp only [implementation, QueryImpl.apply_compose, reference,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, embed]
  cases query with
  | inl query =>
      simp only [RegistrationNativeOpenKey.native, simulateQ_spec_query,
        RegistrationNativeKemEarlyOnline.online, RegistrationNativeKemEarlyOnline.carry,
        RegistrationNativeKemCandidateReserved.reserved, RegistrationNativeKemReservation.reserved,
        RegistrationNativeKemInterface.source, other, RegistrationNativeOpenCompile.close,
        bind_pure_comp, simulateQ_map, simulateQ_spec_query,
        StateT.run, StateT.lift, state_map_apply, Functor.map_map, Prod.map_def, id_eq, embed]
      rfl
  | inr query =>
      change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
          (simulateQ RegistrationNativeKeyCompiler.coins
            ((RegistrationNativeSecretWordKemEarly.actual baseImpl kem selected pairs publicKey challenge candidate query).run
              (pool, marker)))).run table
      rw [coin_program]
      rcases query with (query | key) | query | key
      all_goals try cases query
      all_goals cases marker <;>
        simp only [RegistrationNativeOpenKey.native, simulateQ_spec_query,
          RegistrationNativeKemEarlyOnline.online, RegistrationNativeKemEarlyOnline.carry,
          RegistrationNativeSecretWordKemEarly.actual, RegistrationNativeSecretWordKemEarly.actualOrdinary,
          RegistrationNativeKemCandidateReserved.reserved, RegistrationNativeKemReservation.reserved,
          RegistrationNativeKemInterface.source, other, RegistrationNativeSecretWordKemProvider.ambient,
          RegistrationNativeKemRouting.publicAmbient, StateT.run, StateT.lift,
          bind_pure_comp, Functor.map_map, map_bind, map_pure, Prod.map_def, id_eq, embed]
      all_goals repeat' (split <;> simp_all only [Functor.map_map, map_pure])
      case inr.inr.inl.decapsulate.none handle ciphertext =>
        cases found : pool.keys[handle]? <;> simp only [map_pure]
        by_cases chosen : handle = selected ∧ ciphertext = challenge <;>
          simp only [chosen, and_self, ite_true, ite_false, map_pure, Functor.map_map]
      case inr.inr.inl.decapsulate.some handle ciphertext marker =>
        cases found : pool.keys[handle]? <;> simp only [map_pure]
        by_cases chosen : handle = selected ∧ ciphertext = challenge <;>
          simp only [chosen, and_self, ite_true, ite_false, map_pure, Functor.map_map]
      all_goals rfl
/-- Arbitrary complete native work retains its exact result, lazy key table, indexed history and getter marker under the same reassociation. -/
theorem program_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (work : OracleComp (Spec KemSK) Value)
    (before : Before KemSK) :
    Prod.map id embed <$> (simulateQ (implementation baseImpl kem selected pairs publicKey challenge candidate) work).run before =
      (simulateQ (reference baseImpl kem selected pairs publicKey challenge candidate) work).run (embed before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ embed
    (query_source baseImpl kem selected pairs publicKey challenge candidate) work before

/-- Any complete client observation has the same exact source distribution before and after closing the actual early candidate provider. -/
theorem values_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (work : OracleComp (Spec KemSK) Value)
    (before : Before KemSK) :
    (simulateQ (implementation baseImpl kem selected pairs publicKey challenge candidate) work).run' before =
      (simulateQ (reference baseImpl kem selected pairs publicKey challenge candidate) work).run' (embed before) := by
  have mapped := congrArg (Functor.map Prod.fst)
    (program_source baseImpl kem selected pairs publicKey challenge candidate work before)
  simpa only [StateT.run'_eq, Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using mapped

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlySource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlySource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlySource.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlySource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlySource.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlySource.values_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlySource.values_source
