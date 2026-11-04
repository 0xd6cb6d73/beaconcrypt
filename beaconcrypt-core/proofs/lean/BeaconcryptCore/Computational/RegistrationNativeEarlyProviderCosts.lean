-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyRealSource
import BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts

/-! The actual early candidate provider inherits only primitive keygen/encapsulation/decapsulation byte-query costs. Reserved creation and missing-handle branches retain zero-query replies, while the original first exposed getter retains its actual32-byte discard draw. No desired provider or callback bound is supplied. -/

open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeEarlyProviderCosts
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
variable {ι KemSK : Type} {base : OracleSpec ι}

def providerBill (qKeygen qEncap qDecap : Nat) := 32 + (qKeygen + qEncap + qDecap)

set_option backward.isDefEq.respectTransparency false in
private theorem pool_bound (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (qKeygen qDecap : Nat)
    (keygen : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (decap : ∀ key ciphertext, (simulateQ (kemAmbientImpl baseImpl) (kem.decaps key ciphertext)).IsTotalQueryBound qDecap)
    (query : PqxdhLiveKemBirth.Query) (before : PqxdhLiveKemBirth.Pool KemSK) :
    ((PqxdhLiveKemBirth.poolImpl baseImpl kem query).run before).IsTotalQueryBound (qKeygen + qDecap) := by
  cases query with
  | create =>
      simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
      exact keygen.mono (Nat.le_add_right _ _)
  | reveal handle => trivial
  | decapsulate handle ciphertext =>
      simp only [PqxdhLiveKemBirth.poolImpl, StateT.run]
      cases before.keys[handle]? with
      | none => trivial
      | some pair =>
          exact (isTotalQueryBound_bind (decap pair.2 ciphertext)
            (fun _ => show (pure _ : ProbComp _).IsTotalQueryBound 0 from by trivial)).mono (by omega)

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_bound (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (qKeygen qEncap qDecap : Nat)
    (keygen : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encap : ∀ key, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)).IsTotalQueryBound qEncap)
    (decap : ∀ key ciphertext, (simulateQ (kemAmbientImpl baseImpl) (kem.decaps key ciphertext)).IsTotalQueryBound qDecap)
    (pairs : List (MlKem768PublicKey × KemSK))
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain)
    (before : PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) :
    ((RegistrationNativeOpenKeyKemEarlyRealSource.ordinaryProvider baseImpl kem pairs query).run before).IsTotalQueryBound
      (qKeygen + qEncap + qDecap) := by
  rcases query with (ordinary | publicKey) | (pool | publicKey)
  · cases ordinary <;> trivial
  · simp only [RegistrationNativeOpenKeyKemEarlyRealSource.ordinaryProvider, RegistrationNativeKemReservation.reserved,
      RegistrationNativeKemInterface.source, RegistrationNativeSecretWordKemProvider.ambient,
      RegistrationNativeKemRouting.publicAmbient, StateT.run, StateT.lift, bind_pure_comp,
      IsTotalQueryBound, isQueryBound_map_iff]
    exact (encap publicKey).mono (n₂ := qKeygen + qEncap + qDecap) (by omega)
  · cases pool with
    | create =>
        simp only [RegistrationNativeOpenKeyKemEarlyRealSource.ordinaryProvider, RegistrationNativeKemReservation.reserved,
          StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
        cases pairs[before.1.keys.length]? with
        | some pair => trivial
        | none =>
            simp only [RegistrationNativeKemInterface.source, StateT.run, isQueryBound_map_iff]
            exact (pool_bound baseImpl kem qKeygen qDecap keygen decap .create before.1).mono (by omega)
    | decapsulate handle ciphertext =>
        simp only [RegistrationNativeOpenKeyKemEarlyRealSource.ordinaryProvider, RegistrationNativeKemReservation.reserved,
          RegistrationNativeKemInterface.source, StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
        exact (pool_bound baseImpl kem qKeygen qDecap keygen decap (.decapsulate handle ciphertext) before.1).mono (by omega)
    | reveal handle => trivial
  · simp only [RegistrationNativeOpenKeyKemEarlyRealSource.ordinaryProvider, RegistrationNativeKemReservation.reserved,
      RegistrationNativeKemInterface.source, StateT.run, StateT.lift, bind_pure_comp,
      IsTotalQueryBound, isQueryBound_map_iff]
    exact (encap publicKey).mono (n₂ := qKeygen + qEncap + qDecap) (by omega)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual early-provider request has a literal primitive-derived bill, on arbitrary reserved pools and before/after the exposed getter. -/
theorem provider_bound (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (qKeygen qEncap qDecap : Nat)
    (keygen : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encap : ∀ key, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)).IsTotalQueryBound qEncap)
    (decap : ∀ key ciphertext, (simulateQ (kemAmbientImpl baseImpl) (kem.decaps key ciphertext)).IsTotalQueryBound qDecap)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain)
    (before : PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) :
    ((RegistrationNativeOpenKeyKemEarlyRealSource.provider baseImpl kem pairs publicKey challenge candidate query).run before).IsTotalQueryBound
      (providerBill qKeygen qEncap qDecap) := by
  rcases query with (ordinary | key) | (pool | key)
  all_goals cases phase : before.2 with
    | some value =>
        simp only [RegistrationNativeOpenKeyKemEarlyRealSource.provider, StateT.run, phase]
        exact (ordinary_bound baseImpl kem qKeygen qEncap qDecap keygen encap decap pairs _ before).mono (by unfold providerBill; omega)
    | none =>
        simp only [RegistrationNativeOpenKeyKemEarlyRealSource.provider, StateT.run, phase]
        first
          | exact (ordinary_bound baseImpl kem qKeygen qEncap qDecap keygen encap decap pairs _ before).mono (by unfold providerBill; omega)
          | apply isTotalQueryBound_bind (n₁ := 32) (n₂ := qKeygen + qEncap + qDecap)
            · exact CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32
            · intro discarded
              apply IsTotalQueryBound.mono (n₁ := qEncap + 0) _ (by omega)
              split
              · trivial
              · exact isTotalQueryBound_bind (encap _) (fun _ => by trivial)

end BeaconcryptCore.Computational.RegistrationNativeEarlyProviderCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEarlyProviderCosts.provider_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEarlyProviderCosts.provider_bound
