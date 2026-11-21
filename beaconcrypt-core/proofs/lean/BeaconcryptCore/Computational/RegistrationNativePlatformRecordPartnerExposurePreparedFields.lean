-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxClosed
import BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand
/-! Actual native demand never changes preparation flags, and every other interpreter leaf has its literal flag update. These source metadata receipts retain all failed material, cache and World outcomes. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeRelatedFamily (Message)
open PqxdhRecordLiftInterface (EnvEffects WorldSpec)
open RegistrationNativePairedChoice (Choice)
variable {n : Nat} {I KemSK ProviderState : Type} {base : OracleSpec I}

private theorem reserve_fields (bytes : Pqxdh.Bytes) (before : RegistrationNativeHiddenService.State n) :
    (RegistrationNativeHiddenService.reserve bytes before).2.prepared=before.prepared := by
  unfold RegistrationNativeHiddenService.reserve
  split
  · rfl
  · split <;> rfl

/-- Every native hidden-demand outcome retains the same preparation map, including capacity refusal and absent preparation. -/
theorem hidden_demand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Pqxdh.Bytes) (inside : Pqxdh.Bytes →Bool) (message : Message)
    (before after : RegistrationNativeHiddenService.State n) (reply : Option (Choice n))
    (supported : (reply,after)∈support ((RegistrationNativeHiddenService.demand source input inside message).run before)) :
    after.prepared=before.prepared := by
  simp only [RegistrationNativeHiddenService.demand,StateT.run] at supported
  split at supported
  · cases realized : input message with
    | none=>simp only [realized,mem_support_pure_iff] at supported;cases supported;rfl
    | some bytes=>
      simp only [realized] at supported
      split at supported
      · cases allocated : RegistrationNativeHiddenService.reserve bytes {before with demands:=before.demands+1} with
        | mk slot middle=>
          have fields := reserve_fields bytes {before with demands:=before.demands+1}
          rw [allocated] at fields
          simp only [allocated] at supported
          cases slot with
          | none=>simp only [mem_support_pure_iff] at supported;cases supported;exact fields
          | some slot=>
            simp only [support_map] at supported
            obtain ⟨⟨material,final⟩,called,equal⟩ := supported
            cases equal
            exact (RegistrationNativeHiddenServiceDemand.material_fields slot middle final material called).1.trans fields
      · simp only [mem_support_pure_iff] at supported;cases supported;rfl
  · simp only [mem_support_pure_iff] at supported;cases supported;rfl

private theorem known_fields (bytes : Pqxdh.Bytes) (before after : RegistrationNativeSelectiveHiddenService.State n)
    (reply : PqxdhServerAuthKeySchedule.Output)
    (supported : (reply,after)∈support ((RegistrationNativeSelectiveHiddenService.known bytes).run before)) :
    after.1.prepared=before.1.prepared := by
  simp only [RegistrationNativeSelectiveHiddenService.known,StateT.run] at supported
  split at supported
  · simp only [mem_support_pure_iff] at supported;cases supported;rfl
  · simp only [support_map] at supported
    obtain ⟨output,_draw,equal⟩ := supported
    cases equal
    rfl

/-- Selective known108 and hidden44 demand branches preserve the identical native preparation map. -/
theorem selective_demand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Pqxdh.Bytes) (inside : Pqxdh.Bytes →Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message)
    (before after : RegistrationNativeSelectiveHiddenService.State n) (reply : Option (Choice n))
    (supported : (reply,after)∈support ((RegistrationNativeSelectiveHiddenService.demand source input inside candidate message).run before)) :
    after.1.prepared=before.1.prepared := by
  simp only [RegistrationNativeSelectiveHiddenService.demand,StateT.run] at supported
  split at supported
  · cases realized : input message with
    | none=>
      simp only [realized,RegistrationNativeSelectiveHiddenService.onHidden,StateT.run,support_map] at supported
      obtain ⟨reached,called,equal⟩ := supported
      cases equal
      exact hidden_demand source input _ message before.1 reached.2 reached.1 called
    | some bytes=>
      simp only [realized] at supported
      split at supported
      · simp only [support_map] at supported
        obtain ⟨reached,called,equal⟩ := supported
        cases equal
        exact known_fields bytes ({before.1 with demands:=before.1.demands+1},before.2) reached.2 reached.1 called
      · simp only [RegistrationNativeSelectiveHiddenService.onHidden,StateT.run,support_map] at supported
        obtain ⟨reached,called,equal⟩ := supported
        cases equal
        exact hidden_demand source input _ message before.1 reached.2 reached.1 called
  · simp only [RegistrationNativeSelectiveHiddenService.onHidden,StateT.run,support_map] at supported
    obtain ⟨reached,called,equal⟩ := supported
    cases equal
    exact hidden_demand source input _ message before.1 reached.2 reached.1 called

def next (input : Message →Option Pqxdh.Bytes) (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (flags : Message →Bool) : Message →Bool :=
  match query with
  | .inl (.inl message)=>Function.update flags message (input message).isSome
  | _=>flags

private theorem lift_apply {S A : Type} {m : Type →Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before=(fun value=>(value,before)) <$>work := bind_pure_comp _ _

/-- Every literal native selective-interpreter query has exactly its source-defined preparation-field update. -/
theorem native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query ×RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (supported : result∈support ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query).run before)) :
    result.2.1.keys.prepared=next (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) query before.1.keys.prepared := by
  rcases query with (message|(message|(publication|effect))|kem)|record
  · simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.onKeys,RegistrationNativeHiddenService.prepare,
      StateT.run,simulateQ_pure,map_pure,mem_support_pure_iff] at supported
    cases supported
    rfl
  · simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onKeys,
      StateT.run,support_map] at supported
    obtain ⟨reached,called,equal⟩ := supported
    cases equal
    have original := PqxdhDeploymentEnvironment.support_simulateQ_subset PqxdhRecordLiftInterface.effectLift _ called
    exact selective_demand setup.source _ _ candidate message (before.1.keys,before.2) reached.2 reached.1 original
  · simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.publication,StateT.run,Functor.map_map,support_map] at supported
    obtain ⟨reached,called,equal⟩ := supported
    cases equal
    rfl
  · simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.effect,StateT.run,lift_apply,Functor.map_map,support_map] at supported
    obtain ⟨reached,_called,equal⟩ := supported
    cases equal
    rfl
  · simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.routed,StateT.run,Functor.map_map,support_map] at supported
    obtain ⟨reached,_called,equal⟩ := supported
    cases equal
    rfl
  · simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler,StateT.run,lift_apply,Functor.map_map,support_map] at supported
    obtain ⟨reached,_called,equal⟩ := supported
    cases equal
    rfl


variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (OracleComp (WorldSpec n)))
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey ×KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
local notation "provider"=>RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "actualProvider"=>RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate
local notation "symbolic"=>RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused provider

/-- Exact source query correspondence retains the very native preparation map inside the symbolic private frame. -/
theorem source_query (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK)
    (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query ×RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK)
    (supported : result∈support ((symbolic query).run before)) :
    result.2.2.1.prepared=next (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativePlatformLorCtxLeaves.nativeQuery candidate query) before.2.1.prepared := by
  have actual : (RegistrationNativePlatformLorCtxLeaves.nativeReply candidate query result.1,
      RegistrationNativePlatformLorCtxLeaves.frame candidate result.2)∈support
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate actualProvider
        (RegistrationNativePlatformLorCtxLeaves.nativeQuery candidate query)).run
        (RegistrationNativePlatformLorCtxLeaves.frame candidate before)) := by
    rw [←RegistrationNativePlatformLorCtxLeaves.query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge query before,support_map]
    exact Set.mem_image_of_mem _ supported
  exact native setup wire sign seed scalar candidate actualProvider _ _ _ actual

variable {Physical : Type} (physical : QueryImpl (WorldSpec n) (StateT Physical ProbComp))
/-- An arbitrary persistent physical closing retains the same native preparation field through every original Word query. -/
theorem closed (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK ×Physical)
    (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query ×(RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK ×Physical))
    (supported : result∈support ((RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical query).run before)) :
    result.2.1.2.1.prepared=next (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativePlatformLorCtxLeaves.nativeQuery candidate query) before.1.2.1.prepared := by
  rw [RegistrationNativePlatformLorCtxClosed.implementation,QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨⟨reached,physicalAfter⟩,called,equal⟩ := supported
  cases equal
  apply source_query setup wire sign seed scalar candidate unused selected pairs publicKey challenge query before.1 reached
  apply OracleComp.support_simulateQ_run'_subset physical _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields.hidden_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields.hidden_demand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields.selective_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields.selective_demand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields.source_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields.source_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields.closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields.closed
