-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitAuthentication

/-! Successful original native acceptance retains its actual mandatory ML-verification cache until the returned typed result. The post-authentication agreement only samples ordinary source primitives, and native replay insertion changes no cache or signing history. This permits executable trial observers to use the actual returned cache rather than choose an existential internal cut. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitFinal
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationServerFrontendCompiler (State)
open RegistrationNativeInitAuthentication (withWorld)
variable {n : Nat} {ι KemSK Reader Response Value Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin
  RegistrationServerNativeSource.agree RegistrationServerNativeSource.retain
  RegistrationNativeExperiment.handler RegistrationSigningShared.historyFor RegistrationAuthenticationNative.trial
  RegistrationReplaySchedule.consume

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

/-- Every actual agreement continuation retains exactly its prior shared cache and ML attempt history. -/
theorem agreement (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Value)
    (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : Value × RegistrationWorldAgreement.State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationWorldAgreement.agreement hkdf primitive) work).run before)) :
    result.2.world.1.primitive.2 = before.world.1.primitive.2 ∧ result.2.world.2 = before.world.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, continued⟩ := supported
      obtain ⟨cached, receipts, _requests⟩ := RegistrationWorldAgreement.agreement_cache_receipts
        hkdf primitive query before middle first
      obtain ⟨laterCache, laterReceipts⟩ := ih middle.1 middle.2 result continued
      exact ⟨laterCache.trans cached, laterReceipts.trans receipts⟩

def summary (before : State n) : RegistrationSigningShared.State :=
  (before.world.world.2, before.world.world.1.primitive.2)

/-- The SDK's actual agreement body preserves its complete ML history/cache summary. -/
theorem agree (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n)
    (result : RustM agreement.AgreementEffect × State n)
    (supported : result ∈ support ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)) :
    summary result.2 = summary before := by
  simp only [RegistrationServerNativeSource.agree, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  obtain ⟨cached, receipts⟩ := agreement setup.source
    (RegistrationServerRoleBackend.native setup checks representation created.seed)
    (RegistrationReplaySchedule.begin before.control authenticated before.consumed) before.world inner possible
  exact Prod.ext receipts cached

/-- Moving a retained native token changes no shared-cache or ML signing-attempt receipt. -/
theorem retain (created : PqxdhLiveServerConstruction.Created Unit) (accepted : agreement.ServerAgreement)
    (before : State n) (result : RustM (Option Nat) × State n)
    (supported : result ∈ support ((RegistrationServerNativeSource.retain created accepted).run before)) :
    summary result.2 = summary before := by
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore,
    StateT.run] at supported
  cases taken : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div =>
      simp only [taken, map_pure, support_pure, Set.mem_singleton_iff, Prod.map, id_eq,
        RegistrationServerFrontendCompiler.erase] at supported
      cases supported
      rfl
  | ok moved =>
      rcases moved with ⟨token, history⟩
      cases token <;> simp only [taken, map_pure, support_pure, Set.mem_singleton_iff, Prod.map, id_eq,
        RegistrationServerFrontendCompiler.erase] at supported <;>
        cases supported <;> rfl

/-- Source replay, reservation, agreement failure and insertion retain exactly the cache/history reached by authentication. -/
theorem afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n)
    (result : RustM (Option Nat) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated).run before)) :
    summary result.2 = summary before := by
  simp only [RegistrationServerSdkSource.afterAuthentication, StateT.run] at supported
  split_ifs at supported with replay reserved
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    cases supported
    rfl
  · simp only [mem_support_bind_iff] at supported
    obtain ⟨completed, possible, continued⟩ := supported
    rcases completed with ⟨reply, state⟩
    have prior := agree setup checks representation created packet authenticated before (reply, state) possible
    cases reply with
    | fail error | div =>
        simp only [support_pure, Set.mem_singleton_iff] at continued
        cases continued
        exact prior
    | ok effect => cases effect with
      | ServerComplete accepted =>
          have after := retain created accepted state result continued
          exact after.trans prior
      | _ =>
          simp only [support_pure, Set.mem_singleton_iff] at continued
          cases continued
          exact prior
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    cases supported
    rfl

/-- A successful actual SDK accept carries its ordinary ML trial to the returned cache with the literal prior signing history. -/
theorem accepted (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before after : State n) (session : Nat)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationServerSdkSource.accept setup codec checks route source.verify representation created packet).run before))
    (protectedKey : Bool) (honest : protectedKey = true) :
    MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash after.world.world.1.primitive.2) source.verify
      (RegistrationAuthenticationNative.trial protectedKey before.pin packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (summary before))) := by
  obtain ⟨events, authenticated, middle, called, continued⟩ := RegistrationNativeInitAuthentication.accept_cut setup codec checks
    route source.verify representation created packet before after session supported
  have same := afterAuthentication setup checks representation created packet authenticated (withWorld before middle)
    (.ok (some session), after) continued
  have cached : after.world.world.1.primitive.2 = middle.primitive.2 := congrArg (fun value : RegistrationSigningShared.State => value.2) same
  rw [cached]
  apply RegistrationAuthenticationNative.begin_accepted_trial setup.source.crypto source.verify codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) before.pin packet
    (RegistrationWorldAuthentication.project before.world.world.1) (RegistrationWorldAuthentication.project middle)
    events authenticated (RegistrationWorldAuthentication.begin_native_support setup codec route source.verify before.pin packet
      before.world.world.1 middle events authenticated called) protectedKey honest
    (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (summary before))

/-- Successful typed acceptance retains its exact original SDK poststate. -/
theorem typed_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (packet : registration.InitPacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (session : Nat)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.accept packet))).run before)) :
    ∃ returned, (.ok (some session), returned) ∈ support
      ((RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify
        representation created packet).run before.server) ∧ after.server = returned := by
  have law : (RegistrationNativeExperiment.handler setup checks wire route representation created source credential
      (.inr (.accept packet))).run before =
      (fun result => (result.1, { before with parsedAccepts := before.parsedAccepts + 1, server := result.2 })) <$>
        (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify
          representation created packet).run before.server := by
    simp only [RegistrationNativeExperiment.handler, StateT.run]
    rfl
  rw [law, support_map] at supported
  obtain ⟨reached, possible, same⟩ := supported
  have success : reached.1 = .ok (some session) := congrArg Prod.fst same
  exact ⟨reached.2, success ▸ possible,
    (congrArg (fun result : RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK source => result.2.server) same).symm⟩

/-- The executable original native result supplies the ordinary ML trial, using its returned cache and literal pre-call history. -/
theorem typed_accepted (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (packet : registration.InitPacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (session : Nat)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.accept packet))).run before)) (protectedKey : Bool) (honest : protectedKey = true) :
    MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash after.server.world.world.1.primitive.2) source.verify
      (RegistrationAuthenticationNative.trial protectedKey before.server.pin packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key)
          (RegistrationNativeMldsaShared.nativeProject before))) := by
  obtain ⟨returned, possible, same⟩ := typed_source setup checks wire route representation created credential packet
    before after session supported
  rw [same]
  exact accepted setup (RegistrationNativeWire.ledgerCodec wire) checks route representation created packet
    before.server returned session possible protectedKey honest

/-- Byte-origin failure in the successful returned SDK result exposes an actual weak ML forgery or shared-cache collision. -/
theorem origin_split (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before after : State n) (session : Nat)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationServerSdkSource.accept setup codec checks route source.verify representation created packet).run before))
    (protectedKey : Bool) (honest : protectedKey = true) (cached : RegistrationSigningShared.Cached (summary before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationAuthenticationNative.trial protectedKey before.pin packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (summary before)))) :
    MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash after.world.world.1.primitive.2) source.verify
      (RegistrationAuthenticationNative.trial protectedKey before.pin packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (summary before))) ∨
      CacheHasCollision after.world.world.1.primitive.2 := by
  obtain ⟨events, authenticated, middle, called, continued⟩ := RegistrationNativeInitAuthentication.accept_cut setup codec checks
    route source.verify representation created packet before after session supported
  have same := afterAuthentication setup checks representation created packet authenticated (withWorld before middle)
    (.ok (some session), after) continued
  have finalCache : after.world.world.1.primitive.2 = middle.primitive.2 :=
    congrArg (fun value : RegistrationSigningShared.State => value.2) same
  rw [finalCache]
  apply RegistrationAuthenticationNative.begin_origin_split setup.source.crypto source.verify codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) before.pin packet
    (RegistrationWorldAuthentication.project before.world.world.1) (RegistrationWorldAuthentication.project middle)
    events authenticated (RegistrationWorldAuthentication.begin_native_support setup codec route source.verify before.pin packet
      before.world.world.1 middle events authenticated called) protectedKey honest
    (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (summary before))
  · exact RegistrationSigningShared.history_cached (PqxdhRefinement.absBytes packet.mldsa_public_key) (summary before) cached
  · exact absent

/-- The actual returned native typed result has the same ordinary forgery-or-cache-collision decomposition. -/
theorem typed_origin_split (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (packet : registration.InitPacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (session : Nat)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.accept packet))).run before)) (protectedKey : Bool) (honest : protectedKey = true)
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationAuthenticationNative.trial protectedKey before.server.pin packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key)
        (RegistrationNativeMldsaShared.nativeProject before)))) :
    MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash after.server.world.world.1.primitive.2) source.verify
      (RegistrationAuthenticationNative.trial protectedKey before.server.pin packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key)
          (RegistrationNativeMldsaShared.nativeProject before))) ∨ CacheHasCollision after.server.world.world.1.primitive.2 := by
  obtain ⟨returned, possible, same⟩ := typed_source setup checks wire route representation created credential packet
    before after session supported
  rw [same]
  exact origin_split setup (RegistrationNativeWire.ledgerCodec wire) checks route representation created packet
    before.server returned session possible protectedKey honest cached absent

end BeaconcryptCore.Computational.RegistrationNativeInitFinal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitFinal.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitFinal.agreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitFinal.agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitFinal.agree
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitFinal.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitFinal.retain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitFinal.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitFinal.afterAuthentication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitFinal.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitFinal.accepted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitFinal.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitFinal.typed_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitFinal.typed_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitFinal.typed_accepted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitFinal.origin_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitFinal.origin_split
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitFinal.typed_origin_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitFinal.typed_origin_split
