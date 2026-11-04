-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared
import BeaconcryptCore.Computational.RegistrationAuthenticationNative

/-! A successful original native accept carries its actual mandatory Init authentication cut. The verification trial uses the reached shared cache, current Server pin and chronological global ML signing history before that same accept. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitAuthentication
open PqxdhServerAuthExperiment (Setup Checks Codec)
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow (Event)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationWorldAuthentication.begin
  RegistrationServerSdkSource.afterAuthentication RegistrationNativeExperiment.handler
  RegistrationServerNativeSource.authenticate RegistrationAuthenticationShared.begin
  RegistrationSigningShared.historyFor RegistrationAuthenticationNative.trial

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

def withWorld (before : State n) (world : PqxdhRecordLiftWorld.State n) : State n :=
  { before with world := { before.world with world := (world, before.world.world.2) } }

/-- Actual SDK authentication retains the original Server state and literal global signing-attempt list. -/
theorem authenticate (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before : State n) :
    (RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before =
      Prod.map id (withWorld before) <$>
        (RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.world.world.1 := by
  simp only [RegistrationServerNativeSource.authenticate, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.authenticate, RegistrationWorldServerFrontend.withWorld,
    RegistrationServerFrontendCompiler.restore, RegistrationServerFrontendCompiler.erase,
    StateT.run, Functor.map_map, Prod.map, id_eq]
  rfl

/-- Every successful original SDK accept has the same mandatory ML/Ed cut before replay, reservation and agreement. -/
theorem accept_cut (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before after : State n) (session : Nat)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run before)) :
    ∃ events authenticated middle,
      (.ok (events, .Accepted authenticated), middle) ∈ support
        ((RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.world.world.1) ∧
      (.ok (some session), after) ∈ support
        ((RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated).run
          (withWorld before middle)) := by
  simp only [RegistrationServerSdkSource.accept, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨checked, first, continued⟩ := supported
  rw [authenticate setup codec route verify created packet before, support_map] at first
  obtain ⟨reached, member, same⟩ := first
  subst checked
  rcases reached with ⟨checked, middle⟩
  dsimp only [Prod.map, id] at continued
  cases checked with
  | fail error | div => simp only [StateT.run, state_pure_apply, support_pure, Set.mem_singleton_iff] at continued; cases continued
  | ok checked =>
      rcases checked with ⟨events, authentication⟩
      cases authentication with
      | Accepted authenticated => exact ⟨events, authenticated, middle, member, continued⟩
      | _ => simp only [StateT.run, state_pure_apply, support_pure, Set.mem_singleton_iff] at continued; cases continued

/-- The successful typed accept retains this actual authentication cut before its literal original session result. -/
theorem typed_cut (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (packet : registration.InitPacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (session : Nat)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.accept packet))).run before)) :
    ∃ events authenticated middle,
      (.ok (events, .Accepted authenticated), middle) ∈ support
        ((RegistrationWorldAuthentication.begin setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
          before.server.pin packet).run before.server.world.world.1) := by
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
  obtain ⟨events, authenticated, middle, called, _continued⟩ := accept_cut setup
    (RegistrationNativeWire.ledgerCodec wire) checks route source.verify representation created packet
    before.server reached.2 session (success ▸ possible)
  exact ⟨events, authenticated, middle, called⟩

/-- The same original typed success supplies an ordinary ML verification trial at its real cache cut, with its literal prior history. -/
theorem typed_trial (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (packet : registration.InitPacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (session : Nat)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.accept packet))).run before)) (protectedKey : Bool) (honest : protectedKey = true) :
    ∃ events authenticated middle,
      (.ok (events, .Accepted authenticated), middle) ∈ support
        ((RegistrationWorldAuthentication.begin setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
          before.server.pin packet).run before.server.world.world.1) ∧
      MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash middle.primitive.2) source.verify
        (RegistrationAuthenticationNative.trial protectedKey before.server.pin packet
          (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (RegistrationNativeMldsaShared.nativeProject before))) := by
  obtain ⟨events, authenticated, middle, called⟩ := typed_cut setup checks wire route representation created credential
    packet before after session supported
  refine ⟨events, authenticated, middle, called, ?_⟩
  apply RegistrationAuthenticationNative.begin_accepted_trial setup.source.crypto source.verify
    (RegistrationNativeWire.ledgerCodec wire).frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
    before.server.pin packet (RegistrationWorldAuthentication.project before.server.world.world.1)
    (RegistrationWorldAuthentication.project middle) events authenticated
    (RegistrationWorldAuthentication.begin_native_support setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
      before.server.pin packet before.server.world.world.1 middle events authenticated called)
    protectedKey honest (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key) (RegistrationNativeMldsaShared.nativeProject before))

/-- Failure of byte origin for a successful actual typed Init exposes an ordinary weak ML forgery or a collision between actual shared-cache queries. -/
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
    ∃ events authenticated middle,
      (.ok (events, .Accepted authenticated), middle) ∈ support
        ((RegistrationWorldAuthentication.begin setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
          before.server.pin packet).run before.server.world.world.1) ∧
      (MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash middle.primitive.2) source.verify
        (RegistrationAuthenticationNative.trial protectedKey before.server.pin packet
          (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key)
            (RegistrationNativeMldsaShared.nativeProject before))) ∨ CacheHasCollision middle.primitive.2) := by
  obtain ⟨events, authenticated, middle, called⟩ := typed_cut setup checks wire route representation created credential
    packet before after session supported
  refine ⟨events, authenticated, middle, called, ?_⟩
  apply RegistrationAuthenticationNative.begin_origin_split setup.source.crypto source.verify
    (RegistrationNativeWire.ledgerCodec wire).frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
    before.server.pin packet (RegistrationWorldAuthentication.project before.server.world.world.1)
    (RegistrationWorldAuthentication.project middle) events authenticated
    (RegistrationWorldAuthentication.begin_native_support setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
      before.server.pin packet before.server.world.world.1 middle events authenticated called)
    protectedKey honest (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key)
      (RegistrationNativeMldsaShared.nativeProject before))
  · exact RegistrationSigningShared.history_cached (PqxdhRefinement.absBytes packet.mldsa_public_key)
      (RegistrationNativeMldsaShared.nativeProject before) cached
  · exact absent

/-- The original typed successful accept carries the current selected pin, complete unsigned Init digest and actual AD281 fingerprint composition at one shared-cache cut. -/
theorem typed_binding (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (packet : registration.InitPacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (session : Nat)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.accept packet))).run before)) :
    ∃ events authenticated middle,
      (.ok (events, .Accepted authenticated), middle) ∈ support
        ((RegistrationWorldAuthentication.begin setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
          before.server.pin packet).run before.server.world.world.1) ∧
      authenticated.binding.server_pin.binding = before.server.pin.binding ∧
      authenticated.binding.server_pin.public_key = before.server.pin.public_key ∧
      MldsaSharedAuthentication.cacheHash middle.primitive.2
        (BeaconcryptCore.Refinement.RegistrationAuthentication.initPreimage before.server.pin packet) =
        PqxdhRefinement.absBytes authenticated.binding.init_hash ∧
      PqxdhRefinement.absBytes authenticated.binding.associated_data =
        BeaconcryptCore.Refinement.SessionBinding.boundAssociatedData
          (PqxdhRefinement.absBytes authenticated.binding.server_pin.binding.identity_public_key)
          (PqxdhRefinement.absBytes authenticated.binding.beacon_identity_public_key)
          (MldsaSharedAuthentication.cacheHash middle.primitive.2
            (PqxdhRefinement.absBytes authenticated.binding.server_pin.public_key))
          (MldsaSharedAuthentication.cacheHash middle.primitive.2 (PqxdhRefinement.absBytes packet.mldsa_public_key)) := by
  obtain ⟨events, authenticated, middle, called⟩ := typed_cut setup checks wire route representation created credential
    packet before after session supported
  have native := RegistrationWorldAuthentication.begin_native_support setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
    before.server.pin packet before.server.world.world.1 middle events authenticated called
  have pin := RegistrationAuthenticationNative.begin_selected_pin setup.source.crypto source.verify
    (RegistrationNativeWire.ledgerCodec wire).frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
    before.server.pin packet (RegistrationWorldAuthentication.project before.server.world.world.1)
    (RegistrationWorldAuthentication.project middle) events authenticated native
  refine ⟨events, authenticated, middle, called, pin.1, pin.2, ?_, ?_⟩
  · exact RegistrationAuthenticationNative.begin_init_hash setup.source.crypto source.verify
      (RegistrationNativeWire.ledgerCodec wire).frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
      before.server.pin packet (RegistrationWorldAuthentication.project before.server.world.world.1)
      (RegistrationWorldAuthentication.project middle) events authenticated native
  · exact RegistrationAuthenticationNative.begin_associated_data setup.source.crypto source.verify
      (RegistrationNativeWire.ledgerCodec wire).frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
      before.server.pin packet (RegistrationWorldAuthentication.project before.server.world.world.1)
      (RegistrationWorldAuthentication.project middle) events authenticated native

end BeaconcryptCore.Computational.RegistrationNativeInitAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.authenticate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.authenticate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.accept_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.accept_cut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.typed_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.typed_cut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.typed_trial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.typed_trial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.typed_origin_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.typed_origin_split
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.typed_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitAuthentication.typed_binding
