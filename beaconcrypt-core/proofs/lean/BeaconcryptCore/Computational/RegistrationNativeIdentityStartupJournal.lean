-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerPinCached
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance

/-! Actual initialized startup retains its warm shared CTX cache. Its sole possible address is the independently generated Server ML public key. Seeding the private backend with that cache and this known-input journal changes no cached answer or source counter and supplies retrospective recognition with a derived provenance invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityStartupJournal
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformCtxProvenance (Provenance)
variable {I KemSK Auxiliary Value : Type} {base : OracleSpec I} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem sampled_cache (work : ProbComp Value) (before : PqxdhRecordLiftWorld.State n)
    (after : Value × PqxdhRecordLiftWorld.State n)
    (reached : after ∈ support ((PqxdhRecordLiftWorld.sampled work).run before)) :
    after.2.primitive.2 = before.primitive.2 := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at reached
  obtain ⟨reply, _possible, same⟩ := reached
  cases same
  rfl

private theorem hash_provenance (input : Pqxdh.Bytes) (journal : List Pqxdh.Bytes)
    (before : PqxdhRecordLiftWorld.State n) (prior : Provenance (before.primitive.2, journal))
    (after : CtxRomAuth.CtxDigest × PqxdhRecordLiftWorld.State n)
    (reached : after ∈ support ((PqxdhRecordLiftWorld.effects (.inr (.hash input))).run before)) :
    Provenance (after.2.primitive.2, journal ++ [input]) := by
  have projected : (after.1, ((), after.2.primitive.2)) ∈ support
      (Prod.map id RegistrationWorldAuthentication.project <$>
        (PqxdhRecordLiftWorld.effects (.inr (.hash input))).run before) := by
    rw [support_map]
    exact ⟨after, reached, rfl⟩
  rw [RegistrationWorldAuthentication.hash_project, support_map] at projected
  obtain ⟨queried, actual, same⟩ := projected
  have cache := congrArg (fun result => result.2.2) same
  intro bytes present
  have queriedPresent : queried.2 ((), bytes) ≠ none := by rw [cache]; exact present
  rw [List.mem_append, List.mem_singleton]
  rcases CtxRomAuth.ctxRandomOracle_cache_origin ((), input) before.primitive.2 queried actual ((), bytes) queriedPresent with old | current
  · exact Or.inl (prior bytes old)
  · exact Or.inr (congrArg Prod.snd current)

private theorem pin_provenance (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (journal : List Pqxdh.Bytes) (before : RegistrationWorldServerReplay.Global n Auxiliary)
    (prior : Provenance (before.2.world.1.primitive.2, journal))
    (after : RegistrationNativeServerPinRecompute.PinReply × RegistrationWorldServerReplay.Global n Auxiliary)
    (reached : after ∈ support ((RegistrationWorldServerFrontend.initializePin binding publicKey).run before)) :
    Provenance (after.2.2.world.1.primitive.2, journal ++ [absBytes publicKey]) := by
  rw [RegistrationNativeServerPinRecompute.initialize_native, support_map] at reached
  obtain ⟨returned, actual, same⟩ := reached
  cases same
  rw [RegistrationNativeServerPinRecompute.native_run, mem_support_bind_iff] at actual
  obtain ⟨hashed, called, continued⟩ := actual
  rw [mem_support_pure_iff] at continued
  cases continued
  exact hash_provenance (absBytes publicKey) journal before.2.world.1 prior hashed called

private theorem install_cache (created : PqxdhLiveServerConstruction.Created Unit)
    (before : PqxdhRecordLiftWorld.State n) (after : Unit × PqxdhRecordLiftWorld.State n)
    (reached : after ∈ support ((PqxdhRecordLiftWorld.initializeServer created).run before)) :
    after.2.primitive.2 = before.primitive.2 := by
  cases existing : before.server with
  | none =>
    simp only [PqxdhRecordLiftWorld.initializeServer, StateT.run, existing, mem_support_pure_iff] at reached
    cases reached
    rfl
  | some server =>
    simp only [PqxdhRecordLiftWorld.initializeServer, StateT.run, existing, mem_support_pure_iff] at reached
    cases reached
    rfl

/-- Native Server initialization adds exactly its known public-key input to the inherited actual cache journal. -/
theorem frontend (created : PqxdhLiveServerConstruction.Created Unit) (publicKey : Std.Array U8 1952#usize)
    (auxiliary : Auxiliary) (before after : PqxdhRecordLiftWorld.State n)
    (journal : List Pqxdh.Bytes) (prior : Provenance (before.primitive.2, journal))
    (native : RegistrationWorldServerFrontend.State n Auxiliary)
    (reached : (.ok (.Some native), after) ∈ support ((RegistrationWorldServerFrontend.start created publicKey auxiliary).run before)) :
    Provenance (native.global.2.world.1.primitive.2, journal ++ [absBytes publicKey]) := by
  simp only [RegistrationWorldServerFrontend.start, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at reached
  obtain ⟨installed, installedAt, pinned, pinnedAt, returned⟩ := reached
  have inherited : Provenance (installed.2.primitive.2, journal) := by
    rw [install_cache created before installed installedAt]
    exact prior
  have known := pin_provenance ⟨created.server.server.identity, created.server.server.metadata.sender⟩ publicKey journal
    (PqxdhJointDhExtractFamily.empty, ⟨auxiliary, [], [], (installed.2, [])⟩) inherited pinned pinnedAt
  cases answered : pinned.1 with
  | fail error | div => simp only [answered] at returned; cases returned
  | ok value => cases value with
    | none => simp only [answered] at returned; cases returned
    | some pin =>
      simp only [answered] at returned
      cases returned
      exact known

/-- The actual warm cache after complete successful startup is supported by one known independently generated public-key input. It is never reset to empty. -/
theorem start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (reached : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Provenance (RegistrationNativeWorldCache.cache initial.state, [absBytes initial.credential.publicKey]) := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at reached
  obtain ⟨constructed, constructedAt, continued⟩ := reached
  have constructedCache := sampled_cache _ (PqxdhRecordLiftWorld.initial : PqxdhRecordLiftWorld.State n) constructed constructedAt
  cases built : constructed.1.1 with
  | none => simp only [built, mem_support_pure_iff] at continued; cases continued
  | some created =>
    simp only [built, mem_support_bind_iff] at continued
    obtain ⟨generated, generatedAt, continued⟩ := continued
    have generatedCache := (sampled_cache _ constructed.2 generated generatedAt).trans constructedCache
    cases chosen : generated.1 with
    | none => simp only [chosen, mem_support_pure_iff] at continued; cases continued
    | some credential =>
      simp only [chosen, mem_support_bind_iff] at continued
      obtain ⟨initialized, initializedAt, returned⟩ := continued
      cases native : initialized.1 with
      | fail error | div => simp only [native, mem_support_pure_iff] at returned; cases returned
      | ok reply => cases reply with
        | none => simp only [native, mem_support_pure_iff] at returned; cases returned
        | some state =>
          simp only [native, mem_support_pure_iff, Option.some.injEq] at returned
          cases returned
          have shape : initialized = (.ok (.Some state), initialized.2) := by rw [← native]
          have initialKnown : Provenance (generated.2.primitive.2, []) := by
            rw [generatedCache]
            exact RegistrationNativePlatformCtxProvenance.empty
          exact frontend created credential.publicKey RegistrationServerRoleBackend.empty generated.2 initialized.2 [] initialKnown state
            (by rw [← shape]; exact initializedAt)

/-- The genuine warm initialized cache has at most one address, so its initial collision event is false before any adversarial callback. -/
theorem collision_free (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (reached : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    ¬ CacheHasCollision (RegistrationNativeWorldCache.cache initial.state) := by
  have known := start setup ensureInit identityIndex serverKeyId initial reached
  rintro ⟨⟨unitLeft, bytesLeft⟩, ⟨unitRight, bytesRight⟩, replyLeft, replyRight, different, cachedLeft, cachedRight, _equalReplies⟩
  cases unitLeft
  cases unitRight
  have left := known bytesLeft (by rw [cachedLeft]; simp only [ne_eq, Option.some_ne_none, not_false_eq_true])
  have right := known bytesRight (by rw [cachedRight]; simp only [ne_eq, Option.some_ne_none, not_false_eq_true])
  simp only [List.mem_singleton] at left right
  exact different (congrArg (fun bytes => ((), bytes)) (left.trans right.symm))

end BeaconcryptCore.Computational.RegistrationNativeIdentityStartupJournal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityStartupJournal.frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityStartupJournal.frontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityStartupJournal.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityStartupJournal.start
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityStartupJournal.collision_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityStartupJournal.collision_free
