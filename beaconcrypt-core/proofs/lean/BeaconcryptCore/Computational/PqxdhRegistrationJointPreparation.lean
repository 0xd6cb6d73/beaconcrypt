-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointBundle

/-! Exact Beacon registration preparation through the existing joint identity and KEM services. Only representation and callback routing are changed; the original optional inputs, source order and complete private service histories remain. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation
open PqxdhRefinement PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhRegistrationJointBundle (Identity Key)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

abbrev Spec (Response : Type) := PqxdhBeaconPhase2Preparation.Spec Identity ScalarBytes Key Nat Response
abbrev NativeSpec (KemSK Response : Type) := PqxdhBeaconPhase2Preparation.Spec IdentitySeed ScalarBytes
  (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response
abbrev Pool (KemSK : Type) := PqxdhLiveKemBirth.State KemSK

/-- The private callback client forwards exactly the actual service indices. It carries no separate identity-seed or KEM-secret argument. Optional missing-index and primitive rejection replies are retained. -/
noncomputable def compiler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (Spec Response) (OracleComp (PqxdhLiveKemBirth.Spec KemSK))
  | .decode raw => pure (codec.read2 raw)
  | .ciphertext response => pure (codec.ciphertext response)
  | .ephemeral response => pure (codec.ephemeral response)
  | .serverIdentity response => pure (codec.serverIdentity response)
  | .publicConversion server => pure ((setup.source.crypto.xpkConv (absBytes server)).bind toWord32)
  | .privateConversion identity => pure (some identity.1)
  | .decapsulate ciphertext key =>
      Option.map PqxdhRootTableInitialization.rootArray <$>
        (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr (.decapsulate key.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))))
  | .dhPair scalar point => pure ((sourceScalarDh setup.source.crypto scalar
      (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray)
  | .dhIdentity index point =>
      (fun reply => Option.map PqxdhRootTableInitialization.rootArray reply.join) <$>
        (PqxdhLiveKemBirth.Spec KemSK).query (.inl (.inr (.service index (.staticDh (PqxdhPhase2GapDhSource.peer point)))))
  | .assignedId response => pure (codec.assignedId response)
  | .eraseShared _ => pure ()

noncomputable def interpreted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (Spec Response) (StateT (Pool KemSK) ProbComp) :=
  PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem ∘ₛ compiler setup codec

/-- Private mathematical annotation of the original source callback, recording only its actual decapsulation and joint-DH replies. The source still executes its own original secret arguments. -/
noncomputable def annotated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) : QueryImpl (NativeSpec KemSK Response) (StateT (Pool KemSK) ProbComp) :=
  fun query pool => match query with
  | .decapsulate ciphertext key =>
      (fun reply => (Option.map PqxdhRootTableInitialization.rootArray reply,
        (pool.1, PqxdhLiveKemBirth.record (.decapsulate kemIndex (PqxdhPhase2InputBytes.ciphertext ciphertext)) reply pool.2))) <$>
        simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
          (setup.kem.decaps key.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))
  | .dhIdentity seed point =>
      let peer := PqxdhPhase2GapDhSource.peer point
      let reply := setup.joint.staticDh seed peer
      pure (Option.map PqxdhRootTableInitialization.rootArray reply,
        (PqxdhDynamicIdentityPool.record (.inr (.service identityIndex (.staticDh peer))) (some reply) pool.1, pool.2))
  | query => (fun reply => (reply, pool)) <$> PqxdhRegistrationSchedule.preparation setup codec query

set_option backward.isDefEq.respectTransparency false in
/-- The indexed KEM callback uses the actual owned private pair and preserves its exact optional reply in the full private history. -/
theorem decapsulate_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (pool : Pool KemSK)
    (kemOwned : pool.2.keys[kemIndex]? = some keys) :
    (interpreted setup codec (.decapsulate ciphertext (PqxdhRegistrationJointBundle.keyMap kemIndex keys))).run pool =
      (annotated setup codec identityIndex kemIndex (.decapsulate ciphertext keys)).run pool := by
  simp only [interpreted, QueryImpl.apply_compose, compiler, simulateQ_map,
    simulateQ_spec_query, StateT.run, PqxdhRegistrationJointBundle.keyMap]
  change (((fun reply => (reply.1, (pool.1, reply.2))) <$>
      (PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem
        (.decapsulate kemIndex (PqxdhPhase2InputBytes.ciphertext ciphertext))).run pool.2) >>= fun reply =>
      pure (Option.map PqxdhRootTableInitialization.rootArray reply.1, reply.2)) = _
  rw [PqxdhLiveKemBirth.decapsulate_present setup.baseImpl setup.kem pool.2 kemIndex keys kemOwned]
  simp only [annotated, bind_pure_comp, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- Converted identity DH is answered by the same seed's joint primitive service and records its exact optional reply, without a second private conversion input. -/
theorem dh_identity_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (seed : IdentitySeed) (point : Word32) (pool : Pool KemSK)
    (identityOwned : pool.1.seeds[identityIndex]? = some seed) :
    (interpreted setup codec (.dhIdentity identityIndex point)).run pool =
      (annotated setup codec identityIndex kemIndex (.dhIdentity seed point)).run pool := by
  simp only [interpreted, QueryImpl.apply_compose, compiler, simulateQ_map,
    simulateQ_spec_query, StateT.run]
  change (((fun reply => (reply.1, (reply.2, pool.2))) <$>
      (PqxdhDynamicIdentityPool.lazyImpl setup.joint
        (.inr (.service identityIndex (.staticDh (PqxdhPhase2GapDhSource.peer point))))).run pool.1) >>= fun reply =>
      pure (Option.map PqxdhRootTableInitialization.rootArray reply.1.join, reply.2)) = _
  simp only [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
    StateT.run, identityOwned, Option.map_some, PqxdhJointIdentity.primitiveReply,
    map_pure, pure_bind, annotated]
  rfl


/-- Direct evaluated form of the same compiler, used to keep dependent query types explicit during the source comparison. -/
noncomputable def evaluated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (Spec Response) (StateT (Pool KemSK) ProbComp) := fun query pool => match query with
  | .decode raw => pure (codec.read2 raw, pool)
  | .ciphertext response => pure (codec.ciphertext response, pool)
  | .ephemeral response => pure (codec.ephemeral response, pool)
  | .serverIdentity response => pure (codec.serverIdentity response, pool)
  | .publicConversion server => pure ((setup.source.crypto.xpkConv (absBytes server)).bind toWord32, pool)
  | .privateConversion identity => pure (some identity.1, pool)
  | .decapsulate ciphertext key => do
      let result ← (PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem
        (.decapsulate key.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))).run pool.2
      pure (Option.map PqxdhRootTableInitialization.rootArray result.1, (pool.1, result.2))
  | .dhPair scalar point => pure ((sourceScalarDh setup.source.crypto scalar
      (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray, pool)
  | .dhIdentity index point => do
      let result ← (PqxdhDynamicIdentityPool.lazyImpl setup.joint
        (.inr (.service index (.staticDh (PqxdhPhase2GapDhSource.peer point))))).run pool.1
      pure (Option.map PqxdhRootTableInitialization.rootArray result.1.join, (result.2, pool.2))
  | .assignedId response => pure (codec.assignedId response, pool)
  | .eraseShared _ => pure ((), pool)

set_option backward.isDefEq.respectTransparency false in
/-- The direct callback expression is exactly the original compiled service execution for every request and complete private state. -/
theorem interpreted_evaluated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    interpreted setup codec = evaluated setup codec := by
  funext query pool
  cases query <;> try rfl
  all_goals simp only [interpreted, QueryImpl.apply_compose, compiler,
    simulateQ_map, simulateQ_spec_query]
  all_goals change (((fun result => _) <$> _) >>= fun result => (pure _ : ProbComp _)) = _
  all_goals simp only [bind_map_left]
  all_goals rfl

private theorem bind_at {α β : Type} (work : StateT (Pool KemSK) ProbComp α)
    (next : α → StateT (Pool KemSK) ProbComp β) (pool : Pool KemSK) :
    (work >>= next) pool = (work pool >>= fun result => next result.1 result.2) := rfl

private theorem pure_at {α : Type} (value : α) (pool : Pool KemSK) :
    (pure value : StateT (Pool KemSK) ProbComp α) pool = pure (value, pool) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual source collector and indexed service collector have the same complete evaluated outcome. The only premises identify the exact private slots retained by this native owner. -/
theorem collect_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (seed : IdentitySeed) (prekey oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes) (pool : Pool KemSK)
    (identityOwned : pool.1.seeds[identityIndex]? = some seed)
    (kemOwned : pool.2.keys[kemIndex]? = some keys) :
    (simulateQ (interpreted setup codec)
      (PqxdhBeaconPhase2Preparation.collect (PqxdhRegistrationJointBundle.identityMap setup identityIndex seed)
        prekey oneTime (PqxdhRegistrationJointBundle.keyMap kemIndex keys) raw)).run pool =
      (simulateQ (annotated setup codec identityIndex kemIndex)
        (PqxdhBeaconPhase2Preparation.collect seed prekey oneTime keys raw)).run pool := by
  rw [interpreted_evaluated]
  simp only [PqxdhBeaconPhase2Preparation.collect, OptionT.run_bind, OptionT.run_mk,
    OptionT.run_pure, OptionT.run_monadLift, Option.elimM, simulateQ_bind, simulateQ_spec_query,
    StateT.run]
  cases decoded : codec.read2 raw <;> simp only [Option.elim]
  all_goals repeat' first
    | rfl
    | simp_all only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run, bind_at, pure_at, evaluated, annotated,
        PqxdhRegistrationSchedule.preparation, PqxdhLiveKemBirth.poolImpl,
        PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
        PqxdhJointIdentity.primitiveReply, PqxdhLiveKemBirth.record,
        pure_bind, map_pure, bind_map_left, bind_assoc, Option.map_some,
        PqxdhRegistrationJointBundle.identityMap, PqxdhRegistrationJointBundle.keyMap]
    | split
    | (congr 1; funext reply; cases reply)
  all_goals dsimp only [Option.join] at *
  all_goals simp_all

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting only private analysis histories recovers the literal original callback for every request, including failure replies. -/
theorem annotated_query_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (query : (NativeSpec KemSK Response).Domain) (pool : Pool KemSK) :
    Prod.fst <$> (annotated setup codec identityIndex kemIndex query).run pool =
      PqxdhRegistrationSchedule.preparation setup codec query := by
  cases query <;> simp only [annotated, StateT.run, PqxdhRegistrationSchedule.preparation,
    Functor.map_map, map_pure, simulateQ_map]


/-- The entire private annotation erases to the original source program, including arbitrary adaptive callback continuations. -/
theorem annotated_program_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (program : OracleComp (NativeSpec KemSK Response) Result)
    (pool : Pool KemSK) :
    Prod.fst <$> (simulateQ (annotated setup codec identityIndex kemIndex) program).run pool =
      simulateQ (PqxdhRegistrationSchedule.preparation setup codec) program := by
  induction program using OracleComp.inductionOn generalizing pool with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simpa only [bind_map_left] using congrArg
        (fun work => work >>= fun reply => simulateQ (PqxdhRegistrationSchedule.preparation setup codec) (next reply))
        (annotated_query_erase setup codec identityIndex kemIndex query pool)


/-- The original extracted identity/DH admission and shared-secret erasure follow the same collector outcome and preserve its complete service poststate. -/
theorem prepare_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (seed : IdentitySeed) (prekey oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (raw : Pqxdh.Bytes) (pool : Pool KemSK)
    (identityOwned : pool.1.seeds[identityIndex]? = some seed)
    (kemOwned : pool.2.keys[kemIndex]? = some keys) :
    (simulateQ (interpreted setup codec)
      (PqxdhBeaconPhase2Preparation.prepare control (PqxdhRegistrationJointBundle.identityMap setup identityIndex seed)
        prekey oneTime (PqxdhRegistrationJointBundle.keyMap kemIndex keys) raw)).run pool =
      (simulateQ (annotated setup codec identityIndex kemIndex)
        (PqxdhBeaconPhase2Preparation.prepare control seed prekey oneTime keys raw)).run pool := by
  simp only [PqxdhBeaconPhase2Preparation.prepare, simulateQ_bind, StateT.run_bind]
  rw [collect_source setup codec identityIndex kemIndex seed prekey oneTime keys raw pool identityOwned kemOwned]
  apply bind_congr
  rintro ⟨_ | inputs, after⟩
  · simp only [simulateQ_pure, StateT.run_pure]
  · simp only [PqxdhBeaconPhase2Preparation.afterInputs, simulateQ_bind, simulateQ_spec_query,
      interpreted, QueryImpl.apply_compose, compiler, annotated, PqxdhRegistrationSchedule.preparation,
      simulateQ_pure, pure_bind, StateT.run, map_pure, bind_at, pure_at]


/-- The complete subsequent protocol sees the same actual prepared input and both entire private services; this is stronger than equality of marginal DH or KEM outputs. -/
theorem prepare_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (seed : IdentitySeed) (prekey oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (raw : Pqxdh.Bytes) (pool : Pool KemSK)
    (identityOwned : pool.1.seeds[identityIndex]? = some seed)
    (kemOwned : pool.2.keys[kemIndex]? = some keys)
    (next : Option (PqxdhBeaconPhase2Preparation.Prepared Response) × Pool KemSK → ProbComp Result) :
    ((simulateQ (interpreted setup codec)
      (PqxdhBeaconPhase2Preparation.prepare control (PqxdhRegistrationJointBundle.identityMap setup identityIndex seed)
        prekey oneTime (PqxdhRegistrationJointBundle.keyMap kemIndex keys) raw)).run pool >>= next) =
      ((simulateQ (annotated setup codec identityIndex kemIndex)
        (PqxdhBeaconPhase2Preparation.prepare control seed prekey oneTime keys raw)).run pool >>= next) := by
  rw [prepare_source setup codec identityIndex kemIndex seed prekey oneTime keys control raw pool identityOwned kemOwned]

/-- Only the analysis histories are erased in the literal source result equation. No parser, conversion, KEM, DH, admission or erasure callback is replaced by a success premise. -/
theorem prepare_original (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (seed : IdentitySeed) (prekey oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (raw : Pqxdh.Bytes) (pool : Pool KemSK)
    (identityOwned : pool.1.seeds[identityIndex]? = some seed)
    (kemOwned : pool.2.keys[kemIndex]? = some keys) :
    Prod.fst <$> (simulateQ (interpreted setup codec)
      (PqxdhBeaconPhase2Preparation.prepare control (PqxdhRegistrationJointBundle.identityMap setup identityIndex seed)
        prekey oneTime (PqxdhRegistrationJointBundle.keyMap kemIndex keys) raw)).run pool =
      simulateQ (PqxdhRegistrationSchedule.preparation setup codec)
        (PqxdhBeaconPhase2Preparation.prepare control seed prekey oneTime keys raw) := by
  rw [prepare_source setup codec identityIndex kemIndex seed prekey oneTime keys control raw pool identityOwned kemOwned,
    annotated_program_erase]


/-- Recording a callback never changes any private owner slot, even when the primitive rejects. Only the exact histories may grow. -/
theorem annotated_query_slots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (query : (NativeSpec KemSK Response).Domain) (pool : Pool KemSK)
    (result : (NativeSpec KemSK Response).Range query × Pool KemSK)
    (supported : result ∈ support ((annotated setup codec identityIndex kemIndex query).run pool)) :
    result.2.1.seeds = pool.1.seeds ∧ result.2.2.keys = pool.2.keys := by
  cases query <;> simp only [annotated, StateT.run, support_map, Set.mem_image,
    mem_support_pure_iff] at supported
  all_goals obtain ⟨reply, _, rfl⟩ := supported
  all_goals exact ⟨rfl, rfl⟩

/-- Every adaptive annotated program preserves all private owner slots; later native protocol code may still erase its own live handles. -/
theorem annotated_program_slots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (program : OracleComp (NativeSpec KemSK Response) Result)
    (pool : Pool KemSK) (result : Result × Pool KemSK)
    (supported : result ∈ support ((simulateQ (annotated setup codec identityIndex kemIndex) program).run pool)) :
    result.2.1.seeds = pool.1.seeds ∧ result.2.2.keys = pool.2.keys := by
  induction program using OracleComp.inductionOn generalizing pool result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, rest⟩ := supported
      have head := annotated_query_slots setup codec identityIndex kemIndex query pool middle first
      have tail := ih middle.1 middle.2 result rest
      exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩


end BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.decapsulate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.decapsulate_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.dh_identity_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.dh_identity_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.interpreted_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.interpreted_evaluated

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.collect_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.annotated_query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.annotated_query_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.annotated_program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.annotated_program_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.prepare_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.prepare_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.prepare_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.prepare_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.prepare_original

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.annotated_query_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.annotated_query_slots

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.annotated_program_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation.annotated_program_slots
