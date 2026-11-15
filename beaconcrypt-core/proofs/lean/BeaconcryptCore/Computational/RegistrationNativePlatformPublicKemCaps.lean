-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemMaterial
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
/-! Private indexed KEM bills for the literal corrected public runtime. The actual dynamic writer and allocator state are retained, and the counted external-coin comparison introduces no private-key request. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps
attribute [local irreducible] RegistrationNativePlatformServerOpenControl.accept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
open RegistrationNativePlatformPublicKemLocal (IsPrivate LocalPrivate embed_bound)
open RegistrationNativeKemBeaconFootprint (Kind)
variable {n : Nat} {E Platform I KemSK A : Type} {base : OracleSpec I}
private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : V → W) (work : StateT S m V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
private theorem coins_free (kind : Kind) (work : ProbComp A) :
    (simulateQ (publicCoin (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [publicCoin, IsPrivate, isQueryBoundP_query_iff]
private theorem gate_free {V : Type} (kind : Kind)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : V → Nat) (output : Option V) (before : Platform) :
    ((RegistrationNativePlatformOrdinaryGate.gate (fun amount => platformFull (n := n) (KemSK := KemSK) (reserve amount)) size output).run before).IsQueryBoundP
      (IsPrivate (KemSK := KemSK) kind) 0 := by
  cases output with
  | none => trivial
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run]
    apply isQueryBoundP_bind (m := 0) (coins_free kind _)
    rintro ⟨result, after⟩ _
    cases result <;> trivial
private theorem record_free {source : RegistrationNativeMldsa.Source} (kind : Kind)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform) :
    ((record (n := n) (KemSK := KemSK) reserve query).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  rcases query with (send | raw) | ⟨owner, send | raw⟩
  · simp only [record, StateT.run, old]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨by simp [IsPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate], ?_⟩
    intro output
    simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, IsPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate, ite_false] using gate_free kind reserve _ output before.2
  · simp [record, StateT.run, old, isQueryBoundP_map_iff, IsPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate, isQueryBoundP_query_iff]
  · simp only [record, StateT.run]
    split
    · trivial
    · simp only [old]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨by simp [IsPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate], ?_⟩
      intro output
      simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, IsPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate, ite_false] using gate_free kind reserve _ output before.2
  · simp only [record, StateT.run]
    split
    · trivial
    · simp [old, isQueryBoundP_map_iff, IsPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate, isQueryBoundP_query_iff]
private theorem effect_free {source : RegistrationNativeMldsa.Source} (kind : Kind)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : State source Platform) :
    ((executeLocal (StateT.lift (effect (KemSK := KemSK) query))).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  apply embed_bound kind
  simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
  simp [effect, localQuery, LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate, isQueryBoundP_query_iff]

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Every actual corrected typed callback has its literal indexed birth/reveal allowance. -/
theorem handler_bound (kind : Kind) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind)
      (if kind = .create ∧ RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  cases query with
  | inl coin => simpa [handler, RegistrationNativeRawAdapter.kind] using effect_free kind (.inl coin) before
  | inr query => cases query with
    | create edPin mlPin keyId =>
      change (simulateQ embedLocal (_ : OracleComp (LocalSpec n KemSK) _)).IsQueryBoundP _ _
      apply embed_bound kind
      simp only [beacon, StateT.run, isQueryBoundP_map_iff, RegistrationNativeRawAdapter.kind, and_true]
      exact RegistrationNativePlatformPublicKemLocal.create_bound kind setup source selectedOwner publicPrekey edPin mlPin keyId _ _ _
    | bundle index =>
      change (simulateQ embedLocal (_ : OracleComp (LocalSpec n KemSK) _)).IsQueryBoundP _ _
      apply embed_bound kind
      simp only [beacon, StateT.run, map_apply, isQueryBoundP_map_iff, RegistrationNativeRawAdapter.kind, show (2 : Fin 12) ≠ 1 by decide, and_false, ite_false]
      exact RegistrationNativePlatformPublicKemLocal.bundle_zero kind setup writer selectedOwner publicPrekey index _ _ _
    | accept packet =>
      change (simulateQ embedLocal ((do
        let previous ← get
        modify fun current => ({current.1 with parsedAccepts := current.1.parsedAccepts + 1}, current.2)
        serverOpen (RegistrationNativePlatformServerOpenControl.accept
          (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) (decide (previous.1.parsedAccepts = selectedAccept)))
          (platform reserveRegistration) setup checks source.verify packet) : LocalM n KemSK Platform source _).run before)).IsQueryBoundP _ _
      apply embed_bound kind
      simp only [StateT.run, RegistrationNativeRawAdapter.kind, show (3 : Fin 12) ≠ 1 by decide, and_false, ite_false]
      apply (isQueryBoundP_map_iff _ _ _).mpr
      exact RegistrationNativePlatformPublicKemMaterial.accept_zero kind (decide (before.1.parsedAccepts = selectedAccept)) reserveRegistration setup checks source.verify packet before.1.server before.1.environment before.2
    | build handle application =>
      apply embed_bound kind
      simp only [build, StateT.run, isQueryBoundP_map_iff, RegistrationNativeRawAdapter.kind, show (4 : Fin 12) ≠ 1 by decide, and_false, ite_false]
      exact RegistrationNativePlatformPublicKemMaterial.build_embedding kind _
    | finish index packet =>
      apply embed_bound kind
      simp only [beacon, StateT.run, isQueryBoundP_map_iff, RegistrationNativeRawAdapter.kind, show (5 : Fin 12) ≠ 1 by decide, and_false, ite_false]
      exact RegistrationNativePlatformPublicKemMaterial.finish_zero kind setup wire index packet _ _ _
    | hmac key bytes => trivial
    | hash bytes => simpa [handler, RegistrationNativeRawAdapter.kind] using effect_free kind (.inr (.hash bytes)) before
    | serverSend keyId plaintext => simpa only [handler, RegistrationNativeRawAdapter.kind, show (8 : Fin 12) ≠ 1 by decide, and_false, ite_false] using record_free kind reserveFrame (.inl (.inl (plaintext,keyId))) before
    | serverRaw raw => simpa only [handler, RegistrationNativeRawAdapter.kind, show (9 : Fin 12) ≠ 1 by decide, and_false, ite_false] using record_free kind reserveFrame (.inl (.inr raw)) before
    | beaconSend index plaintext => simpa only [handler, RegistrationNativeRawAdapter.kind, show (10 : Fin 12) ≠ 1 by decide, and_false, ite_false] using record_free kind reserveFrame (.inr (index,.inl plaintext)) before
    | beaconRaw index raw => simpa only [handler, RegistrationNativeRawAdapter.kind, show (11 : Fin 12) ≠ 1 by decide, and_false, ite_false] using record_free kind reserveFrame (.inr (index,.inr raw)) before

/-- Arbitrary corrected adaptive public programs preserve their original private-key budget. -/
theorem program_bound (kind : Kind) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (count : Nat)
    (bounded : work.IsQueryBoundP (fun query => kind = .create ∧ RegistrationNativeRawAdapter.kind query = 1) count)
    (before : State source Platform) :
    ((simulateQ (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer) work).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer kind query current
  · intro query free current
    simpa only [ite_eq_right free] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer kind query current

omit primitive in
private theorem coin_embedding (kind : Kind) (work : OracleComp (Spec n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) count) :
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed work).IsQueryBoundP
      (RegistrationNativeOpenKeyKemPublic.IsPrivate (KemSK := KemSK) kind) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl query =>
    simp only [RegistrationNativePlatformPublicCoinEmbedding.embed, IsPrivate, isQueryBoundP_query_iff]
    intro counted
    simp only [counted, ite_true]
    decide
  | inr coin => simp [RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.effect,
      RegistrationNativePublicFrontend.liftLocal, IsPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate, isQueryBoundP_query_iff]

/-- The literal all-mode runtime tree, including external-coin comparison, creates at most qCreate indexed keys and never reveals one. -/
theorem run_bound (kind : Kind) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : State source Platform) :
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        serverKeyId bounds mode work before)).IsQueryBoundP
      (RegistrationNativeOpenKeyKemPublic.IsPrivate (KemSK := KemSK) kind) (if kind = .create then budget.create else 0) := by
  apply coin_embedding kind
  apply program_bound setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer kind
  cases kind with
  | create =>
    simpa only [true_and, ite_true] using RegistrationNativeKemFullFootprint.compile_creates setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work budget bounded
  | reveal | other =>
    simpa only [reduceCtorEq, false_and, ite_false] using
      isQueryBoundP_false (RegistrationNativeFullCompiler.compile setup.source.crypto
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work) 0
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps.handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemCaps.run_bound
