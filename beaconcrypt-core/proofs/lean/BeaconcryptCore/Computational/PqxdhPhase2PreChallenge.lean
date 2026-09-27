import BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds

/-!
Prechallenge Phase2 attempts execute immediately through the ordinary unblocked decapsulation interface. Their complete owner result and auxiliary state survive into the subsequent challenge selection; no callback or terminal abort is deferred. The secret key occurs only in the native interpreter. Concrete source auxiliary installation and the whole scheduler remain separate consuming work.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2PreChallenge
open PqxdhBeaconPhase2Routed (AuxSpec)
open PqxdhBeaconPhase2Preparation (Bytes Word32 Ciphertext)
open PqxdhKemIndCca PqxdhJointKdfGame PqxdhStatefulPhase1EufCma
open PqxdhRootTableInitialization (rootArray)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK I D K X Response Auxiliary : Type}

noncomputable def preAux
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (unifSpec + baseSpec))) :=
  fun query auxiliary => simulateQ (localKemPreChallengeImpl kem secret) ((aux query).run auxiliary)

noncomputable def nativePre
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D (Option K) X Response)
      (StateT Auxiliary (OracleComp (unifSpec + baseSpec)))
  | .inl (.decode raw) => preAux kem secret aux (.decode raw)
  | .inl (.ciphertext response) => preAux kem secret aux (.ciphertext response)
  | .inl (.ephemeral response) => preAux kem secret aux (.ephemeral response)
  | .inl (.serverIdentity response) => preAux kem secret aux (.serverIdentity response)
  | .inl (.publicConversion value) => preAux kem secret aux (.publicConversion value)
  | .inl (.privateConversion identity) => preAux kem secret aux (.privateConversion identity)
  | .inl (.decapsulate value none) =>
      liftM (Option.map rootArray <$> kem.decaps secret (PqxdhPhase2InputBytes.ciphertext value))
  | .inl (.decapsulate value (some prior)) => preAux kem secret aux (.localDecapsulation value prior)
  | .inl (.dhPair pair value) => preAux kem secret aux (.dhPair pair value)
  | .inl (.dhIdentity identity value) => preAux kem secret aux (.dhIdentity identity value)
  | .inl (.assignedId response) => preAux kem secret aux (.assignedId response)
  | .inl (.eraseShared _) => pure ()
  | .inr (.inl query) => preAux kem secret aux (.raw query)
  | .inr (.inr (.root input)) => pure (some (RawCtxSourceHkdf.rootResponse source.crypto input))
  | .inr (.inr (.initial request)) => preAux kem secret aux (.initial request)
  | .inr (.inr (.application response)) => preAux kem secret aux (.application response)

noncomputable def pre
    (source : FixedHkdfSha512NoSaltSource)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D (Option K) X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))
  | .inl (.decode raw) => aux (.decode raw)
  | .inl (.ciphertext response) => aux (.ciphertext response)
  | .inl (.ephemeral response) => aux (.ephemeral response)
  | .inl (.serverIdentity response) => aux (.serverIdentity response)
  | .inl (.publicConversion value) => aux (.publicConversion value)
  | .inl (.privateConversion identity) => aux (.privateConversion identity)
  | .inl (.decapsulate value none) =>
      liftM (Option.map rootArray <$> ((MlKemCCAOracleSpec baseSpec).query (.inr (PqxdhPhase2InputBytes.ciphertext value))))
  | .inl (.decapsulate value (some prior)) => aux (.localDecapsulation value prior)
  | .inl (.dhPair pair value) => aux (.dhPair pair value)
  | .inl (.dhIdentity identity value) => aux (.dhIdentity identity value)
  | .inl (.assignedId response) => aux (.assignedId response)
  | .inl (.eraseShared _) => pure ()
  | .inr (.inl query) => aux (.raw query)
  | .inr (.inr (.root input)) => pure (some (RawCtxSourceHkdf.rootResponse source.crypto input))
  | .inr (.inr (.initial request)) => aux (.initial request)
  | .inr (.inr (.application response)) => aux (.application response)

/-- Every prechallenge callback retains its original optional reply and complete private state. -/
theorem pre_step
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (query : (PqxdhBeaconPhase2Publication.NativeSpec I D (Option K) X Response).Domain)
    (auxiliary : Auxiliary) :
    simulateQ (localKemPreChallengeImpl kem secret) ((pre source aux query).run auxiliary) =
      ((nativePre source kem secret aux query).run auxiliary) := by
  rcases query with (query | (query | query)) <;> cases query <;> try rfl
  case inl.decapsulate value key =>
    cases key with
    | some prior => rfl
    | none =>
      change simulateQ (localKemPreChallengeImpl kem secret)
        ((fun reply => (reply, auxiliary)) <$> (Option.map rootArray <$>
          ((MlKemCCAOracleSpec baseSpec).query (.inr (PqxdhPhase2InputBytes.ciphertext value)) : OracleComp (MlKemCCAOracleSpec baseSpec) _))) = _
      rw [simulateQ_map, simulateQ_map]
      unfold nativePre
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift,
        StateT.run, bind_pure_comp]
      exact congrArg (fun work => (fun reply => (reply, auxiliary)) <$> (Option.map rootArray <$> work))
        (simulateQ_spec_query (localKemPreChallengeImpl kem secret) (.inr (PqxdhPhase2InputBytes.ciphertext value)))

/-- A complete finish attempt runs before the challenge, preserving its immediate result and full private poststate. -/
theorem owner_pre
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    ((simulateQ (nativePre source kem secret aux)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary) =
      simulateQ (localKemPreChallengeImpl kem secret)
        ((simulateQ (pre source aux) (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary) := by
  exact (simulateQ_StateT_compose (pre source aux)
    (localKemPreChallengeImpl kem secret) (nativePre source kem secret aux)
    (pre_step source kem secret aux) _ auxiliary).symm

/-- The exact prechallenge owner result enters every subsequent adaptive computation, without moving a finish attempt across challenge selection. -/
theorem owner_pre_continuation {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary)
    (next : ((Option Bytes × PqxdhBeaconPhase2Preparation.State I D (Option K)) × Auxiliary) →
      OracleComp (MlKemCCAOracleSpec baseSpec) Result) :
    (((simulateQ (nativePre source kem secret aux)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary) >>=
        fun result => simulateQ (localKemPreChallengeImpl kem secret) (next result)) =
      simulateQ (localKemPreChallengeImpl kem secret)
        (((simulateQ (pre source aux) (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary) >>= next) := by
  rw [owner_pre, simulateQ_bind]

/-- Every prechallenge callback has an explicit selected-query allowance, including locally owned prior keys. -/
theorem pre_step_bound
    (source : FixedHkdfSha512NoSaltSource)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux qDecapsulation : Nat)
    (auxBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP predicate qAux)
    (decapsulationBound : ∀ ciphertext, (if predicate (.inr ciphertext) then 1 else 0) ≤ qDecapsulation)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec I D (Option K) X Response).Domain)
    (auxiliary : Auxiliary) :
    ((pre source aux query).run auxiliary).IsQueryBoundP predicate (qAux + qDecapsulation) := by
  rcases query with (query | (query | query)) <;> cases query <;> try exact (auxBound _ auxiliary).mono (Nat.le_add_right _ _)
  case inl.decapsulate value key =>
    cases key with
    | some prior => exact (auxBound _ auxiliary).mono (Nat.le_add_right _ _)
    | none =>
      change OracleComp.IsQueryBoundP ((fun reply => (reply, auxiliary)) <$> (Option.map rootArray <$>
        ((MlKemCCAOracleSpec baseSpec).query (.inr (PqxdhPhase2InputBytes.ciphertext value)) : OracleComp (MlKemCCAOracleSpec baseSpec) _))) predicate _
      rw [isQueryBoundP_map_iff, isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff (spec := MlKemCCAOracleSpec baseSpec) (p := predicate)
        (.inr (PqxdhPhase2InputBytes.ciphertext value)) _).2 (by
          have bounded := decapsulationBound (PqxdhPhase2InputBytes.ciphertext value)
          intro selected
          simp only [if_pos selected] at bounded
          omega)
  case inl.eraseShared => simp [pre, StateT.run_pure]
  case inr.inr.root => simp [pre, StateT.run_pure]

/-- The complete prechallenge attempt charges every callback before acceptance or terminal rejection. This conservative bill does not drop local fixed-HKDF work. -/
theorem owner_pre_bound
    (source : FixedHkdfSha512NoSaltSource)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux qDecapsulation : Nat)
    (auxBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP predicate qAux)
    (decapsulationBound : ∀ ciphertext, (if predicate (.inr ciphertext) then 1 else 0) ≤ qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    ((simulateQ (pre source aux) (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary).IsQueryBoundP
      predicate (69 * (qAux + qDecapsulation)) :=
  PqxdhBeaconPhase2Bounds.native_interpreted_bound (pre source aux) predicate (qAux + qDecapsulation)
    (pre_step_bound source aux predicate qAux qDecapsulation auxBound decapsulationBound) decode raw state auxiliary

/-- Ordinary prechallenge uniform, base and selected-decapsulation costs remain separate. The decapsulation bill is conservative; no callback work is erased on rejection. -/
theorem owner_pre_classes
    (source : FixedHkdfSha512NoSaltSource)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (qUniform qBase qDecapsulation : Nat)
    (uniformBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemUniformQuery qUniform)
    (baseBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemBaseQuery qBase)
    (decapsulationBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    let run := (simulateQ (pre source aux) (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary
    run.IsQueryBoundP IsMlKemUniformQuery (69 * qUniform) ∧
      run.IsQueryBoundP IsMlKemBaseQuery (69 * qBase) ∧
      run.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (69 * (qDecapsulation + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using owner_pre_bound source aux IsMlKemUniformQuery qUniform 0 uniformBound
      (fun _ => by simp [IsMlKemUniformQuery]) decode raw state auxiliary
  · simpa only [Nat.add_zero] using owner_pre_bound source aux IsMlKemBaseQuery qBase 0 baseBound
      (fun _ => by simp [IsMlKemBaseQuery]) decode raw state auxiliary
  · exact owner_pre_bound source aux IsMlKemLogicalDecapsulationQuery qDecapsulation 1 decapsulationBound
      (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) decode raw state auxiliary

/-- Every later ordinary prechallenge program is charged at the complete original owner result and auxiliary state. -/
theorem continuation_pre_classes {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (qUniform qBase qDecapsulation : Nat)
    (uniformBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemUniformQuery qUniform)
    (baseBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemBaseQuery qBase)
    (decapsulationBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary)
    (next : ((Option Bytes × PqxdhBeaconPhase2Preparation.State I D (Option K)) × Auxiliary) →
      OracleComp (MlKemCCAOracleSpec baseSpec) Result)
    (uNext bNext dNext : Nat)
    (nextBound : ∀ result, (next result).IsQueryBoundP IsMlKemUniformQuery uNext ∧
      (next result).IsQueryBoundP IsMlKemBaseQuery bNext ∧
      (next result).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dNext) :
    let run := ((simulateQ (pre source aux) (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary) >>= next
    run.IsQueryBoundP IsMlKemUniformQuery (69 * qUniform + uNext) ∧
      run.IsQueryBoundP IsMlKemBaseQuery (69 * qBase + bNext) ∧
      run.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (69 * (qDecapsulation + 1) + dNext) := by
  have bounded := owner_pre_classes source aux qUniform qBase qDecapsulation uniformBound baseBound decapsulationBound decode raw state auxiliary
  exact ⟨isQueryBoundP_bind bounded.1 (fun result _ => (nextBound result).1),
    isQueryBoundP_bind bounded.2.1 (fun result _ => (nextBound result).2.1),
    isQueryBoundP_bind bounded.2.2 (fun result _ => (nextBound result).2.2)⟩

end BeaconcryptCore.Computational.PqxdhPhase2PreChallenge

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.pre_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.pre_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.owner_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.owner_pre

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.owner_pre_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.owner_pre_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.pre_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.pre_step_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.owner_pre_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.owner_pre_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.owner_pre_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.owner_pre_classes

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.continuation_pre_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PreChallenge.continuation_pre_classes
