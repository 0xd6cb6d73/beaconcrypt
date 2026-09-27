import BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed
import BeaconcryptCore.Computational.PqxdhBeaconPhase2SharedBounds
import BeaconcryptCore.Computational.FinitePartitionQueryBounds

/-!
Concrete Phase2 dispatch retains the full private auxiliary state while charging every routed request. Public forwarding cannot issue a private root request. The original selected decapsulation site and private root site are separate syntactic classes, and every other callback keeps its stated underlying allowance. These are oracle-query bounds; codec, local primitive and deterministic source computation remain explicit work.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds
open PqxdhBeaconPhase2Routed PqxdhBeaconPhase2SharedBounds
open PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
open PqxdhPhase2DecapsulationRouting PqxdhKemIndCca PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {I D K X Response Auxiliary : Type}

/-- Original auxiliary callbacks have only public capabilities, even when they update arbitrary private state. -/
theorem sharedAux_no_root
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (query : (AuxSpec I D K X Response).Domain) (auxiliary : Auxiliary) :
    ((sharedAux aux query).run auxiliary).IsQueryBoundP (IsPrivateRoot (baseSpec := baseSpec)) 0 := by
  apply RawCtxSourceOpen.simulate_bound publicLift (fun _ => False) (IsPrivateRoot (baseSpec := baseSpec))
    ((aux query).run auxiliary) 0 (isQueryBoundP_false _ _)
  intro request
  exact (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec)
    (p := IsPrivateRoot (baseSpec := baseSpec)) (.inl request) 0).mpr (by simp [IsPrivateRoot])

/-- Only the actual private-root callback can produce a private-root request. -/
theorem handles_root_step
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (query : (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared).Domain)
    (auxiliary : Auxiliary) :
    ((handles source challenge aux query).run auxiliary).IsQueryBoundP
      (IsPrivateRoot (baseSpec := baseSpec)) (if rootCall query = true then 1 else 0) := by
  rcases query with pre | tail
  · cases pre <;> simp only [rootCall, Bool.false_eq_true, if_false]
    all_goals first | exact sharedAux_no_root aux _ auxiliary | skip
    case eraseShared => simp [handles, StateT.run_pure]
    case decapsulate value key =>
      cases key with
      | none =>
          have handled :
              (handles source challenge aux (.inl (.decapsulate value none))).run auxiliary =
                (fun reply => (reply, auxiliary)) <$>
                  PqxdhPhase2InputBytes.decapCall challenge value := by
            rw [show handles source challenge aux (.inl (.decapsulate value none)) =
              liftM (PqxdhPhase2InputBytes.decapCall challenge value) by rfl]
            simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift,
              StateT.run, bind_pure_comp]
          rw [handled]
          apply (isQueryBoundP_map_iff (p := IsPrivateRoot (baseSpec := baseSpec))
            (PqxdhPhase2InputBytes.decapCall challenge value) (fun reply => (reply, auxiliary)) 0).mpr
          apply (PqxdhPhase2InputBytes.decapCall_bound challenge value
            (IsPrivateRoot (baseSpec := baseSpec))).mono
          by_cases selected : PqxdhPhase2InputBytes.ciphertext value = challenge <;>
            simp [selected, IsPrivateRoot]
      | some prior =>
          have handled :
              (handles source challenge aux (.inl (.decapsulate value (some prior)))).run auxiliary =
                (fun pair =>
                  (Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) pair.1,
                    pair.2)) <$>
                  (sharedAux aux (.localDecapsulation value prior)).run auxiliary := by
            rw [show handles source challenge aux (.inl (.decapsulate value (some prior))) =
              Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) <$>
                sharedAux aux (.localDecapsulation value prior) by rfl]
            exact StateT.run_map _ _ _
          rw [handled]
          exact (isQueryBoundP_map_iff (p := IsPrivateRoot (baseSpec := baseSpec))
            ((sharedAux aux (.localDecapsulation value prior)).run auxiliary)
            (fun pair => (Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) pair.1, pair.2)) 0).mpr
              (sharedAux_no_root aux _ auxiliary)
  · rcases tail with query | tail
    · exact sharedAux_no_root aux _ auxiliary
    · cases tail <;> simp only [rootCall, isRoot, Bool.false_eq_true, if_false, if_true]
      all_goals first | exact sharedAux_no_root aux _ auxiliary | skip
      case root secrets =>
        have handled :
            (handles source challenge aux (.inr (.inr (.root secrets)))).run auxiliary =
              (fun reply => (reply, auxiliary)) <$>
                PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1
                  secrets.dh2 secrets.dh3 secrets.dh4 := by
          rw [show handles source challenge aux (.inr (.inr (.root secrets))) =
            liftM (PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1
              secrets.dh2 secrets.dh3 secrets.dh4) by rfl]
          simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift,
            StateT.run, bind_pure_comp]
        rw [handled]
        apply (isQueryBoundP_map_iff (p := IsPrivateRoot (baseSpec := baseSpec))
          (PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4)
          (fun reply => (reply, auxiliary)) 1).mpr
        apply (PqxdhPhase2InputBytes.rootCall_bound source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4
          (IsPrivateRoot (baseSpec := baseSpec))).mono
        cases secrets.shared <;> simp [IsPrivateRoot]

/-- A complete concrete Phase2 attempt issues at most one private-root request, independently of all auxiliary query costs. -/
theorem owner_private_root
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    ((simulateQ (handles source challenge aux)
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary).IsQueryBoundP
        (IsPrivateRoot (baseSpec := baseSpec)) 1 :=
  (owner_root decode raw state).simulateQ_run_StateT_of_step (handles_root_step source challenge aux) auxiliary

/-- Every public query class keeps its original auxiliary allowance under exact forwarding. -/
theorem sharedAux_public
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (query : (AuxSpec I D K X Response).Domain) (auxiliary : Auxiliary)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (budget : Nat) (bounded : ((aux query).run auxiliary).IsQueryBoundP predicate budget) :
    ((sharedAux aux query).run auxiliary).IsQueryBoundP (PublicClass predicate) budget := by
  apply RawCtxSourceOpen.simulate_bound publicLift predicate (PublicClass predicate)
    ((aux query).run auxiliary) budget bounded
  intro request
  exact (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec) (p := PublicClass predicate)
    (.inl request) _).mpr (by by_cases selected : predicate request <;> simp [PublicClass, selected])

/-- Separate the selected-key decapsulation, root processing and all original auxiliary work. -/
def kind : (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared).Domain → Fin 3
  | .inl (.decapsulate _ none) => 1
  | .inr (.inr (.root _)) => 2
  | _ => 0

def allowance (index : Fin 3) : Nat := if index = 0 then 69 else 1

/-- All auxiliary work retains the 69-call allowance; the selected decapsulation and root sites each occur at most once. -/
theorem owner_kind
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (index : Fin 3) :
    (PqxdhBeaconPhase2Shared.owner (X := X) (Response := Response) (Shared := Shared) decode raw state).IsQueryBoundP
      (fun query => kind query = index) (allowance index) := by
  fin_cases index
  · exact IsQueryBoundP.of_imp (fun _ _ => trivial)
      ((isQueryBoundP_true_iff _ _).mpr (owner_bound decode raw state))
  · apply IsQueryBoundP.of_imp (p' := fun query => decapsulationCall query = true) _
      (owner_decapsulation decode raw state)
    intro query selected
    unfold kind at selected
    split at selected <;> simp_all [decapsulationCall, isDecapsulation]
  · apply IsQueryBoundP.of_imp (p' := fun query => rootCall query = true) _ (owner_root decode raw state)
    intro query selected
    unfold kind at selected
    split at selected <;> simp_all [rootCall, isRoot]

def publicCost (qAux qDecapsulation : Nat) (index : Fin 3) : Nat :=
  if index = 0 then qAux else if index = 1 then qDecapsulation else 0

/-- Public costs charge actual auxiliary callbacks and the single selected decapsulation, while root requests use their separate private class. -/
theorem handles_public_step
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux qDecapsulation : Nat)
    (auxBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP predicate qAux)
    (decapsulationBound : ∀ ciphertext, (if predicate (.inr ciphertext) then 1 else 0) ≤ qDecapsulation)
    (query : (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared).Domain)
    (auxiliary : Auxiliary) :
    ((handles source challenge aux query).run auxiliary).IsQueryBoundP (PublicClass predicate)
      (publicCost qAux qDecapsulation (kind query)) := by
  rcases query with pre | tail
  · cases pre
    all_goals first | exact sharedAux_public aux _ auxiliary predicate qAux (auxBound _ auxiliary) | skip
    case eraseShared => simp [handles, StateT.run_pure]
    case decapsulate value key =>
      cases key with
      | none =>
          have handled :
              (handles source challenge aux (.inl (.decapsulate value none))).run auxiliary =
                (fun reply => (reply, auxiliary)) <$>
                  PqxdhPhase2InputBytes.decapCall challenge value := by
            rw [show handles source challenge aux (.inl (.decapsulate value none)) =
              liftM (PqxdhPhase2InputBytes.decapCall challenge value) by rfl]
            simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift,
              StateT.run, bind_pure_comp]
          rw [handled]
          change ((fun reply => (reply, auxiliary)) <$>
            PqxdhPhase2InputBytes.decapCall challenge value).IsQueryBoundP
              (PublicClass predicate) qDecapsulation
          apply (isQueryBoundP_map_iff (p := PublicClass predicate)
            (PqxdhPhase2InputBytes.decapCall challenge value) (fun reply => (reply, auxiliary)) qDecapsulation).mpr
          apply (PqxdhPhase2InputBytes.decapCall_bound challenge value (PublicClass predicate)).mono
          split <;> first | exact Nat.zero_le _ | exact decapsulationBound _
      | some prior =>
          have handled :
              (handles source challenge aux (.inl (.decapsulate value (some prior)))).run auxiliary =
                (fun pair =>
                  (Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) pair.1,
                    pair.2)) <$>
                  (sharedAux aux (.localDecapsulation value prior)).run auxiliary := by
            rw [show handles source challenge aux (.inl (.decapsulate value (some prior))) =
              Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) <$>
                sharedAux aux (.localDecapsulation value prior) by rfl]
            exact StateT.run_map _ _ _
          rw [handled]
          change ((fun pair =>
            (Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) pair.1,
              pair.2)) <$> (sharedAux aux (.localDecapsulation value prior)).run auxiliary).IsQueryBoundP
                (PublicClass predicate) qAux
          exact (isQueryBoundP_map_iff (p := PublicClass predicate)
            ((sharedAux aux (.localDecapsulation value prior)).run auxiliary)
            (fun pair => (Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) pair.1, pair.2)) qAux).mpr
              (sharedAux_public aux _ auxiliary predicate qAux (auxBound _ auxiliary))
  · rcases tail with query | tail
    · exact sharedAux_public aux _ auxiliary predicate qAux (auxBound _ auxiliary)
    · cases tail
      all_goals first | exact sharedAux_public aux _ auxiliary predicate qAux (auxBound _ auxiliary) | skip
      case root secrets =>
        have handled :
            (handles source challenge aux (.inr (.inr (.root secrets)))).run auxiliary =
              (fun reply => (reply, auxiliary)) <$>
                PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1
                  secrets.dh2 secrets.dh3 secrets.dh4 := by
          rw [show handles source challenge aux (.inr (.inr (.root secrets))) =
            liftM (PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1
              secrets.dh2 secrets.dh3 secrets.dh4) by rfl]
          simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift,
            StateT.run, bind_pure_comp]
        rw [handled]
        change ((fun reply => (reply, auxiliary)) <$>
          PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1
            secrets.dh2 secrets.dh3 secrets.dh4).IsQueryBoundP (PublicClass predicate) 0
        apply (isQueryBoundP_map_iff (p := PublicClass predicate)
          (PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4)
          (fun reply => (reply, auxiliary)) 0).mpr
        apply (PqxdhPhase2InputBytes.rootCall_bound source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4
          (PublicClass predicate)).mono
        cases secrets.shared <;> simp [PublicClass]

/-- A complete attempt charges every auxiliary class allowance and one selected decapsulation allowance, with no acceptance premise. -/
theorem owner_public
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux qDecapsulation : Nat)
    (auxBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP predicate qAux)
    (decapsulationBound : ∀ ciphertext, (if predicate (.inr ciphertext) then 1 else 0) ≤ qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    ((simulateQ (handles source challenge aux)
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary).IsQueryBoundP
        (PublicClass predicate) (69 * qAux + qDecapsulation) := by
  simpa [Fin.sum_univ_three, publicCost, allowance, Nat.mul_comm] using
    FinitePartitionQueryBounds.weighted_bound kind (publicCost qAux qDecapsulation) allowance
      (handles source challenge aux) (PublicClass predicate)
      (PqxdhBeaconPhase2Shared.owner decode raw state) (owner_kind decode raw state)
      (handles_public_step source challenge aux predicate qAux qDecapsulation auxBound decapsulationBound) auxiliary

/-- Uniform, base, logical-decapsulation and private-root bills are explicit for the original complete attempt. -/
theorem owner_classes
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (qUniform qBase qDecapsulation : Nat)
    (uniformBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemUniformQuery qUniform)
    (baseBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemBaseQuery qBase)
    (decapsulationBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    PostBounds ((simulateQ (handles source challenge aux)
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary)
      (69 * qUniform) (69 * qBase) (69 * qDecapsulation + 1) 1 := by
  constructor
  · simpa only [Nat.add_zero] using owner_public source challenge aux IsMlKemUniformQuery qUniform 0 uniformBound
      (fun _ => by simp [IsMlKemUniformQuery]) decode raw state auxiliary
  · simpa only [Nat.add_zero] using owner_public source challenge aux IsMlKemBaseQuery qBase 0 baseBound
      (fun _ => by simp [IsMlKemBaseQuery]) decode raw state auxiliary
  · exact owner_public source challenge aux IsMlKemLogicalDecapsulationQuery qDecapsulation 1 decapsulationBound
      (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) decode raw state auxiliary
  · exact owner_private_root source challenge aux decode raw state auxiliary

/-- The original complete poststate enters the continuation, whose four independent allowances are all added explicitly. -/
theorem continuation_classes {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (qUniform qBase qDecapsulation : Nat)
    (uniformBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemUniformQuery qUniform)
    (baseBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemBaseQuery qBase)
    (decapsulationBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary)
    (next : ((Option PqxdhBeaconPhase2Preparation.Bytes × PqxdhBeaconPhase2Preparation.State I D (Option K)) × Auxiliary) →
      OracleComp (LocalPostSpec baseSpec) Result)
    (uNext bNext dNext rNext : Nat)
    (nextBound : ∀ result, PostBounds (next result) uNext bNext dNext rNext) :
    PostBounds (((simulateQ (handles source challenge aux)
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary) >>= next)
      (69 * qUniform + uNext) (69 * qBase + bNext) (69 * qDecapsulation + 1 + dNext) (1 + rNext) := by
  have before := owner_classes source challenge aux qUniform qBase qDecapsulation
    uniformBound baseBound decapsulationBound decode raw state auxiliary
  exact ⟨isQueryBoundP_bind before.uniforms (fun result _ => (nextBound result).uniforms),
    isQueryBoundP_bind before.bases (fun result _ => (nextBound result).bases),
    isQueryBoundP_bind before.decaps (fun result _ => (nextBound result).decaps),
    isQueryBoundP_bind before.privateRoots (fun result _ => (nextBound result).privateRoots)⟩

end BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.sharedAux_no_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.sharedAux_no_root

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.handles_root_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.handles_root_step

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.owner_private_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.owner_private_root

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.sharedAux_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.sharedAux_public

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.owner_kind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.owner_kind

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.handles_public_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.handles_public_step

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.owner_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.owner_public

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.owner_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.owner_classes

/--
info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.continuation_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds.continuation_classes
