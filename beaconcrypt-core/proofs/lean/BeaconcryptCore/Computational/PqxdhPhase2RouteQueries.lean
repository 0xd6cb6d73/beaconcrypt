import BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed

/-!
Ordinary CCA interpretation preserves every auxiliary callback reply and its complete private state. Selected decapsulation retains its exact ciphertext-dependent cost. Both retained-secret roots and challenge-matching private roots become local computations in that interpretation, so neither issues another ordinary decapsulation request.

These are structural query bounds for the actual routed callbacks, with arbitrary selected predicates and explicit auxiliary allowances. They do not transport costs through evaluated distribution equalities or instantiate the remaining source auxiliary callbacks. The supplied challenge secret occurs only in the ordinary root interpreter; the executable opaque callback program has no target secret-key argument.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2RouteQueries
open PqxdhBeaconPhase2Preparation (Bytes Word32 Ciphertext)
open PqxdhKemIndCca PqxdhJointKdfGame PqxdhInitializerSecrecy
open PqxdhChallengeSecretRouting PqxdhPhase2DecapsulationRouting
open PqxdhBeaconPhase2Routed

variable {ι : Type} {baseSpec : OracleSpec ι} {I D K X Response Auxiliary : Type}

/-- The ordinary interpreter forwards every original public request exactly once. -/
theorem publicLift_route
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret) :
    route (baseSpec := baseSpec) source challenge supplied ∘ₛ publicLift =
      QueryImpl.id' (MlKemCCAOracleSpec baseSpec) := by
  funext query
  exact simulateQ_spec_query (route source challenge supplied) (.inl query)

/-- Full private callback replies and poststates survive both forwarding layers. -/
theorem sharedAux_route
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (query : (AuxSpec I D K X Response).Domain) (auxiliary : Auxiliary) :
    simulateQ (route source challenge supplied) ((sharedAux aux query).run auxiliary) =
      (aux query).run auxiliary := by
  exact (QueryImpl.simulateQ_compose _ _ _).symm.trans
    ((congrArg (fun impl => simulateQ impl ((aux query).run auxiliary))
      (publicLift_route source challenge supplied)).trans (simulateQ_id' _))

/-- Auxiliary bounds transfer through exact full-state forwarding. -/
theorem sharedAux_route_bound
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (query : (AuxSpec I D K X Response).Domain) (auxiliary : Auxiliary)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (q : Nat) (bound : ((aux query).run auxiliary).IsQueryBoundP predicate q) :
    (simulateQ (route source challenge supplied) ((sharedAux aux query).run auxiliary)).IsQueryBoundP
      predicate q := by
  rw [sharedAux_route]
  exact bound

/-- Actual typed ciphertext bytes retain the original ordinary optional decapsulation result. -/
theorem decapCall_route
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret) (value : Ciphertext) :
    simulateQ (route (baseSpec := baseSpec) source challenge supplied)
      (PqxdhPhase2InputBytes.decapCall challenge value) =
        ordinaryDecapsulate challenge (PqxdhPhase2InputBytes.ciphertext value) :=
  decapsulate_reduction source challenge supplied (PqxdhPhase2InputBytes.ciphertext value)

/-- Route the base oracle while retaining the whole private auxiliary state. -/
noncomputable def routedHandles
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec)))) :=
  (route source challenge supplied).mapStateTBase (handles source challenge aux)

/-- Selected decapsulation preserves the private state and original optional shared handle. -/
theorem routedHandles_decap
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (value : Ciphertext) (auxiliary : Auxiliary) :
    ((routedHandles source challenge supplied aux (.inl (.decapsulate value none))).run auxiliary) =
      (fun reply => (reply, auxiliary)) <$>
        ordinaryDecapsulate challenge (PqxdhPhase2InputBytes.ciphertext value) := by
  change simulateQ (route source challenge supplied)
    ((fun reply => (reply, auxiliary)) <$> PqxdhPhase2InputBytes.decapCall challenge value) = _
  rw [simulateQ_map, decapCall_route]

/-- Every private root becomes a local computation, including the challenge-matching case. -/
theorem rootCall_route_bound
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret) (shared : Shared) (dh1 dh2 dh3 dh4 : Word32)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    (simulateQ (route (baseSpec := baseSpec) source challenge supplied)
      (PqxdhPhase2InputBytes.rootCall source challenge shared dh1 dh2 dh3 dh4)).IsQueryBoundP
        predicate 0 := by
  rw [PqxdhPhase2InputBytes.rootCall_reduction]
  trivial

/-- Exact selected ordinary cost of one opaque callback; local wiping and root computation have no oracle cost. -/
noncomputable def callbackCost
    (challenge : MlKem768Ciphertext)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux : Nat) :
    (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared).Domain → Nat
  | .inl (.decapsulate value none) =>
      if PqxdhPhase2InputBytes.ciphertext value = challenge then 0
      else if predicate (.inr (PqxdhPhase2InputBytes.ciphertext value)) then 1 else 0
  | .inl (.eraseShared _) => 0
  | .inr (.inr (.root _)) => 0
  | _ => qAux

/-- Structural callback accounting keeps the complete private state for every optional reply. -/
theorem routedHandles_bound
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux : Nat)
    (auxBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP predicate qAux)
    (query : (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared).Domain)
    (auxiliary : Auxiliary) :
    ((routedHandles source challenge supplied aux query).run auxiliary).IsQueryBoundP
      predicate (callbackCost challenge predicate qAux query) := by
  rcases query with pre | tail
  · cases pre
    all_goals first
      | exact sharedAux_route_bound source challenge supplied aux _ auxiliary predicate qAux (auxBound _ auxiliary)
      | skip
    case decapsulate value key =>
      cases key with
      | none =>
          rw [routedHandles_decap]
          exact (isQueryBoundP_map_iff (p := predicate) _ (fun reply => (reply, auxiliary)) _).mpr
            (ordinaryDecapsulate_bound challenge (PqxdhPhase2InputBytes.ciphertext value) predicate)
      | some prior =>
          change (simulateQ (route source challenge supplied)
            ((fun pair => (Option.map (fun value => Shared.known (PqxdhPhase2InputBytes.word value)) pair.1, pair.2)) <$>
              (sharedAux aux (.localDecapsulation value prior)).run auxiliary)).IsQueryBoundP predicate qAux
          rw [simulateQ_map, isQueryBoundP_map_iff]
          exact sharedAux_route_bound source challenge supplied aux _ auxiliary predicate qAux (auxBound _ auxiliary)
    case eraseShared =>
      simp [routedHandles, QueryImpl.mapStateTBase, handles, callbackCost, StateT.run_pure]
  · rcases tail with query | tail
    · exact sharedAux_route_bound source challenge supplied aux _ auxiliary predicate qAux (auxBound _ auxiliary)
    · cases tail
      all_goals first
        | exact sharedAux_route_bound source challenge supplied aux _ auxiliary predicate qAux (auxBound _ auxiliary)
        | skip
      case root secrets =>
        change (simulateQ (route source challenge supplied)
          ((fun reply => (reply, auxiliary)) <$>
            PqxdhPhase2InputBytes.rootCall source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4)).IsQueryBoundP predicate 0
        rw [simulateQ_map, isQueryBoundP_map_iff]
        exact rootCall_route_bound source challenge supplied secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4 predicate

/-- Coarse allowances suitable for the source owner partition: auxiliary, selected decapsulation, and root. -/
def callbackAllowance (qAux qDecapsulation : Nat) :
    (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared).Domain → Nat
  | .inl (.decapsulate _ none) => qDecapsulation
  | .inr (.inr (.root _)) => 0
  | _ => qAux

/-- A uniform selected-decapsulation allowance dominates the exact ciphertext-dependent cost. -/
theorem callbackCost_le
    (challenge : MlKem768Ciphertext)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux qDecapsulation : Nat)
    (decapsulationBound : ∀ ciphertext, (if predicate (.inr ciphertext) then 1 else 0) ≤ qDecapsulation)
    (query : (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared).Domain) :
    callbackCost challenge predicate qAux query ≤ callbackAllowance qAux qDecapsulation query := by
  rcases query with pre | tail
  · cases pre <;> simp only [callbackCost, callbackAllowance, Nat.le_refl, Nat.zero_le]
    case decapsulate value key =>
      cases key with
      | none =>
          dsimp only
          split <;> first | exact Nat.zero_le _ | exact decapsulationBound _
      | some prior => exact Nat.le_refl _
  · rcases tail with query | tail
    · exact Nat.le_refl _
    · cases tail <;> exact Nat.le_refl _

/-- Every callback pays its original auxiliary or selected-decapsulation allowance; roots remain free of ordinary oracle requests. -/
theorem routedHandles_allowance
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux qDecapsulation : Nat)
    (auxBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP predicate qAux)
    (decapsulationBound : ∀ ciphertext, (if predicate (.inr ciphertext) then 1 else 0) ≤ qDecapsulation)
    (query : (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared).Domain)
    (auxiliary : Auxiliary) :
    ((routedHandles source challenge supplied aux query).run auxiliary).IsQueryBoundP
      predicate (callbackAllowance qAux qDecapsulation query) :=
  (routedHandles_bound source challenge supplied aux predicate qAux auxBound query auxiliary).mono
    (callbackCost_le challenge predicate qAux qDecapsulation decapsulationBound query)

/-- Routing the complete adaptive callback program retains its result and complete private poststate. -/
theorem routed_program
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    {Result : Type}
    (program : OracleComp (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared) Result)
    (auxiliary : Auxiliary) :
    simulateQ (route source challenge supplied)
      ((simulateQ (handles source challenge aux) program).run auxiliary) =
        (simulateQ (routedHandles source challenge supplied aux) program).run auxiliary :=
  QueryImpl.simulateQ_mapStateTBase_run _ _ _ _

end BeaconcryptCore.Computational.PqxdhPhase2RouteQueries

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.publicLift_route' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.publicLift_route

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.sharedAux_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.sharedAux_route

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.sharedAux_route_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.sharedAux_route_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.decapCall_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.decapCall_route

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.routedHandles_decap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.routedHandles_decap

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.rootCall_route_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.rootCall_route_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.routedHandles_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.routedHandles_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.callbackCost_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.callbackCost_le

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.routedHandles_allowance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.routedHandles_allowance

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.routed_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2RouteQueries.routed_program
