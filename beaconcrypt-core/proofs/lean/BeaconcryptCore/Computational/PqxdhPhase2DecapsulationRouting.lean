import BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds

/-!
The live Beacon decapsulates before its four DH calls. A private handle retains the result at that original point: the selected challenge has an opaque marker, while every other ciphertext carries the actual optional decapsulation result. Only a later private root callback interprets the marker. Public decapsulation remains on the ordinary CCA interface and public HKDF remains real.

The selected-ciphertext substitution uses the existing complete functional-decapsulation and supported recipient-correctness contract. Equality of returned marginal distributions alone cannot discard native callback effects. The marker interpretation appears only in the mathematical source correspondence and inside the ordinary reduction; it is never supplied to a public program or secret-input sampler.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting
open PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhHiddenRoot PqxdhJointKdfGame PqxdhSecretInputKdf
open PqxdhChallengeSecretRouting
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Private protocol value; the public delivery interface never returns this type. -/
inductive Shared where
  | challenge
  | known : MlKemSharedSecret → Shared

def materialize (supplied : MlKemSharedSecret) : Shared → MlKemSharedSecret
  | .challenge => supplied
  | .known secret => secret

/-- Run at the source decapsulation point, before any of the original DH requests. -/
noncomputable def decapsulate (challenge ciphertext : MlKem768Ciphertext) :
    OracleComp (LocalPostSpec baseSpec) (Option Shared) :=
  if ciphertext = challenge then pure (some .challenge)
  else Option.map Shared.known <$>
    ((LocalPostSpec baseSpec).query (.inl (.inr ciphertext)) :
      OracleComp (LocalPostSpec baseSpec) (Option MlKemSharedSecret))

/-- The original DH coordinates accompany the retained private value; an already recovered secret is never decapsulated twice. -/
noncomputable def derive (source : FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (shared : Shared) (coordinates : KnownPqxdhRootCoordinates) :
    OracleComp (LocalPostSpec baseSpec) (Option RootOutput) :=
  match shared with
  | .challenge => (LocalPostSpec baseSpec).query (.inr ⟨challenge, coordinates⟩)
  | .known secret => pure (some (productionHiddenRoot source coordinates secret))

/-- Actual optional source decapsulation is recovered with all effects of every nonchallenge request intact. -/
theorem decapsulate_native
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (ciphertext : MlKem768Ciphertext) :
    Option.map (materialize supplied) <$>
      simulateQ (actualImpl source kem secret challenge) (decapsulate challenge ciphertext) =
        kem.decaps secret ciphertext := by
  classical
  by_cases same : ciphertext = challenge
  · subst ciphertext
    simp only [decapsulate, if_true, simulateQ_pure, map_pure, Option.map_some, materialize, agreement]
  · simp only [decapsulate, if_neg same, simulateQ_map, Functor.map_map]
    have mapped : (fun a => Option.map (materialize supplied) (Option.map Shared.known a)) = id := by
      funext value
      cases value <;> rfl
    rw [mapped, id_map]
    exact (simulateQ_spec_query (actualImpl source kem secret challenge) (.inl (.inr ciphertext))).trans
      (publicImpl_other kem secret challenge ciphertext same)

/-- Root derivation consumes the retained result, with no second nonchallenge decapsulation and the original four coordinates unchanged. -/
theorem derive_native
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (shared : Shared) (coordinates : KnownPqxdhRootCoordinates) :
    simulateQ (actualImpl source kem secret challenge) (derive source challenge shared coordinates) =
      pure (some (productionHiddenRoot source coordinates (materialize supplied shared))) := by
  cases shared with
  | challenge =>
      exact (simulateQ_spec_query (actualImpl source kem secret challenge) (.inr ⟨challenge, coordinates⟩)).trans
        (by simp only [actualImpl, agreement, pure_bind, Option.map_some, materialize]; rfl)
  | known value => exact simulateQ_pure _ _

/-- The existing ordinary reduction resolves the opaque marker only at the private root callback. -/
theorem derive_reduction
    (source : FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (shared : Shared) (coordinates : KnownPqxdhRootCoordinates) :
    simulateQ (route (baseSpec := baseSpec) source challenge supplied)
      (derive source challenge shared coordinates) =
        pure (some (productionHiddenRoot source coordinates (materialize supplied shared))) := by
  cases shared with
  | challenge =>
      exact (simulateQ_spec_query (route (baseSpec := baseSpec) source challenge supplied)
        (.inr ⟨challenge, coordinates⟩)).trans (route_challenge source challenge supplied coordinates)
  | known value => exact simulateQ_pure _ _

/-- Recipient correctness on the actual key-generation and encapsulation support discharges the selected-ciphertext equation. -/
theorem decapsulate_supported_native
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    {pk : MlKem768PublicKey} {secret : KemSK}
    (generated : (pk, secret) ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen))
    {challenge : MlKem768Ciphertext} {supplied : MlKemSharedSecret}
    (encapsulated : (challenge, supplied) ∈ support (simulateQ (kemAmbientImpl baseImpl) (kem.encaps pk)))
    (ciphertext : MlKem768Ciphertext) :
    Option.map (materialize supplied) <$>
      simulateQ (actualImpl source kem secret challenge) (decapsulate challenge ciphertext) =
        kem.decaps secret ciphertext :=
  decapsulate_native source kem secret challenge supplied
    (honest_decapsulation_program baseImpl kem functional correct generated encapsulated) ciphertext

/-- Every nonchallenge callback forwards one actual ordinary request; the opaque challenge marker requires none. -/
theorem decapsulate_bound
    (challenge ciphertext : MlKem768Ciphertext)
    (predicate : (LocalPostSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    (decapsulate (baseSpec := baseSpec) challenge ciphertext).IsQueryBoundP predicate
      (if ciphertext = challenge then 0 else if predicate (.inl (.inr ciphertext)) then 1 else 0) := by
  classical
  by_cases same : ciphertext = challenge
  · simp only [decapsulate, if_pos same, isQueryBoundP_pure]
  · simp only [decapsulate, if_neg same, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec) (p := predicate)
      (.inl (.inr ciphertext)) _).2 (by split_ifs <;> simp_all)

/-- Only the challenge marker issues one correlated-root request. Real fixed-HKDF work on a known secret remains local computation. -/
theorem derive_bound
    (source : FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (shared : Shared) (coordinates : KnownPqxdhRootCoordinates)
    (predicate : (LocalPostSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    (derive (baseSpec := baseSpec) source challenge shared coordinates).IsQueryBoundP predicate
      (match shared with
       | .challenge => if predicate (.inr ⟨challenge, coordinates⟩) then 1 else 0
       | .known _ => 0) := by
  cases shared with
  | challenge =>
      exact (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec) (p := predicate)
        (.inr ⟨challenge, coordinates⟩) _).2 (by split_ifs <;> simp_all)
  | known value => exact isQueryBoundP_pure _ _ _

/-- The ordinary reduction answers the original private decapsulation point without receiving the KEM secret key. -/
noncomputable def ordinaryDecapsulate (challenge ciphertext : MlKem768Ciphertext) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Option Shared) :=
  if ciphertext = challenge then pure (some .challenge)
  else Option.map Shared.known <$>
    ((MlKemCCAOracleSpec baseSpec).query (.inr ciphertext) :
      OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret))

/-- The original point is independent of the supplied challenge-secret bytes and later DH coordinates. -/
theorem decapsulate_reduction
    (source : FixedHkdfSha512NoSaltSource)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (ciphertext : MlKem768Ciphertext) :
    simulateQ (route (baseSpec := baseSpec) source challenge supplied)
      (decapsulate challenge ciphertext) = ordinaryDecapsulate challenge ciphertext := by
  classical
  by_cases same : ciphertext = challenge
  · simp only [decapsulate, ordinaryDecapsulate, if_pos same, simulateQ_pure]
  · simp only [decapsulate, ordinaryDecapsulate, if_neg same, simulateQ_map]
    exact congrArg (Functor.map (Option.map Shared.known))
      (simulateQ_spec_query (route (baseSpec := baseSpec) source challenge supplied) (.inl (.inr ciphertext)))

/-- Ordinary decapsulation requests remain explicitly charged; no uniform or base query is generated by the routing code. -/
theorem ordinaryDecapsulate_bound
    (challenge ciphertext : MlKem768Ciphertext)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    (ordinaryDecapsulate (baseSpec := baseSpec) challenge ciphertext).IsQueryBoundP predicate
      (if ciphertext = challenge then 0 else if predicate (.inr ciphertext) then 1 else 0) := by
  classical
  by_cases same : ciphertext = challenge
  · simp only [ordinaryDecapsulate, if_pos same, isQueryBoundP_pure]
  · simp only [ordinaryDecapsulate, if_neg same, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff (spec := MlKemCCAOracleSpec baseSpec) (p := predicate)
      (.inr ciphertext) _).2 (by split_ifs <;> simp_all)

end BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.decapsulate_native' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.decapsulate_native

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.derive_native' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.derive_native

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.derive_reduction' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.derive_reduction

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.decapsulate_supported_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.decapsulate_supported_native

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.decapsulate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.decapsulate_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.derive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.derive_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.decapsulate_reduction' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.decapsulate_reduction

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.ordinaryDecapsulate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DecapsulationRouting.ordinaryDecapsulate_bound
