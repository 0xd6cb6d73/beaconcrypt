import BeaconcryptCore.Computational.PqxdhServerRootPreparation

/-!
The exact optional Server prefix keeps its selected static-DH result as public peer metadata. The ordinary functional availability contract covers the native converted identity scalar at every supplied peer encoding. Actual static-DH evaluation remains in the native mathematical interpretation; the executable prefix calls only its public admission predicate and the original instrumentation. All auxiliary callbacks and generator order are unchanged.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerStaticDhSource
open PqxdhJointIdentity PqxdhServerRootPreparation
open PqxdhPhase2GapDhSource (peer)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhRootTableInitialization (rootArray)

/-- Ordinary native optional-result correctness for the actually converted identity scalar. It says precisely which public inputs return a value; it asserts neither protocol admission nor secrecy. -/
structure PublicDomain (joint : Primitives) where
  accepts : PeerEncoding → Bool
  available : ∀ seed input, (joint.staticDh seed input).isSome = accepts input

def materialize (joint : Primitives) (seed : IdentitySeed) (reference : PeerEncoding) : Word32 :=
  rootArray ((joint.staticDh seed reference).getD PqxdhJointGapDh.zeroDh)

def selectedReply {joint : Primitives} (domain : PublicDomain joint) (input : Word32) : Option PeerEncoding :=
  if domain.accepts (peer input) then some (peer input) else none

/-- The public validation predicate reproduces the complete optional static-DH outcome. The secret seed occurs only in the mathematical realization. -/
theorem selected_reply (joint : Primitives) (domain : PublicDomain joint) (seed : IdentitySeed) (input : Word32) :
    (selectedReply domain input).map (materialize joint seed) =
      (joint.staticDh seed (peer input)).map rootArray := by
  cases actual : joint.staticDh seed (peer input) <;>
    simp [selectedReply, ← domain.available seed (peer input), materialize, actual]

def concreteInputs (joint : Primitives) (seed : IdentitySeed) {Reader E : Type}
    (input : Inputs Reader E PeerEncoding) : Inputs Reader E Word32 :=
  ⟨input.verified, input.ephemeral, input.ciphertext, input.convertedIdentity,
    materialize joint seed input.first, input.second, input.third, input.fourth, input.kem⟩

/-- Native source semantics evaluate only the static-DH branch with the unavailable Server seed, retaining its actual call effects. -/
def nativeImpl (joint : Primitives) (seed : IdentitySeed) {Reader E : Type} {m : Type → Type} [Monad m]
    (aux : QueryImpl (Spec Reader E Unit) m) (visit : Word32 → m Unit) : QueryImpl (Spec Reader E Word32) m
  | .decode raw => aux (.decode raw)
  | .identity reader => aux (.identity reader)
  | .identityPoint identity => aux (.identityPoint identity)
  | .pqField reader => aux (.pqField reader)
  | .preField reader => aux (.preField reader)
  | .oneField reader => aux (.oneField reader)
  | .verify identity bytes => aux (.verify identity bytes)
  | .registrationStatus rid => aux (.registrationStatus rid)
  | .reserveRegistration => aux (.reserveRegistration)
  | .parseDh point => aux (.parseDh point)
  | .generate => aux (.generate)
  | .parseKem key => aux (.parseKem key)
  | .encapsulate key => aux (.encapsulate key)
  | .publicConversion identity => aux (.publicConversion identity)
  | .privateConversion => aux (.privateConversion)
  | .ephemeralDh secret point => aux (.ephemeralDh secret point)
  | .staticDh input => do
      let _ ← visit input
      pure ((joint.staticDh seed (peer input)).map rootArray)

/-- Executable unavailable-DH interpretation has no selected seed or secret DH reply. The original static-call work and every other native effect remain. -/
def prefixImpl {joint : Primitives} (domain : PublicDomain joint) {Reader E : Type} {m : Type → Type} [Monad m]
    (aux : QueryImpl (Spec Reader E Unit) m) (visit : Word32 → m Unit) : QueryImpl (Spec Reader E PeerEncoding) m
  | .decode raw => aux (.decode raw)
  | .identity reader => aux (.identity reader)
  | .identityPoint identity => aux (.identityPoint identity)
  | .pqField reader => aux (.pqField reader)
  | .preField reader => aux (.preField reader)
  | .oneField reader => aux (.oneField reader)
  | .verify identity bytes => aux (.verify identity bytes)
  | .registrationStatus rid => aux (.registrationStatus rid)
  | .reserveRegistration => aux (.reserveRegistration)
  | .parseDh point => aux (.parseDh point)
  | .generate => aux (.generate)
  | .parseKem key => aux (.parseKem key)
  | .encapsulate key => aux (.encapsulate key)
  | .publicConversion identity => aux (.publicConversion identity)
  | .privateConversion => aux (.privateConversion)
  | .ephemeralDh secret point => aux (.ephemeralDh secret point)
  | .staticDh input => do
      let _ ← visit input
      pure (selectedReply domain input)

/-- The whole ordered post-verification source prefix, including all early failures and actual local ephemeral/KEM generation, is preserved by the static reference interpretation. -/
theorem collectVerified_realization (joint : Primitives) (domain : PublicDomain joint) (seed : IdentitySeed)
    {Reader E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (aux : QueryImpl (Spec Reader E Unit) m) (visit : Word32 → m Unit) (verified : Verified Reader) :
    simulateQ (nativeImpl joint seed aux visit) (collectVerified verified) =
      Option.map (concreteInputs joint seed) <$>
        simulateQ (prefixImpl domain aux visit) (collectVerified verified) := by
  simp only [collectVerified, OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query]
  simp only [nativeImpl, prefixImpl, map_bind]
  repeat' (
    try simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, OptionT.run_failure, Option.elimM, bind_map_left, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, map_bind, map_pure,
      nativeImpl, prefixImpl, ← selected_reply joint domain seed, selectedReply,
      Option.elim_none, Option.elim_some, Option.map_none, Option.map_some, bind_assoc, pure_bind]
    first | rfl | (congr 1 <;> first | rfl | (funext reply; cases reply)) | (split <;> try simp_all only [if_pos, if_neg]))
  all_goals first | rfl | simp [OptionT.run_failure, simulateQ_pure]

/-- Raw parsing and all three attached verification positions are identical in both interpretations; no selected-DH response is queried during verification. -/
theorem verifyInput_realization (joint : Primitives) (domain : PublicDomain joint) (seed : IdentitySeed)
    {Reader E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (aux : QueryImpl (Spec Reader E Unit) m) (visit : Word32 → m Unit) (raw : Pqxdh.Bytes) :
    simulateQ (nativeImpl joint seed aux visit) (verifyInput raw) =
      simulateQ (prefixImpl domain aux visit) (verifyInput raw) := by
  simp only [verifyInput, simulateQ_bind, simulateQ_spec_query, nativeImpl, prefixImpl]
  repeat' (
    try simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, nativeImpl, prefixImpl]
    first | rfl | (congr 1 <;> first | rfl | (funext reply; cases reply)) |
      (split <;> try simp_all only [if_pos, if_neg]))
  all_goals simp only [simulateQ_pure]

/-- The complete raw Server prefix keeps every failed callback's poststate and source generator order while withholding the selected static DH value from its executable client. -/
theorem collect_realization (joint : Primitives) (domain : PublicDomain joint) (seed : IdentitySeed)
    {Reader E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (aux : QueryImpl (Spec Reader E Unit) m) (visit : Word32 → m Unit) (raw : Pqxdh.Bytes) :
    simulateQ (nativeImpl joint seed aux visit) (collect raw) =
      Option.map (concreteInputs joint seed) <$>
        simulateQ (prefixImpl domain aux visit) (collect raw) := by
  simp only [collect, simulateQ_bind, verifyInput_realization joint domain seed aux visit, map_bind]
  congr 1
  funext result
  cases result with
  | none => simp only [simulateQ_pure, map_pure, Option.map_none]
  | some verified => exact collectVerified_realization joint domain seed aux visit verified

/-- Equality applies to the full remaining source continuation and the complete reached primitive state, rather than just a root-input marginal. -/
theorem collect_continuation (joint : Primitives) (domain : PublicDomain joint) (seed : IdentitySeed)
    {Reader E A Result : Type} (aux : QueryImpl (Spec Reader E Unit) (StateT A ProbComp))
    (visit : Word32 → StateT A ProbComp Unit) (raw : Pqxdh.Bytes) (initial : A)
    (next : Option (Inputs Reader E Word32) → A → ProbComp Result) :
    ((simulateQ (nativeImpl joint seed aux visit) (collect raw)).run initial >>= fun result => next result.1 result.2) =
      ((simulateQ (prefixImpl domain aux visit) (collect raw)).run initial >>=
        fun result => next (result.1.map (concreteInputs joint seed)) result.2) := by
  rw [collect_realization joint domain seed aux visit, StateT.run_map, bind_map_left]


def References {joint : Primitives} (domain : PublicDomain joint) {Reader E : Type}
    (input : Inputs Reader E PeerEncoding) : Prop :=
  input.first = peer (rootArray input.verified.keys.prekey) ∧ domain.accepts input.first = true

/-- Every supported post-verification success has the exact reached static-DH public input and its actual availability fact. No arbitrary reference is assumed. -/
theorem collectVerified_references {joint : Primitives} (domain : PublicDomain joint)
    {Reader E A : Type} (aux : QueryImpl (Spec Reader E Unit) (StateT A ProbComp))
    (visit : Word32 → StateT A ProbComp Unit) (verified : Verified Reader) (initial final : A)
    (input : Inputs Reader E PeerEncoding)
    (reached : (some input, final) ∈ support ((simulateQ (prefixImpl domain aux visit)
      (collectVerified verified)).run initial)) : References domain input := by
  simp only [collectVerified, OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
  repeat' first
    | (simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, OptionT.run_failure,
        Option.elimM, bind_map_left, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true,
        Option.elim_none, Option.elim_some, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, mem_support_bind_iff, prefixImpl, selectedReply,
        bind_assoc, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq,
        Option.some_ne_none, false_and] at reached)
    | (obtain ⟨⟨reply, state⟩, step, reached⟩ := reached; cases reply)
    | (split at reached)
  all_goals simp_all [References]

/-- Raw parsing does not weaken provenance: every reached complete-prefix result contains the same publicly admitted static-DH reference. -/
theorem collect_references {joint : Primitives} (domain : PublicDomain joint)
    {Reader E A : Type} (aux : QueryImpl (Spec Reader E Unit) (StateT A ProbComp))
    (visit : Word32 → StateT A ProbComp Unit) (raw : Pqxdh.Bytes) (initial final : A)
    (input : Inputs Reader E PeerEncoding)
    (reached : (some input, final) ∈ support ((simulateQ (prefixImpl domain aux visit)
      (collect raw)).run initial)) : References domain input := by
  simp only [collect, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨⟨result, state⟩, _, reached⟩ := reached
  cases result with
  | none => simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some_ne_none, false_and] at reached
  | some verified => exact collectVerified_references domain aux visit verified state final input reached


end BeaconcryptCore.Computational.PqxdhServerStaticDhSource

/-- info: 'BeaconcryptCore.Computational.PqxdhServerStaticDhSource.selected_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerStaticDhSource.selected_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhServerStaticDhSource.collectVerified_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerStaticDhSource.collectVerified_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhServerStaticDhSource.verifyInput_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerStaticDhSource.verifyInput_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhServerStaticDhSource.collect_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerStaticDhSource.collect_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhServerStaticDhSource.collect_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerStaticDhSource.collect_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhServerStaticDhSource.collectVerified_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerStaticDhSource.collectVerified_references

/-- info: 'BeaconcryptCore.Computational.PqxdhServerStaticDhSource.collect_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerStaticDhSource.collect_references
