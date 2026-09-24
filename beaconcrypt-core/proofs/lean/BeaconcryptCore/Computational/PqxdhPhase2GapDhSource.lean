import BeaconcryptCore.Computational.PqxdhJointGapDh
import BeaconcryptCore.Computational.PqxdhPhase2JointIdentity
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation
import BeaconcryptCore.Computational.PqxdhPhase2InputBytes

/-!
The selected Beacon prekey is represented by a private public-peer reference. The executable prefix has no selected scalar or pinned Server seed. Optional scalar-multiplication admission is supplied by an ordinary public native-input domain law, applied at the original call position. All other typed parsing, conversion, local DH and KEM operations retain their actual interfaces and effects.

The materializer belongs only to the mathematical native interpreter. A complete root-output simulation is not claimed here; the pending two-coordinate input is kept explicit for the subsequent Extract/output service.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Refinement.RepresentationBridge PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhPhase2GapDhSource
open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhBeaconPhase2Preparation (Bytes Word32 Ciphertext)

/-- Ordinary native DH input validation on correctly generated scalar inputs. Neither field asserts secrecy or pseudorandomness. -/
structure PublicDomain {joint : Primitives} (dh : DhInterface joint) where
  accepts : PeerEncoding → Bool
  available : ∀ scalar peer, (dh.dh scalar peer).isSome = accepts peer
  nonzero : ∀ scalar peer value, dh.dh scalar peer = some value → value ≠ zeroDh

def peer (value : Word32) : PeerEncoding := ⟨absBytes value, by simp⟩

def word (value : DhOutput) : Word32 := PqxdhRootTableInitialization.rootArray value

inductive Reference where
  | known (value : Word32)
  | selected (input : PeerEncoding)

def materialize {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes) : Reference → Word32
  | .known value => value
  | .selected input => word ((dh.dh scalar input).getD zeroDh)

def selectedReply {joint : Primitives} {dh : DhInterface joint} (domain : PublicDomain dh)
    (input : Word32) : Option Reference :=
  if domain.accepts (peer input) then some (.selected (peer input)) else none

/-- The public-domain test preserves exactly the native optional DH result; the raw value is used only in the private mathematical realization. -/
theorem selected_reply {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) (input : Word32) :
    Option.map (materialize dh scalar) (selectedReply domain input) =
      Option.map word (dh.dh scalar (peer input)) := by
  cases actual : dh.dh scalar (peer input) with
  | none =>
    simp [selectedReply, ← domain.available scalar (peer input), actual]
  | some value =>
    simp [selectedReply, ← domain.available scalar (peer input), materialize, actual]

inductive Query (I D K X Response : Type) where
  | decode : Bytes → Query I D K X Response
  | ciphertext : Response → Query I D K X Response
  | ephemeral : Response → Query I D K X Response
  | serverIdentity : Response → Query I D K X Response
  | publicConversion : Word32 → Query I D K X Response
  | privateConversion : I → Query I D K X Response
  | decapsulate : Ciphertext → K → Query I D K X Response
  | dhPair : D → Word32 → Query I D K X Response
  | dhIdentity : X → Word32 → Query I D K X Response
  | selected : Word32 → Query I D K X Response
  | assignedId : Response → Query I D K X Response
  | eraseShared : pqxdh.PqxdhSharedSecrets → Query I D K X Response

abbrev PrefixSpec (I D K X Response : Type) : OracleSpec (Query I D K X Response)
  | .decode _ => Option Response
  | .ciphertext _ => Option Ciphertext
  | .ephemeral _ | .serverIdentity _ | .publicConversion _ => Option Word32
  | .privateConversion _ => Option X
  | .decapsulate _ _ | .dhPair _ _ | .dhIdentity _ _ => Option Word32
  | .selected _ => Option Reference
  | .assignedId _ => Std.U64
  | .eraseShared _ => Unit

/-- Public typed fields and local DH/KEM outputs stay concrete; only the two selected-prekey results are references. -/
structure Inputs (Response : Type) where
  response : Response
  ciphertext : Ciphertext
  ephemeral : Word32
  server : Word32
  serverConverted : Word32
  assigned : Std.U64
  first : Reference
  second : Word32
  third : Reference
  fourth : Word32
  shared : Word32

def concreteInputs {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    {Response : Type} (input : Inputs Response) : PqxdhBeaconPhase2Preparation.Inputs Response :=
  ⟨input.response, input.ciphertext, input.ephemeral, ⟨input.server, input.assigned,
    ⟨materialize dh scalar input.first, input.second, materialize dh scalar input.third,
      input.fourth, input.shared⟩⟩⟩

/-- Exact original optional prefix: all twelve callbacks retain their original order and early exits. -/
def collect {I D K X Response : Type} (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    OracleComp (PrefixSpec I D K X Response) (Option (Inputs Response)) := OptionT.run do
  let response ← OptionT.mk ((PrefixSpec I D K X Response).query (.decode raw))
  let ciphertext ← OptionT.mk ((PrefixSpec I D K X Response).query (.ciphertext response))
  let ephemeral ← OptionT.mk ((PrefixSpec I D K X Response).query (.ephemeral response))
  let server ← OptionT.mk ((PrefixSpec I D K X Response).query (.serverIdentity response))
  let serverConverted ← OptionT.mk ((PrefixSpec I D K X Response).query (.publicConversion server))
  let identityConverted ← OptionT.mk ((PrefixSpec I D K X Response).query (.privateConversion identity))
  let shared ← OptionT.mk ((PrefixSpec I D K X Response).query (.decapsulate ciphertext kem))
  let first ← OptionT.mk ((PrefixSpec I D K X Response).query (.selected serverConverted))
  let second ← OptionT.mk ((PrefixSpec I D K X Response).query (.dhIdentity identityConverted ephemeral))
  let third ← OptionT.mk ((PrefixSpec I D K X Response).query (.selected ephemeral))
  let fourth ← OptionT.mk ((PrefixSpec I D K X Response).query (.dhPair oneTime ephemeral))
  let assigned ← liftM ((PrefixSpec I D K X Response).query (.assignedId response))
  pure ⟨response, ciphertext, ephemeral, server, serverConverted, assigned, first, second, third, fourth, shared⟩

/-- The reference interpreter uses only the public availability predicate. `visit` preserves the actual selected-call instrumentation and local work interface. -/
def prefixImpl {joint : Primitives} {dh : DhInterface joint} (domain : PublicDomain dh)
    {I D K X Response : Type} {m : Type → Type} [Monad m]
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (visit : Word32 → m Unit) : QueryImpl (PrefixSpec I D K X Response) m
  | .decode raw => aux (.decode raw)
  | .ciphertext response => aux (.ciphertext response)
  | .ephemeral response => aux (.ephemeral response)
  | .serverIdentity response => aux (.serverIdentity response)
  | .publicConversion server => aux (.publicConversion server)
  | .privateConversion identity => aux (.privateConversion identity)
  | .decapsulate ciphertext kem => aux (.decapsulate ciphertext kem)
  | .dhPair pair input => aux (.dhPair pair input)
  | .dhIdentity identity input => aux (.dhIdentity identity input)
  | .assignedId response => aux (.assignedId response)
  | .eraseShared secrets => aux (.eraseShared secrets)
  | .selected input => do
      let _ ← visit input
      pure (selectedReply domain input)

/-- Native selected DH retains the same call effects before returning its real optional value. The scalar is confined to this mathematical native interpreter. -/
def nativeImpl {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    {I D K X Response : Type} {m : Type → Type} [Monad m]
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (visit : Word32 → m Unit) :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec I (Unit ⊕ D) K X Response) m
  | .decode raw => aux (.decode raw)
  | .ciphertext response => aux (.ciphertext response)
  | .ephemeral response => aux (.ephemeral response)
  | .serverIdentity response => aux (.serverIdentity response)
  | .publicConversion server => aux (.publicConversion server)
  | .privateConversion identity => aux (.privateConversion identity)
  | .decapsulate ciphertext kem => aux (.decapsulate ciphertext kem)
  | .dhPair (.inl _) input => do
      let _ ← visit input
      pure (Option.map word (dh.dh scalar (peer input)))
  | .dhPair (.inr pair) input => aux (.dhPair pair input)
  | .dhIdentity identity input => aux (.dhIdentity identity input)
  | .assignedId response => aux (.assignedId response)
  | .eraseShared secrets => aux (.eraseShared secrets)

/-- Interpreting the unavailable prekey references reproduces the complete original optional collection, including every callback effect and early rejection. -/
theorem collect_realization {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) {I D K X Response : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (visit : Word32 → m Unit) (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    simulateQ (nativeImpl dh scalar aux visit)
      (PqxdhBeaconPhase2Preparation.collect identity (.inl ()) (.inr oneTime) kem raw) =
      Option.map (concreteInputs dh scalar) <$>
        simulateQ (prefixImpl domain aux visit) (collect identity oneTime kem raw) := by
  simp only [PqxdhBeaconPhase2Preparation.collect, collect, OptionT.run_bind, OptionT.run_mk,
    OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query]
  simp only [nativeImpl, prefixImpl, map_bind]
  congr 1
  funext response
  cases response <;> simp only [Option.elim_none, Option.elim_some, simulateQ_pure, map_pure, Option.map_none]
  repeat' (
    try simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, map_bind, map_pure,
      nativeImpl, prefixImpl, ← selected_reply dh domain scalar, selectedReply,
      Option.elim_none, Option.elim_some, Option.map_none, Option.map_some, bind_assoc, pure_bind]
    first | rfl | (congr 1 <;> first | rfl | (funext reply; cases reply)) | (split <;> try simp_all only [if_pos, if_neg]))
  all_goals simp only [Option.elim, simulateQ_pure, map_pure, Option.map]

/-- The equality is retained by the complete remaining computation, rather than only by a marginal root-input projection. -/
theorem collect_continuation {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) {I D K X Response Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (visit : Word32 → m Unit) (identity : I) (oneTime : D) (kem : K) (raw : Bytes)
    (next : Option (PqxdhBeaconPhase2Preparation.Inputs Response) → m Result) :
    (simulateQ (nativeImpl dh scalar aux visit)
      (PqxdhBeaconPhase2Preparation.collect identity (.inl ()) (.inr oneTime) kem raw) >>= next) =
    (simulateQ (prefixImpl domain aux visit) (collect identity oneTime kem raw) >>=
      fun input => next (Option.map (concreteInputs dh scalar) input)) := by
  rw [collect_realization dh domain scalar aux visit, bind_map_left]

/-- Original extracted preparation and erasure occur after the compiled prefix, including mismatched pinned identities. This mathematical continuation still materializes DH and is not an output simulator. -/
theorem prepare_continuation {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) {I D K X Response A Result : Type}
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (StateT A ProbComp))
    (visit : Word32 → StateT A ProbComp Unit) (identity : I) (oneTime : D) (kem : K) (raw : Bytes)
    (control : pqxdh.BeaconInitSent) (initial : A)
    (next : Option (PqxdhBeaconPhase2Preparation.Prepared Response) × A → ProbComp Result) :
    ((simulateQ (nativeImpl dh scalar aux visit)
      (PqxdhBeaconPhase2Preparation.prepare control identity (.inl ()) (.inr oneTime) kem raw)).run initial >>= next) =
    ((simulateQ (prefixImpl domain aux visit) (collect identity oneTime kem raw)).run initial >>=
      fun input => match input.1 with
        | none => next (none, input.2)
        | some value =>
          (simulateQ (nativeImpl dh scalar aux visit)
            (PqxdhBeaconPhase2Preparation.afterInputs control (concreteInputs dh scalar value))).run input.2 >>= next) := by
  simp only [PqxdhBeaconPhase2Preparation.prepare, simulateQ_bind,
    collect_realization dh domain scalar aux visit, bind_map_left, StateT.run_bind, bind_assoc]
  congr 1
  funext input
  cases input.1 <;> simp only [Option.map_none, Option.map_some, simulateQ_pure, StateT.run_pure, pure_bind]

/-- At most twelve typed callbacks occur, including both selected-prekey call positions. -/
theorem collect_bound {I D K X Response : Type} (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    (collect (X := X) (Response := Response) identity oneTime kem raw).IsTotalQueryBound 12 := by
  unfold collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | rw [isTotalQueryBound_query_bind_iff]
    | constructor
    | intro reply; cases reply

def selectedQuery {I D K X Response : Type} : Query I D K X Response → Bool
  | .selected _ => true
  | _ => false

/-- Rejections never cause extra selected-prekey work: at most two native call effects must be simulated. -/
theorem selected_bound {I D K X Response : Type} (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    (collect (X := X) (Response := Response) identity oneTime kem raw).IsQueryBoundP
      (fun query => selectedQuery query = true) 2 := by
  unfold collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; simp [selectedQuery])
    | rw [isQueryBoundP_map_iff]
    | intro reply; cases reply <;> simp only [Option.elim]

  all_goals exact (isQueryBoundP_query_iff (spec := PrefixSpec I D K X Response)
    (p := fun query => selectedQuery query = true) _ 0).mpr (by simp [selectedQuery])

/-- The remaining ten callbacks are billed separately, including decapsulation before selected DH. -/
theorem auxiliary_bound {I D K X Response : Type} (identity : I) (oneTime : D) (kem : K) (raw : Bytes) :
    (collect (X := X) (Response := Response) identity oneTime kem raw).IsQueryBoundP
      (fun query => selectedQuery query = false) 10 := by
  unfold collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; simp [selectedQuery])
    | rw [isQueryBoundP_map_iff]
    | intro reply; cases reply <;> simp only [Option.elim]

  all_goals exact (isQueryBoundP_query_iff (spec := PrefixSpec I D K X Response)
    (p := fun query => selectedQuery query = false) _ 1).mpr (by simp [selectedQuery])

/-- Reached selected references retain their actual callback arguments and public admission results. -/
def References {joint : Primitives} {dh : DhInterface joint} (domain : PublicDomain dh)
    {Response : Type} (input : Inputs Response) : Prop :=
  input.first = .selected (peer input.serverConverted) ∧
  input.third = .selected (peer input.ephemeral) ∧
  domain.accepts (peer input.serverConverted) = true ∧ domain.accepts (peer input.ephemeral) = true

/-- Every supported compiled success has the two actual selected-prekey coordinates; arbitrary callback replies cannot manufacture other references. -/
theorem collect_references {joint : Primitives} {dh : DhInterface joint} (domain : PublicDomain dh)
    {I D K X Response A : Type}
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (StateT A ProbComp))
    (visit : Word32 → StateT A ProbComp Unit) (identity : I) (oneTime : D) (kem : K) (raw : Bytes)
    (initial final : A) (input : Inputs Response)
    (reached : (some input, final) ∈ support
      ((simulateQ (prefixImpl domain aux visit) (collect identity oneTime kem raw)).run initial)) :
    References domain input := by
  simp only [collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
    Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at reached
  repeat' first
    | (simp only [Option.elim_none, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        prefixImpl, selectedReply, bind_assoc, pure_bind, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq, Option.some_ne_none, false_and] at reached)
    | (obtain ⟨⟨reply, state⟩, step, reached⟩ := reached; cases reply)
    | (split at reached)
  all_goals simp_all [References]

/-- A reached public conversion remains the actual native conversion, with no early pinned-identity check inserted into the source order. -/
theorem collect_conversion {joint : Primitives} {dh : DhInterface joint} (domain : PublicDomain dh)
    {I D K X Response A : Type} (c : Pqxdh.Crypto)
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (StateT A ProbComp))
    (conversion : ∀ value initial converted final,
      (some converted, final) ∈ support ((aux (.publicConversion value)).run initial) →
        c.xpkConv (absBytes value) = some (absBytes converted))
    (visit : Word32 → StateT A ProbComp Unit) (identity : I) (oneTime : D) (kem : K) (raw : Bytes)
    (initial final : A) (input : Inputs Response)
    (reached : (some input, final) ∈ support
      ((simulateQ (prefixImpl domain aux visit) (collect identity oneTime kem raw)).run initial)) :
    c.xpkConv (absBytes input.server) = some (absBytes input.serverConverted) := by
  simp only [collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
    Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at reached
  repeat' first
    | (simp only [Option.elim_none, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        prefixImpl, selectedReply, bind_assoc, pure_bind, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq, Option.some_ne_none, false_and] at reached)
    | (obtain ⟨⟨reply, state⟩, step, reached⟩ := reached; cases reply)
    | (split at reached)
  all_goals simp_all
  all_goals solve_by_elim [conversion]

/-- Every auxiliary callback and selected-call effect is charged under the complete adaptive interpreter state; none is declared free. -/
theorem interpreted_bound {joint : Primitives} {dh : DhInterface joint} (domain : PublicDomain dh)
    {I D K X Response A ι : Type} {target : OracleSpec ι}
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (StateT A (OracleComp target)))
    (visit : Word32 → StateT A (OracleComp target) Unit)
    (predicate : target.Domain → Prop) [DecidablePred predicate] (qAux qVisit : Nat)
    (auxBound : ∀ query state, ((aux query).run state).IsQueryBoundP predicate qAux)
    (visitBound : ∀ input state, ((visit input).run state).IsQueryBoundP predicate qVisit)
    (identity : I) (oneTime : D) (kem : K) (raw : Bytes) (initial : A) :
    ((simulateQ (prefixImpl domain aux visit) (collect identity oneTime kem raw)).run initial).IsQueryBoundP
      predicate (10 * qAux + 2 * qVisit) := by
  have structural := FinitePartitionQueryBounds.weighted_bound selectedQuery
    (fun selected => if selected then qVisit else qAux)
    (fun selected => if selected then 2 else 10)
    (prefixImpl domain aux visit) predicate (collect identity oneTime kem raw)
    (by intro selected; cases selected
        · exact auxiliary_bound identity oneTime kem raw
        · exact selected_bound identity oneTime kem raw)
  have step : ∀ query state, ((prefixImpl domain aux visit query).run state).IsQueryBoundP predicate
      ((fun selected => if selected then qVisit else qAux) (selectedQuery query)) := by
    intro query state
    cases query with
    | selected input =>
      simp only [prefixImpl, StateT.run_bind, StateT.run_pure, selectedQuery, if_true]
      simpa only [Nat.add_zero] using isQueryBoundP_bind (visitBound input state)
        (fun _ _ => isQueryBoundP_pure predicate _ 0)
    | _ => exact auxBound _ state
  simpa [Nat.mul_comm, Nat.add_comm] using structural step initial

end BeaconcryptCore.Computational.PqxdhPhase2GapDhSource

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.selected_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.selected_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.collect_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.collect_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.collect_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.collect_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.prepare_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.prepare_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.collect_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.selected_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.selected_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.auxiliary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.auxiliary_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.collect_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.collect_references

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.collect_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.collect_conversion

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.interpreted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhSource.interpreted_bound
