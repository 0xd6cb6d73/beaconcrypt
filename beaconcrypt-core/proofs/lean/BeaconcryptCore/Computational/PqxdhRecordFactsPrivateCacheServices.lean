-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFamily

/-! The coordinate-family discard law with arbitrary interleaved base-only operations. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices
open CtxRomAuth AdaptiveCtxReceive
open LazyOracleDiscard PqxdhRecordFactsPrivateCacheFamily
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode KeyedSpec onBase)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι}

/-- Any base-only service, including a public hash or table update, frames all private suffix caches. -/
theorem onBase_commutes {Result : Type} (work : StateT (PqxdhRecordLiftProtocol.Private n) ProbComp Result) :
    Commutes familyLens (onBase work) := by
  apply commutes_frame
  intro state cache
  simp only [onBase, StateT.run, familyLens, Functor.map_map]

/-- Internal plumbing can interleave a keyed request with any base-only service. -/
abbrev MixedSpec (n : Nat) (baseSpec : OracleSpec ι) := KeyedSpec n + baseSpec

/-- The actual uncounted key endpoint alongside an arbitrary supplied base-only interpreter. -/
noncomputable def mixed (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (baseImpl : QueryImpl baseSpec (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp)) :
    QueryImpl (MixedSpec n baseSpec) (StateT (CtxPrivate n) ProbComp)
  | .inl q => uncountedKeyed modes decode crypto q
  | .inr q => onBase (baseImpl q)

/-- Only key-local parsed raw receives report a discarded suffix completion. -/
noncomputable def pointed (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (baseImpl : QueryImpl baseSpec (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp)) :
    (q : (MixedSpec n baseSpec).Domain) → StateT (CtxPrivate n) ProbComp
      ((MixedSpec n baseSpec).Range q × Option (FamilyRO n).Domain)
  | .inl q => keyedPointed modes decode crypto q
  | .inr q => (fun answer => (answer, none)) <$> onBase (baseImpl q)

/-- The complete mixed step, including every base effect, equals its pointed factor. -/
theorem mixed_factor (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (baseImpl : QueryImpl baseSpec (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp))
    (supported : ∀ label, modes label ≠ .real) (q : (MixedSpec n baseSpec).Domain) (state : CtxPrivate n) :
    LawEq ((mixed modes decode crypto baseImpl q).run state)
      ((pointed modes decode crypto baseImpl q).run state >>= fun r =>
        (r.1.1, ·) <$> familyLens.completeOpt r.1.2 r.2) := by
  cases q with
  | inl q => exact keyed_factor modes decode crypto supported q state
  | inr q =>
      apply LawEq.of_eq
      simp only [mixed, pointed, StateT.run_map, bind_map_left, StateLens.completeOpt, map_pure]
      change ((onBase (baseImpl q)).run state) =
        ((onBase (baseImpl q)).run state >>= fun r => pure (r.1, r.2))
      simp only [Prod.eta, bind_pure]

/-- Both internal query classes commute with completion at any hidden coordinate. -/
theorem pointed_commutes (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (baseImpl : QueryImpl baseSpec (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp))
    (supported : ∀ label, modes label ≠ .real) (q : (MixedSpec n baseSpec).Domain) :
    Commutes familyLens (pointed modes decode crypto baseImpl q) := by
  cases q with
  | inl q => exact keyedPointed_commutes modes decode crypto supported q
  | inr q => exact commutes_map familyLens (fun answer => (answer, none)) (onBase_commutes (baseImpl q))

/-- Erased mixed handler; all base-only work remains literal. -/
noncomputable def erased (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (baseImpl : QueryImpl baseSpec (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp)) :
    QueryImpl (MixedSpec n baseSpec) (StateT (CtxPrivate n) ProbComp) :=
  fun q => Prod.fst <$> pointed modes decode crypto baseImpl q

/-- Full adaptive family discard with arbitrary interleaved base effects. No property of the supplied base interpreter is assumed beyond its explicit state interface. -/
theorem mixed_observation (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (baseImpl : QueryImpl baseSpec (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp))
    (supported : ∀ label, modes label ≠ .real) {Result : Type}
    (client : OracleComp (MixedSpec n baseSpec) Result) (state : CtxPrivate n) :
    LawEq (Prod.map id observeFamily <$> (simulateQ (mixed modes decode crypto baseImpl) client).run state)
      (Prod.map id observeFamily <$> (simulateQ (erased modes decode crypto baseImpl) client).run state) := by
  exact discard_erase_proj familyLens (mixed modes decode crypto baseImpl)
    (pointed modes decode crypto baseImpl) (mixed_factor modes decode crypto baseImpl supported)
    (fun q => commutes_map familyLens Prod.fst (pointed_commutes modes decode crypto baseImpl supported q))
    observeFamily observeFamily_set client state

end BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices.onBase_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices.onBase_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices.mixed_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices.mixed_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices.pointed_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices.pointed_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices.mixed_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices.mixed_observation
