-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationNativeKeyPreparation
import BeaconcryptCore.Computational.RegistrationNativeKeyBounds

/-! The concrete paired root/material phase starts before the prepare callback, executes the dependent protected root Expand there, and exposes only its message reference. A proved private-cache deferral and the concrete PRK-free compiler reduce the entire adaptive phase schedule to the indexed five-hop primitive experiment. The uniform108 endpoint is bounded by actual material-demand commands; known/off-protected inputs retain the real source function throughout. Native slot/role alias exclusion and the earlier selected KEM/related-Extract hops are separate boundaries. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKeyServiceBound
open RegistrationNativeKeyPhases (Spec State Meta Value erased eager initial emptyMeta)
open RegistrationNativeKeyCompiler (client)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (HmacSha512)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)

/-- The private native prepare root is executed before erasing just its root bytes from the public reference reply. -/
noncomputable def native (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl Spec (StateT State ProbComp)
  | .inr (.prepare message) => Option.map Prod.fst <$>
      RegistrationNativeKeyPreparation.prepare source hmac input inside message
  | query => erased source hmac input inside query

theorem native_eager (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    native source hmac input inside = eager source hmac input inside := by
  funext query before
  cases query with
  | inl coin =>
    simp only [native, eager, RegistrationNativeKeyPhases.pendingPoint,
      LazyOracleDiscard.StateLens.completeOpt, StateT.run, map_pure,
      bind_pure_comp, Prod.mk.eta, bind_pure]
  | inr request => cases request with
    | prepare message =>
      change ((Option.map Prod.fst <$> RegistrationNativeKeyPreparation.prepare source hmac input inside message).run before) = _
      rw [StateT.run_map]
      exact RegistrationNativeKeyPreparation.prepare_public source hmac input inside message before
    | demand message =>
      simp only [native, eager, RegistrationNativeKeyPhases.pendingPoint,
        LazyOracleDiscard.StateLens.completeOpt, StateT.run, map_pure,
        bind_pure_comp, Prod.mk.eta, bind_pure]

/-- The G1 private protected PRKs are first queried during actual preparation, before any material request or its gates. -/
noncomputable def g1 (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Bool) : ProbComp Bool :=
  (simulateQ (native source hmac input inside) work).run' initial

/-- Every protected complete108 entry is uniform and persistent; the public source phase client and all side computations are unchanged. -/
noncomputable def g2 (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Bool) : ProbComp Bool :=
  RegistrationNativeKeyHybrid.uniform (client source input inside work emptyMeta)

theorem g1_hybrid (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Bool) :
    𝒟[g1 source hmac input inside work] =
      𝒟[RegistrationNativeKeyHybrid.hybrid source hmac (client source input inside work emptyMeta) 0] := by
  have postponed := RegistrationNativeKeyPhases.defer_preparation source hmac input inside work initial
  have onlyBit := (postponed.map Prod.fst).evalDist_eq
  have first : 𝒟[g1 source hmac input inside work] =
      𝒟[(simulateQ (erased source hmac input inside) work).run' initial] := by
    simpa only [g1, native_eager, StateT.run'_eq, Functor.map_map, Prod.map, id_eq] using onlyBit
  rw [first]
  have sourceClient := RegistrationNativeKeyBounds.client_source source hmac input inside work initial
  have sourceTable := RegistrationNativeKeyRelabel.source_hybrid source hmac (client source input inside work emptyMeta)
  change 𝒟[(simulateQ (erased source hmac input inside) work).run' initial] = _
  rw [← sourceClient]
  exact congrArg evalDist sourceTable

/-- Actual admitted-demand bounds give a computational uniform108 law for the whole phase schedule. The five standard primitive losses include root Expand and the complete later native experiment. No desired simulation or conditional PRK-independence premise occurs. -/
theorem bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect source hmac)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Bool) (count : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativeKeyBounds.IsDemand count) :
    (g1 source hmac input inside work).boolDistance (g2 source input inside work) ≤
      ∑ index ∈ Finset.range count, RegistrationBoundKeySchedule.keyLoss source hmac
        (RegistrationNativeKeyHybrid.reduction source hmac (client source input inside work emptyMeta) index) := by
  have changeGame : (g1 source hmac input inside work).boolDistance (g2 source input inside work) =
      (RegistrationNativeKeyHybrid.hybrid source hmac (client source input inside work emptyMeta) 0).boolDistance
        (RegistrationNativeKeyHybrid.uniform (client source input inside work emptyMeta)) := by
    unfold ProbComp.boolDistance g2
    rw [g1_hybrid]
  rw [changeGame]
  exact RegistrationNativeKeyHybrid.bound source hmac correct _ count
    (RegistrationNativeKeyBounds.client_bound source input inside work count bounded emptyMeta)

end BeaconcryptCore.Computational.RegistrationNativeKeyServiceBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyServiceBound.native_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyServiceBound.native_eager
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyServiceBound.g1_hybrid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyServiceBound.g1_hybrid
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyServiceBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyServiceBound.bound
