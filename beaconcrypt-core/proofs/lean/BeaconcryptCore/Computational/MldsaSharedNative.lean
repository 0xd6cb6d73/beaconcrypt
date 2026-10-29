-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.MldsaSharedAuthentication
import BeaconcryptCore.Computational.RawCtxMixedShared

/-!
Authentication and record operations share one actual primitive state and one BLAKE2b cache. The typed authentication digest and optional native hash reply are two representations of the same reached query, including its poststate.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.MldsaSharedNative

open CtxRomAuth

abbrev Spec := CtxRO + RawCtxMixedOwner.NativeSpec

def authentication {Auxiliary : Type} :
    QueryImpl CtxRO (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  fun query state => (fun result => (result.1, (state.1, result.2))) <$>
    (ctxRandomOracle query).run state.2

noncomputable def primitives {Auxiliary : Type} (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl query => authentication query
  | .inr query => RawCtxMixedShared.sharedImpl crypto writer kdf query

def authLift : QueryImpl CtxRO (OracleComp Spec) :=
  fun query => Spec.query (.inl query)

def recordLift : QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp Spec) :=
  fun query => Spec.query (.inr query)

theorem same_hash {Auxiliary : Type} (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (bytes : Pqxdh.Bytes) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (fun result => (some result.1.toList, result.2)) <$>
        (primitives crypto writer kdf (.inl ((), bytes))).run state =
      (primitives crypto writer kdf (.inr (.inr (.inr (.inr (.inl bytes)))))).run state := by
  simpa only [primitives, authentication, StateT.run, Functor.map_map, bind_pure_comp] using
    (RawCtxMixedShared.shared_hash crypto writer kdf bytes state).symm

end BeaconcryptCore.Computational.MldsaSharedNative

/-- info: 'BeaconcryptCore.Computational.MldsaSharedNative.same_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedNative.same_hash
