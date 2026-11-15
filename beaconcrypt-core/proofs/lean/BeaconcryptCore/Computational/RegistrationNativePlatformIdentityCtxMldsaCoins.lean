-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingMetadata
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMldsaCoins
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Auxiliary Platform A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def Coin : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain → Prop
  | .inl (.inl (.inl _)) => True
  | _ => False
private def NativeCoin : (RegistrationNativeIdentityFrontend.Trusted n KemSK).Domain → Prop
  | .inl (.inl (.inl _)) => True
  | _ => False
private def PlatformCoin : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain → Prop
  | .inl _ => True
  | .inr query => NativeCoin (n := n) (KemSK := KemSK) query
private def NativeWork (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source A) : Prop :=
  ∀ owners env, ((work.run owners).run env).AllQueriesSatisfy (NativeCoin (n := n) (KemSK := KemSK))

private theorem mapped {J X Y : Type} {queries : OracleSpec J}
    (work : OracleComp queries X) (change : X → Y) (predicate : J → Prop)
    (allowed : work.AllQueriesSatisfy predicate) : (change <$> work).AllQueriesSatisfy predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)
private theorem compiled {J K X : Type} {left : OracleSpec J} {right : OracleSpec K}
    (handler : QueryImpl left (OracleComp right)) (input : J → Prop) (output : K → Prop)
    (step : ∀ query, input query → (handler query).AllQueriesSatisfy output)
    (work : OracleComp left X) (allowed : work.AllQueriesSatisfy input) :
    (simulateQ handler work).AllQueriesSatisfy output := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact allQueriesSatisfy_bind (step query allowed.1) (fun reply => ih reply (allowed.2 reply))
private theorem native_pure (value : A) : NativeWork (pure value : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source A) := by
  intro owners env
  simp only [StateT.run_pure]
  trivial
private theorem native_bind (work : RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source A)
    (next : A → RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source B)
    (first : NativeWork work) (later : ∀ value, NativeWork (next value)) : NativeWork (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun result => later result.1.1 result.1.2 result.2)
private theorem native_coin (coin : unifSpec.Domain) :
    NativeWork (RegistrationNativeIdentityFrontend.effect (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (.inl coin)) := by
  intro owners env
  simp only [RegistrationNativeIdentityFrontend.effect, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  exact mapped _ _ _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)
private theorem native_sample (work : ProbComp A) :
    NativeWork (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [RegistrationNativeIdentityFrontend.sample, simulateQ_pure] using native_pure value
  | query_bind query next ih =>
    simp only [RegistrationNativeIdentityFrontend.sample, simulateQ_bind, simulateQ_spec_query]
    exact native_bind _ _ (native_coin query) ih
private theorem native_update (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    NativeWork (RegistrationNativeIdentityFrontend.updateEnv (n := n) (KemSK := KemSK) (source := source) change) := by
  intro owners env
  simp only [RegistrationNativeIdentityFrontend.updateEnv, StateT.run_lift]
  trivial
private theorem native_outgoing (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (request : registration.MldsaSigningRequest) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) :
    NativeWork (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner (.inl (.sign request payload digest))) :=
  native_pure (core.option.Option.None : RegistrationSigningShared.SignReply)

private theorem native_lifted (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (request : registration.MldsaSigningRequest) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (owners : RegistrationNativeIdentityFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (previous : Platform) :
    ((((RegistrationNativePlatformIdentityProgram.native (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary)
      setup source index owner (.inl (.sign request payload digest)))).run owners).run env).run previous).AllQueriesSatisfy
      (PlatformCoin (n := n) (KemSK := KemSK)) := by
  simp only [RegistrationNativePlatformIdentityProgram.native, StateT.run]
  apply mapped
  apply compiled RegistrationNativePlatformIdentityProgram.nativeLift (NativeCoin (n := n) (KemSK := KemSK)) (PlatformCoin (n := n) (KemSK := KemSK))
    _ _ (native_outgoing setup index owner request payload digest owners env)
  intro query permitted
  exact (allQueriesSatisfy_query_iff _ _).mpr permitted

private theorem backend_coins (work : ProbComp A) :
    (simulateQ RegistrationNativePlatformIdentityCtxCompiler.backend (simulateQ RegistrationNativePlatformCtxBackend.coin work)).AllQueriesSatisfy Coin := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformCtxBackend.coin,
      RegistrationNativePlatformIdentityCtxCompiler.backend]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem compiler_coin (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain)
    (permitted : PlatformCoin (n := n) (KemSK := KemSK) query) (before : RegistrationNativeIdentityWorld.Context n KemSK) :
    ((RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created) query).run before).AllQueriesSatisfy Coin := by
  rcases query with coin | query
  · simp only [RegistrationNativePlatformIdentityCtxCompiler.free,
      RegistrationNativePlatformIdentityCtxCompiler.implementation, StateT.run,
      RegistrationNativePlatformIdentityCtxCompiler.coins]
    exact mapped _ _ _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)
  · rcases query with ((coin | action) | kem) | identity
    · simp only [RegistrationNativePlatformIdentityCtxCompiler.free,
        RegistrationNativePlatformIdentityCtxCompiler.implementation,
        RegistrationNativePlatformIdentityCtxAmbient.program, RegistrationNativePlatformIdentityCtxAmbient.world,
        StateT.run, RegistrationNativePlatformCtxEffects.program, simulateQ_map]
      exact mapped _ _ _ (backend_coins _)
    · exact False.elim permitted
    · exact False.elim permitted
    · cases identity with
      | create | reveal handle => exact False.elim permitted
      | service handle request => exact False.elim permitted

private theorem compiled_state {J K S X : Type} {left : OracleSpec J} {right : OracleSpec K}
    (handler : QueryImpl left (StateT S (OracleComp right))) (input : J → Prop) (output : K → Prop)
    (step : ∀ query before, input query → ((handler query).run before).AllQueriesSatisfy output)
    (work : OracleComp left X) (allowed : work.AllQueriesSatisfy input) (before : S) :
    ((simulateQ handler work).run before).AllQueriesSatisfy output := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (step query before allowed.1) (fun result => ih result.1 (allowed.2 result.1) result.2)

/-- The literal actual current ML outgoing callback can query only ordinary uniform coins. All physical/native/P effects remain in the tree. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (request : registration.MldsaSigningRequest) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.native
        (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
          setup source index owner (.inl (.sign request payload digest))))).run before).AllQueriesSatisfy Coin := by
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.run]
  apply mapped
  apply compiled_state _ (PlatformCoin (n := n) (KemSK := KemSK)) Coin
    (fun query current allowed => compiler_coin setup checks representation created query allowed current)
    _ (native_lifted setup index owner request payload digest _ _ _) _
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMldsaCoins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing
