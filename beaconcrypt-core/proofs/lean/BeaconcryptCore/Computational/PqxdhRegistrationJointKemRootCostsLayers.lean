import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCostsTools
import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOncePost
import BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts
import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceServices
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform

/-!
# The random draws of the layers below the skeleton (item 2, stage S8, layers)

The item 2 root client runs the skeleton's post-challenge phase through the actual encapsulator, the post-challenge KEM router and the CCA evaluation, and answers its direct table reads from a public table that it holds itself. This module gives each of these interpreters a weight on its requests that covers the random draws of its step, and carries the weights down to the root client's coins:

- `wRoot` (the root client: one per coin), `wSkel` (the skeleton's interface: one per coin, 64 per direct table read, none for a hidden read), `wCca` (the CCA interface with the table oracles: one per coin, `baseUniform` per base query, `decapsCost` per decapsulation), `wPoolT` (the private pool with the table oracles: 32 per identity creation, one per identity or explicit coin, `decapsCost` per KEM decapsulation) and `wEnc` (the exposed encapsulation interface: `encapsCost` per encapsulation);
- `publicLocal_cost`, `evalLayer_cost`, `router_cost` and `actual_cost`: every step of each layer costs at most the weight of its request in the weights of the layer below (`KemBound setup caps` supplies the primitive costs);
- `lower_cost`: a program of the exposed encapsulation interface run through the three lower layers costs, in the skeleton's weight, at most its own weight; `liftT_cost` lifts a bound of a native-layer program of the skeleton.

These are resource bounds; they make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhRegistrationJointKemPostSkeleton
open PqxdhRegistrationJointBeaconFinishOnce (liftComp_inl)

/-! ### Weights -/

section Weights

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK V : Type}

/-- The root client's coins. -/
def wRoot : PqxdhCorrelatedExpand.RootSpec.Domain → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- The table oracles: a hidden read draws nothing, a direct read at most one 64-byte block. -/
def wTable : (TSpec V).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 64

/-- The skeleton's interface: coins and table oracles. -/
def wSkel : (SkelSpec V).Domain → ℕ
  | .inl _ => 1
  | .inr query => wTable (V := V) query

/-- The CCA interface: coins, base queries and decapsulations, with the table oracles. -/
def wCca (caps : KemCaps) : (MlKemCCAOracleSpec baseSpec + TSpec V).Domain → ℕ
  | .inl (.inl (.inl _)) => 1
  | .inl (.inl (.inr _)) => caps.baseUniform
  | .inl (.inr _) => caps.decapsCost
  | .inr query => wTable (V := V) query

/-- The private pool: identity creations, identity and explicit coins, and KEM decapsulations. -/
def wPool (caps : KemCaps) : (PqxdhLiveKemBirth.Spec KemSK).Domain → ℕ
  | .inl query => (if PqxdhDynamicIdentityPool.IsCreate query then 32 else 0) +
      (if PqxdhDynamicIdentityPool.IsUniform query then 1 else 0)
  | .inr (.inl _) => 1
  | .inr (.inr query) => if PqxdhDynamicKemBounds.IsDecapsulation query then caps.decapsCost else 0

/-- The private pool with the table oracles. -/
def wPoolT (caps : KemCaps) : (PqxdhLiveKemBirth.Spec KemSK + TSpec V).Domain → ℕ
  | .inl query => wPool (KemSK := KemSK) caps query
  | .inr query => wTable (V := V) query

/-- The exposed encapsulation interface with the table oracles. -/
def wEnc (caps : KemCaps) : (Enc KemSK + TSpec V).Domain → ℕ
  | .inl (.inl query) => wPool (KemSK := KemSK) caps query
  | .inl (.inr _) => caps.encapsCost
  | .inr query => wTable (V := V) query

end Weights

/-! ### Generic lifts -/

section Lifts

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'} {α : Type}

/-- A total query bound is a weighted bound with weight one. -/
theorem wBound_of_total {work : OracleComp spec α} {n : ℕ} (bounded : work.IsTotalQueryBound n) :
    WBound work (fun _ => 1) n := by
  have := wBound_of_isQueryBoundP (fun _ => True) 1 ((isQueryBoundP_true_iff work n).mpr bounded)
  simpa using this

/-- Lifting into the left summand keeps the weights of the left requests. -/
theorem wBound_liftComp_inl {ιT : Type} {T : OracleSpec.{0, 0} ιT} (w : spec.Domain → ℕ)
    (w' : (spec + T).Domain → ℕ) (same : ∀ query, w' (.inl query) = w query) {work : OracleComp spec α} {n : ℕ}
    (bounded : WBound work w n) : WBound (work.liftComp (spec + T)) w' n := by
  induction work using OracleComp.inductionOn generalizing n with
  | pure value => simp only [liftComp_pure]; trivial
  | query_bind query next ih =>
      rw [wBound_query_bind] at bounded
      rw [liftComp_bind, liftComp_inl, wBound_query_bind, same]
      exact ⟨bounded.1, fun reply => ih reply (bounded.2 reply)⟩

end Lifts

/-! ### The lower layers -/

section Lower

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- The root client's public table: a coin is one coin, a hidden read becomes a root request, a direct read draws at most 64 coins. -/
theorem publicLocal_cost (query : (SkelSpec PqxdhSecretInputKdf.RootOutput).Domain) (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache) :
    WBound ((PqxdhRegistrationJointKemRootExpand.publicLocal query).run cache) wRoot (wSkel query) := by
  rcases query with coin | (message | point)
  · change WBound ((fun reply => (reply, cache)) <$>
      (liftM (PqxdhCorrelatedExpand.RootSpec.query (.inl coin)) : OracleComp PqxdhCorrelatedExpand.RootSpec _)) _ _
    exact wBound_map _ ((wBound_query _ _ _).mpr le_rfl)
  · change WBound ((fun reply => (reply, cache)) <$>
      (liftM (PqxdhCorrelatedExpand.RootSpec.query (.inr message)) : OracleComp PqxdhCorrelatedExpand.RootSpec _)) _ _
    exact wBound_map _ ((wBound_query _ _ _).mpr le_rfl)
  · change WBound (PqxdhCorrelatedExpand.rootCoins ((PqxdhSecretInputKdf.HmacOracle.randomOracle point).run cache)) _ _
    have coins := PqxdhCorrelatedExpandQueryBounds.rootCoins_uniform _ 64
      (PqxdhServerAuthNativeUniformCosts.extract_table_uniform point cache)
    refine wBound_weight_mono (fun query => ?_) (wBound_of_isQueryBoundP _ 1 coins)
    rcases query with _ | _ <;> simp [wRoot, PqxdhCorrelatedExpandQueryBounds.IsCoin]

/-- The CCA interface without the table oracles. -/
def wCcaBase (caps : KemCaps) : (MlKemCCAOracleSpec baseSpec).Domain → ℕ
  | .inl (.inl _) => 1
  | .inl (.inr _) => caps.baseUniform
  | .inr _ => caps.decapsCost

theorem evalLayer_inl (setup : Setup baseSpec KemSK) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (unifSpec + baseSpec).Domain) :
    evalLayer setup secret challenge (.inl query) = kemAmbientImpl setup.baseImpl query := by
  change simulateQ (kemAmbientImpl setup.baseImpl) (liftM ((unifSpec + baseSpec).query query)) = _
  rw [simulateQ_spec_query]

theorem evalLayer_inr (setup : Setup baseSpec KemSK) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (ciphertext : MlKem768Ciphertext) :
    evalLayer setup secret challenge (.inr ciphertext) = simulateQ (kemAmbientImpl setup.baseImpl)
      (if ciphertext = challenge then pure none else setup.kem.decaps secret ciphertext) := rfl

/-- Each CCA request of the challenger's evaluation draws at most its weight. -/
theorem evalLayer_total (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (secret : KemSK) (challenge : MlKem768Ciphertext) (query : (MlKemCCAOracleSpec baseSpec).Domain) :
    (evalLayer setup secret challenge query).IsTotalQueryBound (wCcaBase caps query) := by
  rcases query with (coin | base) | ciphertext
  · rw [evalLayer_inl]
    exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  · rw [evalLayer_inl]
    exact bounded.base base
  · rw [evalLayer_inr]
    split
    · simp only [simulateQ_pure]
      trivial
    · exact PqxdhServerAuthSourceCosts.ambient_uniform setup.baseImpl caps.baseUniform bounded.base _ _ _
        (bounded.decapsUniform secret ciphertext) (bounded.decapsBase secret ciphertext)

/-- The challenger's CCA evaluation, forwarding the table oracles: each step costs at most its CCA weight. -/
theorem evalLayer_cost (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (secret : KemSK) (challenge : MlKem768Ciphertext) (query : (MlKemCCAOracleSpec baseSpec + TSpec V).Domain) :
    WBound (fwd (T := TSpec V) (evalLayer setup secret challenge) query) (wSkel (V := V)) (wCca caps query) := by
  rcases query with cca | table
  · rw [fwd_inl]
    have weight : wCca (baseSpec := baseSpec) (V := V) caps (.inl cca) = wCcaBase (baseSpec := baseSpec) caps cca := by
      rcases cca with (_ | _) | _ <;> rfl
    rw [weight]
    exact wBound_liftComp_inl (fun _ => 1) _ (fun _ => rfl)
      (wBound_of_total (evalLayer_total setup caps bounded secret challenge cca))
  · rw [fwd_inr]
    exact (wBound_query _ _ _).mpr (by rcases table with _ | _ <;> exact le_rfl)

/-- The challenger's coins inside the CCA interface keep their count. -/
theorem ccaCoins_cost {α : Type} (caps : KemCaps) (work : ProbComp α) {n : ℕ} (bounded : work.IsTotalQueryBound n) :
    WBound (PqxdhPrivateKemSource.ccaCoins (baseSpec := baseSpec) work) (wCcaBase caps) n := by
  unfold PqxdhPrivateKemSource.ccaCoins
  refine wBound_simulate _ (fun _ => 1) (wCcaBase caps) (fun query => ?_) (wBound_of_total bounded)
  exact (wBound_query _ _ _).mpr le_rfl

/-- A local KEM operation inside the CCA interface costs its uniform and base queries. -/
theorem ccaAmbient_cost {α : Type} (caps : KemCaps) (work : OracleComp (unifSpec + baseSpec) α) (u b : ℕ)
    (uniform : work.IsQueryBoundP (PqxdhServerAuthSourceCosts.IsAmbientUniform (baseSpec := baseSpec)) u)
    (base : work.IsQueryBoundP (PqxdhServerAuthSourceCosts.IsAmbientBase (baseSpec := baseSpec)) b) :
    WBound (PqxdhPrivateKemSource.ccaAmbient work) (wCcaBase caps) (u + caps.baseUniform * b) := by
  have both := wBound_add (wBound_of_isQueryBoundP _ 1 uniform) (wBound_of_isQueryBoundP _ caps.baseUniform base)
  rw [Nat.one_mul] at both
  unfold PqxdhPrivateKemSource.ccaAmbient
  refine wBound_simulate _ _ (wCcaBase caps) (fun query => ?_) both
  refine (wBound_query _ _ _).mpr ?_
  rcases query with _ | _ <;> simp [wCcaBase, PqxdhServerAuthSourceCosts.IsAmbientUniform,
    PqxdhServerAuthSourceCosts.IsAmbientBase]

/-- One step of the post-challenge KEM router costs at most the pool weight of its request: identity work and explicit coins pass through, a decapsulation is local KEM work or one CCA decapsulation. -/
theorem post_router_cost (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    WBound (((PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected reservation challenge candidate
      query).run).run state) (wCcaBase caps) (wPool caps query) := by
  rcases query with identity | (coin | request)
  · simp only [PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run]
    refine wBound_map _ (ccaCoins_cost caps _ ?_)
    exact PqxdhDynamicIdentityPool.lazyImpl_uniform_step setup.joint identity state.1
  · simp only [PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run]
    exact wBound_map _ (ccaCoins_cost caps _ ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩)
  · simp only [PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run]
    refine wBound_map _ ?_
    cases request with
    | create =>
        simp only [PqxdhDynamicKemRouter.post, PqxdhDynamicKemRouter.router, OptionT.run_mk]
        split <;> trivial
    | reveal index =>
        simp only [PqxdhDynamicKemRouter.post, PqxdhDynamicKemRouter.router, OptionT.run_mk]
        split
        · trivial
        · split <;> trivial
    | decapsulate index ciphertext =>
        simp only [PqxdhDynamicKemRouter.post, PqxdhDynamicKemRouter.router, OptionT.run_mk, wPool,
          PqxdhDynamicKemBounds.IsDecapsulation]
        rw [← Nat.add_zero caps.decapsCost]
        refine wBound_bind ?_ fun _ _ => trivial
        unfold PqxdhDynamicKemRouter.postDecapsulation
        split
        · trivial
        · split
          · split
            · trivial
            · exact (wBound_query _ _ _).mpr le_rfl
          · split
            · trivial
            · exact ccaAmbient_cost caps _ _ _ (bounded.decapsUniform _ ciphertext) (bounded.decapsBase _ ciphertext)

/-- The post-challenge router forwarding the table oracles. -/
theorem router_cost (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : (PqxdhLiveKemBirth.Spec KemSK + TSpec V).Domain)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    WBound (((fwdOption (T := TSpec V) (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected reservation
      challenge candidate) query).run).run state) (wCca (V := V) caps) (wPoolT (V := V) caps query) := by
  rcases query with request | table
  · rw [fwdOption_inl]
    exact wBound_liftComp_inl (wCcaBase caps) _ (fun query => by rcases query with (_ | _) | _ <;> rfl)
      (post_router_cost setup caps bounded selected reservation challenge candidate request state)
  · rw [fwdOption_inr]
    exact wBound_map _ ((wBound_query _ _ _).mpr (by rcases table with _ | _ <;> exact le_rfl))

/-- The actual encapsulator forwarding the table oracles: an exposed encapsulation draws its `encapsCost`. -/
theorem actual_cost (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (query : (Enc KemSK + TSpec V).Domain) :
    WBound (fwd (T := TSpec V) (PqxdhRegistrationJointKemEncapsulation.actual setup) query)
      (wPoolT (V := V) caps) (wEnc (V := V) caps query) := by
  rcases query with (pool | request) | table
  · rw [fwd_inl]
    exact wBound_liftComp_inl (wPool caps) _ (fun _ => rfl) ((wBound_query _ _ _).mpr le_rfl)
  · rw [fwd_inl]
    refine wBound_liftComp_inl (wPool caps) _ (fun _ => rfl) ?_
    change WBound (PqxdhLiveKemBirth.coins (PqxdhServerAuthExperiment.encapsulate setup request.2)) _ _
    unfold PqxdhLiveKemBirth.coins
    refine wBound_simulate _ (fun _ => 1) (wPool caps) (fun coin => ?_)
      (wBound_of_total (PqxdhServerAuthSourceCosts.encaps_uniform setup caps bounded request.2))
    exact (wBound_query _ _ _).mpr le_rfl
  · rw [fwd_inr]
    exact (wBound_query _ _ _).mpr (by rcases table with _ | _ <;> exact le_rfl)

/-- A program of the exposed encapsulation interface, run through the actual encapsulator, the post-challenge router and the challenger's CCA evaluation, costs in the skeleton's weight at most its own weight. -/
theorem lower_cost (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (secret : KemSK) (challenge : MlKem768Ciphertext) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (candidate : MlKemSharedSecret) {α : Type}
    (work : OracleComp (Enc KemSK + TSpec V) α) {n : ℕ} (bounded' : WBound work (wEnc (V := V) caps) n)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    WBound (simulateQ (fwd (T := TSpec V) (evalLayer setup secret challenge))
      (((simulateQ (fwdOption (T := TSpec V) (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected
        reservation challenge candidate)) (simulateQ (fwd (T := TSpec V)
          (PqxdhRegistrationJointKemEncapsulation.actual setup)) work)).run).run state)) (wSkel (V := V)) n :=
  wBound_simulate _ _ _ (evalLayer_cost setup caps bounded secret challenge)
    (wBound_option _ _ _ (router_cost setup caps bounded selected reservation challenge candidate)
      (wBound_simulate _ _ _ (actual_cost setup caps bounded) bounded') state)

/-- A native-layer program of the skeleton keeps its weight on the exposed encapsulation interface. -/
theorem liftT_cost (caps : KemCaps) {α : Type} (work : NGame KemSK V α) (state : SkelState KemSK V) {n : ℕ}
    (bounded : WBound (work.run state) (wSkel (V := V)) n) :
    WBound ((liftT work).run state) (wEnc (V := V) caps) n := by
  change WBound (simulateQ (fwd (T := TSpec V) (coinLift (KemSK := KemSK))) (work.run state)) _ _
  refine wBound_simulate _ _ _ (fun query => ?_) bounded
  rcases query with coin | table
  · rw [fwd_inl]
    exact wBound_liftComp_inl (fun query => wEnc (V := V) caps (.inl query)) _ (fun _ => rfl)
      ((wBound_query _ _ _).mpr le_rfl)
  · rw [fwd_inr]
    exact (wBound_query _ _ _).mpr (by rcases table with _ | _ <;> exact le_rfl)

end Lower

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_of_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_of_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_liftComp_inl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wBound_liftComp_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.publicLocal_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.publicLocal_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.evalLayer_inl' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.evalLayer_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.evalLayer_inr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.evalLayer_inr

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.evalLayer_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.evalLayer_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.evalLayer_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.evalLayer_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ccaCoins_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ccaCoins_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ccaAmbient_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ccaAmbient_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.post_router_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.post_router_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.router_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.router_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.actual_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.actual_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.lower_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.lower_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.liftT_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.liftT_cost
