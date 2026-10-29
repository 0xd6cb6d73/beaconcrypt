-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys
import BeaconcryptCore.Computational.RegistrationNativeG3CellEager

/-! This service opens only the finite material44 cache. Preparation, source gates, allocation failures and the separate nonselected108 cache remain literal. All probability draws are retained as coin queries. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePairedChoice (Choice)
variable {n : Nat} {Value : Type}
attribute [local irreducible] uniformSample

abbrev State (n : Nat) := RegistrationNativeSelectiveHiddenService.State n
abbrev Spec (n : Nat) := RegistrationNativeG3CellEager.Spec (Slot n) Material

def put (before : State n) (cache : (Slot n →ₒ Material).QueryCache) : State n :=
  ({ before.1 with materials := cache }, before.2)

def drop (before : State n) : State n := put before ∅

def coins : QueryImpl unifSpec (OracleComp (Spec n)) := fun query => (Spec n).query (.inl query)

def material (slot : Slot n) : StateT (State n) (OracleComp (Spec n)) Material :=
  StateT.lift ((Spec n).query (.inr slot))

def prepare (input : Message → Option Pqxdh.Bytes) (message : Message) :
    StateT (State n) (OracleComp (Spec n)) (Option Message) := fun before =>
  pure ((input message).map (fun _ => message),
    ({ before.1 with prepared := Function.update before.1.prepared message (input message).isSome }, before.2))

noncomputable def known (bytes : Pqxdh.Bytes) : StateT (State n) (OracleComp (Spec n)) PqxdhServerAuthKeySchedule.Output :=
  fun before => match before.2 bytes with
  | some output => pure (output, before)
  | none => (fun output => (output, (before.1, before.2.cacheQuery bytes output))) <$> simulateQ coins ($ᵗ PqxdhServerAuthKeySchedule.Output)

noncomputable def hiddenDemand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) :
    StateT (State n) (OracleComp (Spec n)) (Option (Choice n)) := fun before =>
  let counted := { before.1 with demands := before.1.demands + 1 }
  if before.1.prepared message then
    match input message with
    | none => pure (none, (counted, before.2))
    | some bytes =>
        if inside bytes then
          match RegistrationNativeHiddenService.reserve bytes counted with
          | (none, after) => pure (none, (after, before.2))
          | (some slot, after) => (fun result => (some (.hidden ⟨slot, result.1⟩), result.2)) <$>
              (material slot).run (after, before.2)
        else pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot source
          (RegistrationNativeRelatedRoot.nativeRoot source bytes))), (counted, before.2))
  else pure (none, (counted, before.2))

noncomputable def demand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message) :
    StateT (State n) (OracleComp (Spec n)) (Option (Choice n)) := fun before =>
  if before.1.prepared message then
    match input message with
    | none => (hiddenDemand source input (RegistrationNativeSelectiveHiddenService.selected inside candidate) message).run before
    | some bytes =>
        if inside bytes && !(RegistrationNativeSelectiveHiddenService.selected inside candidate bytes) then
          (fun result => (some (.known result.1), result.2)) <$>
            (known bytes).run ({ before.1 with demands := before.1.demands + 1 }, before.2)
        else (hiddenDemand source input (RegistrationNativeSelectiveHiddenService.selected inside candidate) message).run before
  else (hiddenDemand source input (RegistrationNativeSelectiveHiddenService.selected inside candidate) message).run before

noncomputable def close (work : StateT (State n) (OracleComp (Spec n)) Value) (before : State n)
    (cache : (Slot n →ₒ Material).QueryCache) : ProbComp (Value × State n) :=
  (fun result => (result.1.1, put result.1.2 result.2)) <$>
    (simulateQ RegistrationNativeG3CellEager.lazy (work.run before)).run cache

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

theorem coins_source (work : ProbComp Value) (cache : (Slot n →ₒ Material).QueryCache) :
    (simulateQ RegistrationNativeG3CellEager.lazy (simulateQ coins work)).run cache =
      (fun value => (value, cache)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeG3CellEager.lazy ∘ₛ coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Slot n →ₒ Material).QueryCache ProbComp) := by
    funext query
    simp only [QueryImpl.compose, coins, simulateQ_spec_query, RegistrationNativeG3CellEager.lazy,
      QueryImpl.add_apply_inl]
  rw [same]
  rw [simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp only [StateT.run_monadLift, monadLift_self, bind_pure_comp]

private theorem coins_apply (work : ProbComp Value) (cache : (Slot n →ₒ Material).QueryCache) :
    simulateQ RegistrationNativeG3CellEager.lazy (simulateQ coins work) cache =
      (fun value => (value, cache)) <$> work := coins_source work cache

private theorem local_coins (work : ProbComp Value) :
    simulateQ (RegistrationNativeG3MetricCoins.localCoins (n := n)) (simulateQ RegistrationNativeHiddenService.coins work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeG3MetricCoins.localCoins (n := n) ∘ₛ RegistrationNativeHiddenService.coins = QueryImpl.id' unifSpec := by
    funext query
    simp only [QueryImpl.compose, RegistrationNativeHiddenService.coins, simulateQ_spec_query,
      RegistrationNativeG3MetricCoins.localCoins, QueryImpl.id', QueryImpl.liftTarget_apply, QueryImpl.id_apply]
  rw [same, simulateQ_id']

/-- Opening a material query retains the exact lazy cache update and every other service field. -/
theorem material_source (slot : Slot n) (before : State n) (cache : (Slot n →ₒ Material).QueryCache) :
    close (material slot) before cache =
      simulateQ RegistrationNativeG3MetricCoins.localCoins
        ((RegistrationNativeSelectiveHiddenService.onHidden (RegistrationNativeHiddenService.material slot)).run (put before cache)) := by
  cases found : cache slot with
  | some value =>
      simp only [close, material, StateT.run_lift, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
        RegistrationNativeG3CellEager.lazy, QueryImpl.add_apply_inr, StateT.run_map]
      rw [QueryImpl.withCaching_run_some _ found]
      simp only [map_pure, RegistrationNativeSelectiveHiddenService.onHidden, StateT.run,
        RegistrationNativeHiddenService.material, put, found, simulateQ_pure]
  | none =>
      simp only [close, material, StateT.run_lift, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
        RegistrationNativeG3CellEager.lazy, QueryImpl.add_apply_inr, StateT.run_map]
      rw [QueryImpl.withCaching_run_none _ found]
      simp only [Functor.map_map, RegistrationNativeSelectiveHiddenService.onHidden, StateT.run,
        RegistrationNativeHiddenService.material, put, found, simulateQ_map, local_coins]
      rfl

/-- The independent known108 reader never inspects the opened material cache. -/
theorem known_source (bytes : Pqxdh.Bytes) (before : State n) (cache : (Slot n →ₒ Material).QueryCache) :
    close (known bytes) before cache =
      simulateQ RegistrationNativeG3MetricCoins.localCoins
        ((RegistrationNativeSelectiveHiddenService.known bytes).run (put before cache)) := by
  cases found : before.2 bytes with
  | some output => simp only [close, known, StateT.run, pure_apply, found, simulateQ_pure, map_pure,
      RegistrationNativeSelectiveHiddenService.known, put]
  | none =>
      simp only [close, known, StateT.run, map_apply, found, simulateQ_map, coins_apply,
        Functor.map_map, RegistrationNativeSelectiveHiddenService.known, put, local_coins]
      rfl

/-- Preparation opens no material cell and preserves every initial cached value. -/
theorem prepare_source (input : Message → Option Pqxdh.Bytes) (message : Message)
    (before : State n) (cache : (Slot n →ₒ Material).QueryCache) :
    close (prepare input message) before cache =
      simulateQ RegistrationNativeG3MetricCoins.localCoins
        ((RegistrationNativeSelectiveHiddenService.prepare input message).run (put before cache)) := by
  simp only [close, prepare, StateT.run, pure_apply, simulateQ_pure, map_pure,
    RegistrationNativeSelectiveHiddenService.prepare, RegistrationNativeSelectiveHiddenService.onHidden,
    RegistrationNativeHiddenService.prepare, put]

private theorem reserve_put (bytes : Pqxdh.Bytes) (before : RegistrationNativeHiddenService.State n)
    (cache : (Slot n →ₒ Material).QueryCache) :
    RegistrationNativeHiddenService.reserve bytes { before with materials := cache } =
      Prod.map id (fun after => { after with materials := cache })
        (RegistrationNativeHiddenService.reserve bytes before) := by
  simp only [RegistrationNativeHiddenService.reserve]
  split
  · rfl
  · split <;> rfl

private theorem close_map {Next : Type} (map : Value → Next)
    (work : StateT (State n) (OracleComp (Spec n)) Value) (before : State n)
    (cache : (Slot n →ₒ Material).QueryCache) :
    close (map <$> work) before cache = Prod.map map id <$> close work before cache := by
  simp only [close, StateT.run_map, simulateQ_map, Functor.map_map]
  rfl

private theorem close_pure (value : Value) (before : State n) (cache : (Slot n →ₒ Material).QueryCache) :
    close (pure value) before cache = pure (value, put before cache) := by
  simp only [close, StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure]

/-- The actual hidden allocator and every failure branch are retained when its sole material read is opened. -/
theorem hidden_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before : State n) (cache : (Slot n →ₒ Material).QueryCache) :
    close (hiddenDemand source input inside message) before cache =
      simulateQ RegistrationNativeG3MetricCoins.localCoins
        ((RegistrationNativeSelectiveHiddenService.onHidden
          (RegistrationNativeHiddenService.demand source input inside message)).run (put before cache)) := by
  cases prepared : before.1.prepared message with
  | false =>
      simp only [close, hiddenDemand, StateT.run, pure_apply, prepared, Bool.false_eq_true, ite_false,
        simulateQ_pure, map_pure, RegistrationNativeSelectiveHiddenService.onHidden,
        RegistrationNativeHiddenService.demand, put]
  | true =>
      cases realized : input message with
      | none =>
          simp only [close, hiddenDemand, StateT.run, pure_apply, prepared, ite_true, realized,
            simulateQ_pure, map_pure, RegistrationNativeSelectiveHiddenService.onHidden,
            RegistrationNativeHiddenService.demand, put]
      | some bytes =>
          cases protectedInput : inside bytes with
          | false =>
              simp only [close, hiddenDemand, StateT.run, pure_apply, prepared, ite_true, realized, protectedInput,
                Bool.false_eq_true, ite_false, simulateQ_pure, map_pure,
                RegistrationNativeSelectiveHiddenService.onHidden, RegistrationNativeHiddenService.demand, put]
          | true =>
              have allocated := reserve_put bytes { before.1 with demands := before.1.demands + 1 } cache
              rcases found : RegistrationNativeHiddenService.reserve bytes
                { before.1 with demands := before.1.demands + 1 } with ⟨slot, after⟩
              rw [found] at allocated
              cases slot with
              | none =>
                  simp only [close, hiddenDemand, StateT.run, pure_apply, prepared, ite_true, realized, protectedInput,
                    found, simulateQ_pure, map_pure,
                    RegistrationNativeSelectiveHiddenService.onHidden, RegistrationNativeHiddenService.demand,
                    put, allocated, Prod.map, id_eq]
              | some slot =>
                  have read := material_source slot (after, before.2) cache
                  simp only [close, hiddenDemand, StateT.run, map_apply, prepared, ite_true, realized, protectedInput,
                    found, RegistrationNativeSelectiveHiddenService.onHidden, RegistrationNativeHiddenService.demand,
                    put, allocated, Prod.map, id_eq, simulateQ_map, Functor.map_map] at read ⊢
                  have mapped := congrArg (fun distribution => Prod.map (fun (value : Material) => some (Choice.hidden ⟨slot, value⟩)) id <$> distribution) read
                  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_apply] using mapped

/-- The complete selective demand, including nonselected known108 reads, has the opened material-cache source law. -/
theorem demand_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message)
    (before : State n) (cache : (Slot n →ₒ Material).QueryCache) :
    close (demand source input inside candidate message) before cache =
      simulateQ RegistrationNativeG3MetricCoins.localCoins
        ((RegistrationNativeSelectiveHiddenService.demand source input inside candidate message).run (put before cache)) := by
  cases prepared : before.1.prepared message with
  | false =>
      simpa only [close, demand, RegistrationNativeSelectiveHiddenService.demand, StateT.run, pure_apply, map_apply, put,
        prepared, Bool.false_eq_true, ite_false] using
        hidden_source source input (RegistrationNativeSelectiveHiddenService.selected inside candidate) message before cache
  | true =>
      cases realized : input message with
      | none =>
          simpa only [close, demand, RegistrationNativeSelectiveHiddenService.demand, StateT.run, pure_apply, map_apply, put,
            prepared, ite_true, realized] using
            hidden_source source input (RegistrationNativeSelectiveHiddenService.selected inside candidate) message before cache
      | some bytes =>
          by_cases other : (inside bytes && !(RegistrationNativeSelectiveHiddenService.selected inside candidate bytes) : Bool) = true
          · have read := known_source bytes ({ before.1 with demands := before.1.demands + 1 }, before.2) cache
            have mapped := congrArg (fun distribution => Prod.map (fun (value : PqxdhServerAuthKeySchedule.Output) => some (Choice.known (n := n) value)) id <$> distribution) read
            simpa only [close, demand, RegistrationNativeSelectiveHiddenService.demand, StateT.run, pure_apply, map_apply, put,
              prepared, ite_true, realized, other, simulateQ_map, StateT.run_map, Functor.map_map,
              Prod.map_def, id_eq, Function.comp_apply] using mapped
          · simpa only [close, demand, RegistrationNativeSelectiveHiddenService.demand, StateT.run, pure_apply, map_apply, put,
              prepared, ite_true, realized, other, Bool.false_eq_true, ite_false] using
              hidden_source source input (RegistrationNativeSelectiveHiddenService.selected inside candidate) message before cache

end BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.material_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.material_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.known_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.prepare_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.hidden_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.hidden_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.demand_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.demand_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.coins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService.coins_source
