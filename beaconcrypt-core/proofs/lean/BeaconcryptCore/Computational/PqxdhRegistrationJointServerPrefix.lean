-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts

/-! The actual ordered Server prefix through the indexed joint identity service. The compiler carries a private service index and public callback inputs, with no Server seed. Every other native callback, optional reply, generator and consumed-registration state is retained. Exact seed-slot ownership is a representation condition to be supplied by actual initialization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhRegistrationJointPreparation (Pool)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result A : Type}

abbrev NativeSpec (Reader : Type) := PqxdhServerRootPreparation.Spec Reader ScalarBytes Word32
abbrev AuxSpec (Reader : Type) := PqxdhServerRootPreparation.Spec Reader ScalarBytes Unit
abbrev Spec (KemSK Reader : Type) := PqxdhLiveKemBirth.Spec KemSK + AuxSpec Reader
abbrev State (KemSK A : Type) := Pool KemSK × A

def onPool (work : StateT (Pool KemSK) ProbComp Result) : StateT (State KemSK A) ProbComp Result :=
  fun state => (fun result => (result.1, (result.2, state.2))) <$> work.run state.1

def onAux (work : StateT A ProbComp Result) : StateT (State KemSK A) ProbComp Result :=
  fun state => (fun result => (result.1, (state.1, result.2))) <$> work.run state.2

/-- All native auxiliary callbacks keep their exact interface; only converted static DH routes to the selected private identity slot. -/
def compiler (identityIndex : Nat) : QueryImpl (NativeSpec Reader) (OracleComp (Spec KemSK Reader))
  | .decode raw => (Spec KemSK Reader).query (.inr (.decode raw))
  | .identity reader => (Spec KemSK Reader).query (.inr (.identity reader))
  | .identityPoint identity => (Spec KemSK Reader).query (.inr (.identityPoint identity))
  | .pqField reader => (Spec KemSK Reader).query (.inr (.pqField reader))
  | .preField reader => (Spec KemSK Reader).query (.inr (.preField reader))
  | .oneField reader => (Spec KemSK Reader).query (.inr (.oneField reader))
  | .verify identity bytes => (Spec KemSK Reader).query (.inr (.verify identity bytes))
  | .registrationStatus rid => (Spec KemSK Reader).query (.inr (.registrationStatus rid))
  | .reserveRegistration => (Spec KemSK Reader).query (.inr .reserveRegistration)
  | .parseDh point => (Spec KemSK Reader).query (.inr (.parseDh point))
  | .generate => (Spec KemSK Reader).query (.inr .generate)
  | .parseKem key => (Spec KemSK Reader).query (.inr (.parseKem key))
  | .encapsulate key => (Spec KemSK Reader).query (.inr (.encapsulate key))
  | .publicConversion identity => (Spec KemSK Reader).query (.inr (.publicConversion identity))
  | .privateConversion => (Spec KemSK Reader).query (.inr .privateConversion)
  | .ephemeralDh scalar point => (Spec KemSK Reader).query (.inr (.ephemeralDh scalar point))
  | .staticDh point => (fun reply => Option.map PqxdhRootTableInitialization.rootArray reply.join) <$>
      (Spec KemSK Reader).query (.inl (.inl (.inr (.service identityIndex (.staticDh (PqxdhPhase2GapDhSource.peer point))))))

def impl (setup : Setup baseSpec KemSK) (aux : QueryImpl (AuxSpec Reader) (StateT A ProbComp)) :
    QueryImpl (Spec KemSK Reader) (StateT (State KemSK A) ProbComp)
  | .inl query => onPool (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query)
  | .inr query => onAux (aux query)

/-- Record the one actual converted-DH service reply while keeping every native auxiliary effect in its original source position. -/
def visit (joint : Primitives) (seed : IdentitySeed) (identityIndex : Nat) (point : Word32) :
    StateT (State KemSK A) ProbComp Unit := fun state =>
  let peer := PqxdhPhase2GapDhSource.peer point
  pure ((), ((PqxdhDynamicIdentityPool.record (.inr (.service identityIndex (.staticDh peer)))
    (some (joint.staticDh seed peer)) state.1.1, state.1.2), state.2))

def annotated (joint : Primitives) (seed : IdentitySeed) (identityIndex : Nat)
    (aux : QueryImpl (AuxSpec Reader) (StateT A ProbComp)) : QueryImpl (NativeSpec Reader) (StateT (State KemSK A) ProbComp) :=
  PqxdhServerStaticDhSource.nativeImpl joint seed (fun query => onAux (aux query)) (visit joint seed identityIndex)

set_option backward.isDefEq.respectTransparency false in
/-- Every compiled callback agrees with its actual native callback and complete private history at the exact initialized identity slot. -/
theorem query_source (setup : Setup baseSpec KemSK) (aux : QueryImpl (AuxSpec Reader) (StateT A ProbComp))
    (seed : IdentitySeed) (identityIndex : Nat) (query : (NativeSpec Reader).Domain)
    (state : State KemSK A) (owned : state.1.1.seeds[identityIndex]? = some seed) :
    ((impl setup aux ∘ₛ compiler identityIndex) query).run state =
      (annotated setup.joint seed identityIndex aux query).run state := by
  cases query <;> simp only [QueryImpl.apply_compose, compiler, simulateQ_spec_query, annotated,
    PqxdhServerStaticDhSource.nativeImpl, impl]
  simp only [simulateQ_map, simulateQ_spec_query, impl]
  rw [StateT.run_map, StateT.run_bind]
  simp only [onPool, PqxdhLiveKemBirth.impl, PqxdhDynamicIdentityPool.lazyImpl,
    PqxdhDynamicIdentityPool.poolImpl, StateT.run, owned, Option.map_some,
    PqxdhJointIdentity.primitiveReply, map_pure, visit, pure_bind]
  rfl

/-- Native prefix callbacks preserve all private seed and KEM slots, including on auxiliary failure; only the actual DH observation is appended. -/
theorem query_slots (joint : Primitives) (seed : IdentitySeed) (identityIndex : Nat)
    (aux : QueryImpl (AuxSpec Reader) (StateT A ProbComp)) (query : (NativeSpec Reader).Domain)
    (state : State KemSK A) (result : (NativeSpec Reader).Range query × State KemSK A)
    (supported : result ∈ support ((annotated joint seed identityIndex aux query).run state)) :
    result.2.1.1.seeds = state.1.1.seeds ∧ result.2.1.2.keys = state.1.2.keys := by
  cases query <;> simp only [annotated, PqxdhServerStaticDhSource.nativeImpl, onAux, StateT.run,
    support_map, Set.mem_image] at supported
  all_goals obtain ⟨answer, _, rfl⟩ := supported; exact ⟨rfl, rfl⟩

/-- The entire compiled adaptive prefix has exactly the native reply and complete private/auxiliary state, with ownership propagated through each actually supported callback. -/
theorem program_source (setup : Setup baseSpec KemSK) (aux : QueryImpl (AuxSpec Reader) (StateT A ProbComp))
    (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (NativeSpec Reader) Result)
    (state : State KemSK A) (owned : state.1.1.seeds[identityIndex]? = some seed) :
    (simulateQ (impl setup aux) (simulateQ (compiler identityIndex) program)).run state =
      (simulateQ (annotated setup.joint seed identityIndex aux) program).run state := by
  rw [← QueryImpl.simulateQ_compose]
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, query_source setup aux seed identityIndex query state owned]
      apply bind_congr_of_forall_mem_support
      intro result supported
      exact ih result.1 result.2 (by rw [(query_slots setup.joint seed identityIndex aux query state result supported).1]; exact owned)

/-- Erasing the private disclosure annotation gives the original native callback and its entire auxiliary state. -/
theorem query_projection (joint : Primitives) (seed : IdentitySeed) (identityIndex : Nat)
    (aux : QueryImpl (AuxSpec Reader) (StateT A ProbComp)) (query : (NativeSpec Reader).Domain) (state : State KemSK A) :
    (fun result => (result.1, result.2.2)) <$> (annotated joint seed identityIndex aux query).run state =
      (PqxdhServerStaticDhSource.nativeImpl joint seed aux (fun _ => pure ()) query).run state.2 := by
  cases query <;> simp [annotated, PqxdhServerStaticDhSource.nativeImpl, onAux,
    StateT.run, Functor.map_map]
  rfl

/-- All source callbacks and their complete continuation survive annotation erasure; this equality keeps the actual native generator order. -/
theorem program_projection (joint : Primitives) (seed : IdentitySeed) (identityIndex : Nat)
    (aux : QueryImpl (AuxSpec Reader) (StateT A ProbComp)) (program : OracleComp (NativeSpec Reader) Result)
    (state : State KemSK A) :
    (fun result => (result.1, result.2.2)) <$> (simulateQ (annotated joint seed identityIndex aux) program).run state =
      (simulateQ (PqxdhServerStaticDhSource.nativeImpl joint seed aux (fun _ => pure ())) program).run state.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simpa only [bind_map_left] using congrArg
        (fun work => work >>= fun result =>
          (simulateQ (PqxdhServerStaticDhSource.nativeImpl joint seed aux (fun _ => pure ())) (next result.1)).run result.2)
        (query_projection joint seed identityIndex aux query state)

/-- The actual source prefix: raw admission, attached verification, ephemeral generation, encapsulation and all four DH positions keep their original order. Only static DH uses the private identity service. -/
def clientPrefix (identityIndex : Nat) (raw : Pqxdh.Bytes) :
    OracleComp (Spec KemSK Reader) (Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes Word32)) :=
  simulateQ (compiler identityIndex) (PqxdhServerRootPreparation.collect raw)

/-- The complete compiled raw prefix, including every optional exit and private service history, equals the annotated native source prefix at its exact initialized seed slot. -/
theorem prefix_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (pool : Pool KemSK) (consumed : List Pqxdh.Bytes)
    (owned : pool.1.seeds[identityIndex]? = some seed) :
    (simulateQ (impl setup (serverAux setup codec checks)) (clientPrefix identityIndex raw)).run (pool, consumed) =
      (simulateQ (annotated setup.joint seed identityIndex (serverAux setup codec checks))
        (PqxdhServerRootPreparation.collect raw)).run (pool, consumed) := by
  exact program_source setup (serverAux setup codec checks) seed identityIndex _ (pool, consumed) owned

/-- Forgetting only private service annotations yields the actual native raw prefix with its complete original result and consumed-registration poststate. -/
theorem prefix_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (pool : Pool KemSK) (consumed : List Pqxdh.Bytes)
    (owned : pool.1.seeds[identityIndex]? = some seed) :
    (fun result => (result.1, result.2.2)) <$>
      (simulateQ (impl setup (serverAux setup codec checks)) (clientPrefix identityIndex raw)).run (pool, consumed) =
        (PqxdhServerAuthNative.nativePrefix setup codec checks seed raw).run consumed := by
  rw [prefix_source setup codec checks seed identityIndex raw pool consumed owned]
  exact program_projection setup.joint seed identityIndex (serverAux setup codec checks) _ (pool, consumed)

/-- The complete interpreted prefix charges its original scalar generation and KEM encapsulation/base randomness; the private DH service introduces no new random draw. -/
theorem prefix_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (pool : Pool KemSK) (consumed : List Pqxdh.Bytes)
    (owned : pool.1.seeds[identityIndex]? = some seed) :
    ((simulateQ (impl setup (serverAux setup codec checks)) (clientPrefix identityIndex raw)).run (pool, consumed)).IsTotalQueryBound
      (32 + caps.encapsCost) := by
  have nativeBound : ((fun result => (result.1, result.2.2)) <$>
      (simulateQ (impl setup (serverAux setup codec checks)) (clientPrefix identityIndex raw)).run (pool, consumed)).IsTotalQueryBound
      (32 + caps.encapsCost) := by
    rw [prefix_native setup codec checks seed identityIndex raw pool consumed owned,
      PqxdhServerAuthNative.native_prefix, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
    exact PqxdhServerAuthSourceCosts.server_prefix_uniform setup codec checks caps bounded raw consumed
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using nativeBound

end BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.query_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.query_slots

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.query_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.query_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.program_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.prefix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.prefix_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.prefix_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.prefix_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.prefix_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefix.prefix_uniform
