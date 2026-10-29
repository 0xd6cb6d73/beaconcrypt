-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDynamicIdentityPool

/-! Generated native Ed25519 identities use public indexed credentials. The private source supplies the same 32-byte seed to public conversion, every signature and every static-DH query. The source retains the exact creation/service transcript; the executable credential has no seed or converted secret. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityInterface
open PqxdhJointIdentity
open PqxdhDynamicIdentityPool

structure Credential where
  handle : Nat
  publicIdentity : PublicIdentity

abbrev Spec {Index : Type} (ambient : OracleSpec Index) := ambient + PoolSpec
abbrev State (Auxiliary : Type) := Auxiliary × SourceState

def source {Index Auxiliary : Type} (ambient : OracleSpec Index)
    (ordinary : QueryImpl ambient (StateT Auxiliary ProbComp)) (primitives : Primitives) :
    QueryImpl (Spec ambient) (StateT (State Auxiliary) ProbComp)
  | .inl query => fun before =>
      (fun result => (result.1, (result.2, before.2))) <$> (ordinary query).run before.1
  | .inr query => fun before =>
      (fun result => (result.1, (before.1, result.2))) <$> (lazyImpl primitives (.inr query)).run before.2

def create {Index : Type} (ambient : OracleSpec Index) : OracleComp (Spec ambient) (Option Credential) :=
  Option.map (fun result => ⟨result.1, result.2⟩) <$>
    ((Spec ambient).query (.inr .create) : OracleComp (Spec ambient) _)

def sign {Index : Type} (ambient : OracleSpec Index) (credential : Credential) (message : Pqxdh.Bytes) :
    OracleComp (Spec ambient) (Option PqxdhEd25519EufCma.Ed25519Signature) :=
  (Spec ambient).query (.inr (.service credential.handle (.sign message)))

def staticDh {Index : Type} (ambient : OracleSpec Index) (credential : Credential) (peer : PeerEncoding) :
    OracleComp (Spec ambient) (Option (Option DhOutput)) :=
  (Spec ambient).query (.inr (.service credential.handle (.staticDh peer)))

private theorem source_pool {Index Auxiliary : Type} (ambient : OracleSpec Index)
    (ordinary : QueryImpl ambient (StateT Auxiliary ProbComp)) (primitives : Primitives)
    (query : PoolSpec.Domain) (before : State Auxiliary) :
    (source ambient ordinary primitives (.inr query)).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        (lazyImpl primitives (.inr query)).run before.2 := rfl

/-- The actual create operation samples at the call position, appends that seed privately and publishes only its generated index and correlated public keys. -/
theorem create_source {Index Auxiliary : Type} (ambient : OracleSpec Index)
    (ordinary : QueryImpl ambient (StateT Auxiliary ProbComp)) (primitives : Primitives)
    (before : State Auxiliary) :
    (simulateQ (source ambient ordinary primitives) (create ambient)).run before =
      (fun seed => (some (⟨before.2.seeds.length, primitives.publicKeys seed⟩ : Credential),
        (before.1, (createdReply primitives before.2 seed).2))) <$> sampleSeed := by
  simp only [create, simulateQ_map, simulateQ_spec_query]
  rw [StateT.run_map, source_pool, lazyImpl_create]
  simp only [Functor.map_map, createdReply, Option.map_some]

/-- The same privately generated seed determines the service reply, and every attempted request is recorded even when its handle is absent. -/
theorem service_source {Index Auxiliary : Type} (ambient : OracleSpec Index)
    (ordinary : QueryImpl ambient (StateT Auxiliary ProbComp)) (primitives : Primitives)
    (handle : Nat) (request : JointSpec.Domain) (before : State Auxiliary) :
    (source ambient ordinary primitives (.inr (.service handle request))).run before =
      pure ((before.2.seeds[handle]?).map (fun seed => primitiveReply primitives seed request),
        (before.1, record (.inr (.service handle request))
          ((before.2.seeds[handle]?).map (fun seed => primitiveReply primitives seed request)) before.2)) := by
  simp only [source, lazyImpl, poolImpl, StateT.run, map_pure]

end BeaconcryptCore.Computational.RegistrationNativeIdentityInterface

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityInterface.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityInterface.create_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityInterface.service_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityInterface.service_source
