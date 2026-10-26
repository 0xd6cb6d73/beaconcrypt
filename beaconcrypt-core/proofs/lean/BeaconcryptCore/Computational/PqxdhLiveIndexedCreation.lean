import BeaconcryptCore.Computational.PqxdhLiveKemOwnership

/-!
Native owner allocation uses the actual joint-identity and indexed-KEM constructor. The published owner index stays distinct from both private service indices. The complete creation equation retains every earlier role and both complete service histories; selected generation, source reveal routing and the full global scheduler remain separate consumers.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveIndexedCreation
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhStatefulPhase1EufCma PqxdhKemIndCca
open PqxdhLiveOwnerCreation (Owners Reply install Represents)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- The source constructor requests its actual services before publishing the newly allocated owner handle. -/
def create (baseImpl : QueryImpl baseSpec ProbComp)
    (setup : StatefulPhase1Setup baseSpec) (binding : beaconcrypt_core.pqxdh.ServerBinding) :
    StateT (Owners setup Nat) (OracleComp (PqxdhLiveKemBirth.Spec KemSK)) (Option Reply) := fun owners => do
  let value ← PqxdhLiveKemBirth.create baseImpl setup
  pure (install binding value owners)

/-- A native owner resolves to the actual correlated identity and to every private KEM payload retained in its current phase. -/
def Valid (primitives : Primitives) (state : PqxdhLiveKemBirth.State KemSK)
    {setup : StatefulPhase1Setup baseSpec} (owners : Owners setup Nat) : Prop :=
  ∀ owner ∈ owners, Represents primitives state.1 owner ∧ PqxdhLiveKemOwnership.Owner state.2 owner

set_option backward.isDefEq.respectTransparency false in
/-- The complete allocation executes original source generator order and retains all earlier private/native state, publishing only the original owner/public-identity reply. -/
theorem create_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (owners : Owners setup Nat) (state : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((create baseImpl setup binding).run owners)).run state = (do
      let value ← PqxdhLiveBeaconBirth.create baseImpl primitives kem setup
      pure (install binding (some (PqxdhLiveKemBirth.handle primitives state.1.seeds.length state.2.keys.length value)) owners,
        ((createdReply primitives state.1 value.seed).2, (PqxdhLiveKemBirth.created state.2 (value.target, value.secret)).2))) := by
  simp only [create, StateT.run, simulateQ_bind, simulateQ_pure]
  change (((simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
    (PqxdhLiveKemBirth.create baseImpl setup)).run state) >>= fun result =>
    pure (install binding result.1 owners, result.2)) = _
  rw [PqxdhLiveKemBirth.create_source]
  simp only [bind_assoc, pure_bind]

/-- Appending an actual source-generated owner establishes both service relations and preserves every earlier owner without public-key injectivity. -/
theorem install_valid (primitives : Primitives) (state : PqxdhLiveKemBirth.State KemSK)
    {setup : StatefulPhase1Setup baseSpec} (value : PqxdhLiveBeaconBirth.Created setup KemSK)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) (owners : Owners setup Nat)
    (valid : Valid primitives state owners) :
    Valid primitives
      ((createdReply primitives state.1 value.seed).2, (PqxdhLiveKemBirth.created state.2 (value.target, value.secret)).2)
      (install binding (some (PqxdhLiveKemBirth.handle primitives state.1.seeds.length state.2.keys.length value)) owners).2 := by
  intro owner present
  simp only [install, List.mem_append, List.mem_singleton] at present
  rcases present with earlier | rfl
  · exact ⟨PqxdhLiveOwnerCreation.prior_represents primitives state.1 value.seed owner (valid owner earlier).1,
      PqxdhLiveKemOwnership.created_prior_owner state.2 (value.target, value.secret) owner (valid owner earlier).2⟩
  · exact ⟨⟨value.seed, PqxdhLiveJointBirth.created_seed primitives state.1 value.seed, rfl⟩,
      PqxdhLiveKemOwnership.created_known state.2 (value.target, value.secret)⟩

/-- Actual supported owner creation preserves both private services and every retained native owner. -/
theorem create_valid (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (owners : Owners setup Nat) (state : PqxdhLiveKemBirth.State KemSK) (valid : Valid primitives state owners)
    (result : (Option Reply × Owners setup Nat) × PqxdhLiveKemBirth.State KemSK)
    (actual : result ∈ support ((simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((create baseImpl setup binding).run owners)).run state)) :
    Valid primitives result.2 result.1.2 := by
  rw [create_source] at actual
  simp only [mem_support_bind_iff, mem_support_pure_iff] at actual
  obtain ⟨value, _, rfl⟩ := actual
  exact install_valid primitives state value binding owners valid

/-- Starting with no native owners needs no representation premise for an invented owner. -/
theorem empty_valid (primitives : Primitives) (state : PqxdhLiveKemBirth.State KemSK)
    (setup : StatefulPhase1Setup baseSpec) : Valid primitives state ([] : Owners setup Nat) := by
  simp [Valid]

/-- Allocation changes no source sampling cost: identity32, actual prekey generation and actual KEM generation remain charged. -/
theorem create_uniform (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (owners : Owners setup Nat) (state : PqxdhLiveKemBirth.State KemSK) (qPrekey qKeygen : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen) :
    ((simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((create baseImpl setup binding).run owners)).run state).IsTotalQueryBound (32 + (qPrekey + qKeygen)) := by
  rw [create_source]
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhLiveBeaconBirth.create_uniform baseImpl primitives kem setup qPrekey qKeygen prekeyBound keygenBound

/-- Publishing the native owner adds no requests to any constructor service class. -/
theorem create_bills (baseImpl : QueryImpl baseSpec ProbComp)
    (setup : StatefulPhase1Setup baseSpec) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (owners : Owners setup Nat) (qPrekey : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (kind : PqxdhLiveKemBirth.Kind) :
    ((create (KemSK := KemSK) baseImpl setup binding).run owners).IsQueryBoundP
      (PqxdhLiveKemBirth.IsKind (KemSK := KemSK) kind)
      ((if kind = .joint then 1 else 0) +
        ((if kind = .localUniform then qPrekey else 0) + (if kind = .kem then 1 else 0))) := by
  simpa only [create, StateT.run, bind_pure_comp, isQueryBoundP_map_iff] using
    PqxdhLiveKemBirth.create_bills (KemSK := KemSK) baseImpl setup qPrekey prekeyBound kind

/-- The source returns a native-owner index while retaining the separate actual identity and KEM-service indices in the complete new role. -/
theorem allocated_lookup (primitives : Primitives) (state : PqxdhLiveKemBirth.State KemSK)
    {setup : StatefulPhase1Setup baseSpec} (value : PqxdhLiveBeaconBirth.Created setup KemSK)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) (owners : Owners setup Nat) :
    let created := PqxdhLiveKemBirth.handle primitives state.1.seeds.length state.2.keys.length value
    (install binding (some created) owners).1 = some (owners.length, primitives.publicKeys value.seed) ∧
      (install binding (some created) owners).2[owners.length]? = some
        (PqxdhLiveJointBirth.fresh created binding) :=
  PqxdhLiveOwnerCreation.allocated_lookup binding _ owners

end BeaconcryptCore.Computational.PqxdhLiveIndexedCreation

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.create_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.install_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.install_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.create_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.create_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.empty_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.empty_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.create_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.create_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.create_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.create_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.allocated_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveIndexedCreation.allocated_lookup
