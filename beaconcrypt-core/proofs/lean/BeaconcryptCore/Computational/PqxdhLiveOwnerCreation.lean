import BeaconcryptCore.Computational.PqxdhLiveJointBirth
import BeaconcryptCore.Computational.PqxdhLiveJointSigning

/-!
Honest native owner allocation consumes the actual joint birth program. The public reply contains an owner index and public identity only. The private role retains all generated prekey and KEM state; joint seed indices remain separate from owner indices. The complete evaluated source equation preserves all earlier owners and joint observations, with no injectivity premise on public encodings.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveOwnerCreation
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhStatefulPhase1EufCma PqxdhKemIndCca

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

abbrev Owners (setup : StatefulPhase1Setup baseSpec) (KemSK : Type) :=
  List (PqxdhLiveJointBirth.Beacon setup KemSK)

abbrev Reply := Nat × PublicIdentity

/-- Native allocation publishes a role handle, not its private generated material or the identity-service index. -/
def install {setup : StatefulPhase1Setup baseSpec}
    (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (created : Option (PqxdhLiveJointBirth.Created setup KemSK))
    (owners : Owners setup KemSK) : Option Reply × Owners setup KemSK :=
  match created with
  | none => (none, owners)
  | some created =>
      (some (owners.length, created.publicIdentity), owners ++ [PqxdhLiveJointBirth.fresh created binding])

def create (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) :
    StateT (Owners setup KemSK) (OracleComp PqxdhLiveJointBirth.Spec) (Option Reply) := fun owners => do
  let created ← PqxdhLiveJointBirth.create baseImpl kem setup
  pure (install binding created owners)

/-- A valid live owner refers to the actual joint seed and its actual correlated public identity. This is source representation, not network authentication. -/
def Represents (primitives : Primitives) (joint : SourceState)
    {setup : StatefulPhase1Setup baseSpec} (owner : PqxdhLiveJointBirth.Beacon setup KemSK) : Prop :=
  ∃ seed, joint.seeds[owner.beacon.identity.1]? = some seed ∧
    owner.beacon.identity.2 = primitives.publicKeys seed

def Valid (primitives : Primitives) (joint : SourceState)
    {setup : StatefulPhase1Setup baseSpec} (owners : Owners setup KemSK) : Prop :=
  ∀ owner ∈ owners, Represents primitives joint owner

/-- No owner exists initially, so no source identity agreement is assumed. -/
theorem empty_valid (primitives : Primitives) (joint : SourceState)
    (setup : StatefulPhase1Setup baseSpec) : Valid primitives joint ([] : Owners setup KemSK) := by
  simp [Valid]

/-- The freshly allocated source owner keeps the exact seed/public pair at its own joint index. -/
theorem new_represents (primitives : Primitives) (joint : SourceState)
    {setup : StatefulPhase1Setup baseSpec} (created : PqxdhLiveBeaconBirth.Created setup KemSK)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) :
    Represents primitives (createdReply primitives joint created.seed).2
      (PqxdhLiveJointBirth.fresh (PqxdhLiveJointBirth.handle primitives joint.seeds.length created) binding) := by
  exact ⟨created.seed, PqxdhLiveJointBirth.created_seed primitives joint created.seed, rfl⟩

/-- Allocation preserves prior seed/public agreement even if distinct public encodings coincide. -/
theorem prior_represents (primitives : Primitives) (joint : SourceState) (seed : IdentitySeed)
    {setup : StatefulPhase1Setup baseSpec} (owner : PqxdhLiveJointBirth.Beacon setup KemSK)
    (valid : Represents primitives joint owner) :
    Represents primitives (createdReply primitives joint seed).2 owner := by
  obtain ⟨prior, lookup, publicEq⟩ := valid
  refine ⟨prior, ?_, publicEq⟩
  rw [PqxdhLiveJointBirth.created_prior primitives joint seed owner.beacon.identity.1 ?_]
  · exact lookup
  · exact List.getElem?_eq_some_iff.mp lookup |>.1

/-- Actual source creation preserves every earlier owner and establishes the new owner's exact seed/public representation. -/
theorem install_valid (primitives : Primitives) (joint : SourceState)
    {setup : StatefulPhase1Setup baseSpec} (created : PqxdhLiveBeaconBirth.Created setup KemSK)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) (owners : Owners setup KemSK)
    (valid : Valid primitives joint owners) :
    Valid primitives (createdReply primitives joint created.seed).2
      (install binding (some (PqxdhLiveJointBirth.handle primitives joint.seeds.length created)) owners).2 := by
  intro owner present
  simp only [install, List.mem_append, List.mem_singleton] at present
  rcases present with earlier | rfl
  · exact prior_represents primitives joint created.seed owner (valid owner earlier)
  · exact new_represents primitives joint created binding

set_option backward.isDefEq.respectTransparency false in
/-- Allocation runs the actual source constructor in place and retains the complete existing registry and joint history. No generator is moved across a later operation. -/
theorem create_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (owners : Owners setup KemSK) (joint : SourceState) :
    (simulateQ (PqxdhLiveJointBirth.impl primitives)
      ((create baseImpl kem setup binding).run owners)).run joint = (do
      let created ← PqxdhLiveBeaconBirth.create baseImpl primitives kem setup
      pure (install binding (some (PqxdhLiveJointBirth.handle primitives joint.seeds.length created)) owners,
        (createdReply primitives joint created.seed).2)) := by
  simp only [create, StateT.run, simulateQ_bind, simulateQ_pure]
  change (((simulateQ (PqxdhLiveJointBirth.impl primitives)
    (PqxdhLiveJointBirth.create baseImpl kem setup)).run joint) >>= fun result =>
    pure (install binding result.1 owners, result.2)) = _
  rw [PqxdhLiveJointBirth.create_complete]
  simp only [bind_assoc, pure_bind]

/-- Every supported native allocation outcome establishes source representation for the whole private registry, without an honest network-target premise. -/
theorem create_valid (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (owners : Owners setup KemSK) (joint : SourceState) (valid : Valid primitives joint owners)
    (result : (Option Reply × Owners setup KemSK) × SourceState)
    (actual : result ∈ support ((simulateQ (PqxdhLiveJointBirth.impl primitives)
      ((create baseImpl kem setup binding).run owners)).run joint)) :
    Valid primitives result.2 result.1.2 := by
  rw [create_source] at actual
  simp only [mem_support_bind_iff, mem_support_pure_iff] at actual
  obtain ⟨created, _, rfl⟩ := actual
  exact install_valid primitives joint created binding owners valid

/-- The returned owner index resolves to the complete newly created private role; it is not equated with the separately allocated identity-service index. -/
theorem allocated_lookup {setup : StatefulPhase1Setup baseSpec}
    (binding : beaconcrypt_core.pqxdh.ServerBinding) (created : PqxdhLiveJointBirth.Created setup KemSK)
    (owners : Owners setup KemSK) :
    (install binding (some created) owners).1 = some (owners.length, created.publicIdentity) ∧
    (install binding (some created) owners).2[owners.length]? = some (PqxdhLiveJointBirth.fresh created binding) := by
  simp [install]

/-- Every older native owner remains byte-for-byte represented by the same complete value. -/
theorem allocated_prior {setup : StatefulPhase1Setup baseSpec}
    (binding : beaconcrypt_core.pqxdh.ServerBinding) (created : PqxdhLiveJointBirth.Created setup KemSK)
    (owners : Owners setup KemSK) (index : Nat) (prior : index < owners.length) :
    (install binding (some created) owners).2[index]? = owners[index]? := by
  simp only [install, List.getElem?_append_left prior]

set_option backward.isDefEq.respectTransparency false in
/-- Native allocation adds no random sampling to the source identity, prekey and KEM generators; their complete ordinary callback bills remain charged. -/
theorem create_uniform (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (owners : Owners setup KemSK) (joint : SourceState) (qPrekey qKeygen : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen) :
    ((simulateQ (PqxdhLiveJointBirth.impl primitives)
      ((create baseImpl kem setup binding).run owners)).run joint).IsTotalQueryBound (32 + (qPrekey + qKeygen)) := by
  rw [create_source]
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhLiveBeaconBirth.create_uniform baseImpl primitives kem setup qPrekey qKeygen prekeyBound keygenBound

end BeaconcryptCore.Computational.PqxdhLiveOwnerCreation

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.empty_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.empty_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.new_represents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.new_represents

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.prior_represents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.prior_represents

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.install_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.install_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.create_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.create_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.create_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.allocated_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.allocated_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.allocated_prior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.allocated_prior

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.create_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveOwnerCreation.create_uniform
