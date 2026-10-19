import BeaconcryptCore.Computational.PqxdhLiveKemRouting
import BeaconcryptCore.Computational.PqxdhPhase2KemProvenance

/-!
Actual indexed creation and retained native-owner handles establish the reversible selected/other representation. The relation uses one private list slot, not public-key injectivity or accepted-key honesty. The dynamic generation/reveal compiler must still preserve it alongside its actual private history.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveKemOwnership
open PqxdhLiveKemRouting PqxdhKemIndCca
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK I D : Type}

/-- The source's actual fresh creation returns the public bytes and index of its newly stored private pair. -/
theorem created_known (pool : PqxdhLiveKemBirth.Pool KemSK) (pair : MlKem768PublicKey × KemSK) :
    Known (PqxdhLiveKemBirth.created pool pair).2 (pair.1, pool.keys.length) :=
  ⟨pair.2, (PqxdhLiveKemBirth.created_lookup pool pair).2⟩

/-- A retained handle at the selected creation index has that slot's public bytes, by list lookup alone. -/
theorem selected_public (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat)
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (handle : Handle) (known : Known pool handle) (same : handle.2 = selected) :
    handle.1 = target := by
  rcases known with ⟨key, lookup⟩
  simpa only [same, present, Option.map_some, Option.some.injEq] using (congrArg (Option.map Prod.fst) lookup).symm

/-- Reconstruct the selected slot from its public creation descriptor; all other handles remain unchanged. -/
def decode (selected : Nat) (target : MlKem768PublicKey) : Option Handle → Handle
  | none => (target, selected)
  | some handle => handle

/-- The source-created ownership relation makes selected/other encoding reversible without comparing distinct owners' public bytes. -/
theorem decode_encode (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat)
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (handle : Handle) (known : Known pool handle) :
    decode selected target (encode selected handle) = handle := by
  by_cases same : handle.2 = selected
  · simpa only [encode, ite_eq_left same, decode] using
      Prod.ext (selected_public pool selected target secret present handle known same).symm same.symm
  · simp only [encode, ite_eq_right same, decode]

/-- Every retained native KEM payload resolves to the actual private creation pool. Terminal phases contain no such payload. -/
def Owner (pool : PqxdhLiveKemBirth.Pool KemSK) (state : RawCtxBeaconLifecycle.State I D Handle) : Prop :=
  PqxdhPhase2KemProvenance.Phase (Known pool) state.beacon.phase

/-- Complete native state, including every private prekey, binding and attempt field, is reconstructed from the reversible indexed handle representation. -/
theorem owner_inverse (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat)
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (state : RawCtxBeaconLifecycle.State I D Handle) (valid : Owner pool state) :
    PqxdhBeaconPhase1Publication.mapState id (decode selected target)
      (PqxdhBeaconPhase1Publication.mapState id (encode selected) state) = state := by
  cases state with
  | mk beacon attempts =>
    cases beacon with
    | mk identity keyId serverIdentity phase =>
      cases phase <;> simp only [Owner, PqxdhPhase2KemProvenance.Phase] at valid
      all_goals simp only [PqxdhBeaconPhase1Publication.mapState, PqxdhBeaconPhase1Publication.mapPhase, id_eq]
      all_goals rw [decode_encode pool selected target secret present _ valid]

/-- The complete interpreted native owner retains its optional plaintext and all auxiliary state under the actual indexed selected/other representation. -/
theorem native_encoded_run {A X Response : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D Handle X Response) (StateT A m))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (decodeFrame : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxBeaconLifecycle.State I D Handle) (valid : Owner pool state) (auxiliary : A) :
    (fun result => ((result.1.1, PqxdhBeaconPhase1Publication.mapState id (decode selected target) result.1.2), result.2)) <$>
      (simulateQ (handler ∘ₛ PqxdhPhase2KemHandles.native (decode selected target))
        (PqxdhBeaconPhase2Publication.nativeOwner decodeFrame raw
          (PqxdhBeaconPhase1Publication.mapState id (encode selected) state))).run auxiliary =
      (simulateQ handler (PqxdhBeaconPhase2Publication.nativeOwner decodeFrame raw state)).run auxiliary := by
  rw [PqxdhPhase2KemHandles.native_owner_run, owner_inverse pool selected target secret present state valid]

/-- A later source creation preserves every earlier handle's actual private slot, including public-byte aliases. -/
theorem created_prior_known (pool : PqxdhLiveKemBirth.Pool KemSK)
    (pair : MlKem768PublicKey × KemSK) (handle : Handle) (known : Known pool handle) :
    Known (PqxdhLiveKemBirth.created pool pair).2 handle := by
  rcases known with ⟨secret, lookup⟩
  exact ⟨secret, (PqxdhLiveKemBirth.created_prior pool pair handle.2
    (List.getElem?_eq_some_iff.mp lookup).1).trans lookup⟩

/-- Every actually supported identity/prekey/KEM constructor reply resolves to its newly created slot in the same complete private service state. -/
theorem create_known (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (state : PqxdhLiveKemBirth.State KemSK)
    (result : Option (PqxdhLiveJointBirth.Created setup Nat) × PqxdhLiveKemBirth.State KemSK)
    (actual : result ∈ support ((simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      (PqxdhLiveKemBirth.create baseImpl setup)).run state)) :
    ∀ value, result.1 = some value → Known result.2.2 (value.target, value.secret) := by
  rw [PqxdhLiveKemBirth.create_source] at actual
  simp only [mem_support_bind_iff, mem_support_pure_iff] at actual
  obtain ⟨created, _, rfl⟩ := actual
  simpa only [Option.some.injEq, forall_eq', PqxdhLiveKemBirth.handle] using
    created_known state.2 (created.target, created.secret)

/-- The actual constructor's returned handle establishes ownership of the full installed Fresh role, including its original binding and private prekey. -/
theorem create_owner (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (state : PqxdhLiveKemBirth.State KemSK)
    (result : Option (PqxdhLiveJointBirth.Created setup Nat) × PqxdhLiveKemBirth.State KemSK)
    (actual : result ∈ support ((simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      (PqxdhLiveKemBirth.create baseImpl setup)).run state))
    (value : PqxdhLiveJointBirth.Created setup Nat) (returned : result.1 = some value)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) :
    Owner result.2.2 (PqxdhLiveJointBirth.fresh value binding) :=
  create_known baseImpl primitives kem setup state result actual value returned

/-- Appending another private KEM creation preserves the complete earlier owner's retained-handle relation. -/
theorem created_prior_owner (pool : PqxdhLiveKemBirth.Pool KemSK)
    (pair : MlKem768PublicKey × KemSK) (state : RawCtxBeaconLifecycle.State I D Handle)
    (valid : Owner pool state) : Owner (PqxdhLiveKemBirth.created pool pair).2 state := by
  cases phase : state.beacon.phase <;> simp only [Owner, phase, PqxdhPhase2KemProvenance.Phase] at valid ⊢
  all_goals exact created_prior_known pool pair _ valid

end BeaconcryptCore.Computational.PqxdhLiveKemOwnership

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemOwnership.created_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemOwnership.created_known

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemOwnership.selected_public' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemOwnership.selected_public

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemOwnership.decode_encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemOwnership.decode_encode

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemOwnership.owner_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemOwnership.owner_inverse

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemOwnership.native_encoded_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemOwnership.native_encoded_run

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemOwnership.created_prior_known' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemOwnership.created_prior_known

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemOwnership.create_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemOwnership.create_known

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemOwnership.create_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemOwnership.create_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemOwnership.created_prior_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemOwnership.created_prior_owner
