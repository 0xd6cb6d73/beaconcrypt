import BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication
import BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication

/-!
KEM representation changes preserve the complete source Phase2 program. Only the retained KEM handle sent to decapsulation is mapped. Parsing, joint identity operations, every original optional reply, publication and terminal abort keep their order. These equalities supply a handle compiler, not a secrecy or key-honesty premise.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2KemHandles
open PqxdhBeaconPhase2Preparation (Bytes State)
variable {I D K K' X Response : Type}

def preparation (kem : K → K') :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response)
      (OracleComp (PqxdhBeaconPhase2Preparation.Spec I D K' X Response))
  | .decode raw => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.decode raw)
  | .ciphertext response => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.ciphertext response)
  | .ephemeral response => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.ephemeral response)
  | .serverIdentity response => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.serverIdentity response)
  | .publicConversion value => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.publicConversion value)
  | .privateConversion identity => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.privateConversion identity)
  | .decapsulate value key => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.decapsulate value (kem key))
  | .dhPair pair value => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.dhPair pair value)
  | .dhIdentity identity value => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.dhIdentity identity value)
  | .assignedId response => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.assignedId response)
  | .eraseShared shared => (PqxdhBeaconPhase2Preparation.Spec I D K' X Response).query (.eraseShared shared)

/-- Every original getter and DH/decapsulation callback keeps its place under private KEM handle mapping. -/
theorem collect_map (kem : K → K') (identity : I) (prekey oneTime : D) (key : K) (raw : Bytes) :
    simulateQ (preparation (X := X) (Response := Response) kem)
      (PqxdhBeaconPhase2Preparation.collect identity prekey oneTime key raw) =
      PqxdhBeaconPhase2Preparation.collect identity prekey oneTime (kem key) raw := by
  simp only [PqxdhBeaconPhase2Preparation.collect, OptionT.run_bind, OptionT.run_mk,
    OptionT.run_pure, OptionT.run_monadLift, Option.elimM, simulateQ_bind, simulateQ_spec_query,
    preparation]
  repeat' (
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      preparation, Option.elim_none, Option.elim_some, bind_map_left]
    all_goals first | rfl | (congr 1; funext reply; cases reply))

/-- Core preparation and unconditional secret clearing retain the same input and exact outcome. -/
theorem afterInputs_map (kem : K → K') (control : pqxdh.BeaconInitSent)
    (inputs : PqxdhBeaconPhase2Preparation.Inputs Response) :
    simulateQ (preparation (I := I) (D := D) (X := X) kem)
      (PqxdhBeaconPhase2Preparation.afterInputs control inputs) =
      PqxdhBeaconPhase2Preparation.afterInputs control inputs := by
  simp only [PqxdhBeaconPhase2Preparation.afterInputs, simulateQ_bind, simulateQ_spec_query,
    preparation, simulateQ_pure]

/-- The entire original preparation keeps every optional result under the same retained key map. -/
theorem prepare_map (kem : K → K') (control : pqxdh.BeaconInitSent)
    (identity : I) (prekey oneTime : D) (key : K) (raw : Bytes) :
    simulateQ (preparation (X := X) (Response := Response) kem)
      (PqxdhBeaconPhase2Preparation.prepare control identity prekey oneTime key raw) =
      PqxdhBeaconPhase2Preparation.prepare control identity prekey oneTime (kem key) raw := by
  simp only [PqxdhBeaconPhase2Preparation.prepare, simulateQ_bind, collect_map]
  apply bind_congr
  intro reply
  cases reply <;> simp only [simulateQ_pure, afterInputs_map]

/-- Successful publication and terminal abort retain every field under the private KEM representation map. -/
theorem finish_map (kem : K → K') (control : pqxdh.BeaconInitSent) (state : State I D K)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (fun result => (result.1, PqxdhBeaconPhase1Publication.mapState id kem result.2))
        (PqxdhBeaconPhase2Publication.finish control state staged) =
      PqxdhBeaconPhase2Publication.finish control (PqxdhBeaconPhase1Publication.mapState id kem state) staged := by
  cases staged with
  | none => rfl
  | some staged =>
    simp only [PqxdhBeaconPhase2Publication.finish, PqxdhBeaconPhase1Publication.mapState]
    split_ifs <;> simp_all [PqxdhBeaconPhase2Preparation.abort,
      PqxdhBeaconPhase2Publication.publish, PqxdhBeaconPhase1Publication.mapPhase]

def full (kem : K → K') :
    QueryImpl (PqxdhBeaconPhase2Publication.FullSpec I D K X Response)
      (OracleComp (PqxdhBeaconPhase2Publication.FullSpec I D K' X Response))
  | .inl query => simulateQ PqxdhBeaconPhase2Publication.preLift (preparation kem query)
  | .inr query => (PqxdhBeaconPhase2Publication.FullSpec I D K' X Response).query (.inr query)

/-- Preparation forwarding keeps the same original source request, with only its KEM handle represented differently. -/
theorem full_pre (kem : K → K') :
    full (I := I) (D := D) (X := X) (Response := Response) kem ∘ₛ PqxdhBeaconPhase2Publication.preLift =
      PqxdhBeaconPhase2Publication.preLift ∘ₛ preparation kem := by
  funext query
  exact simulateQ_spec_query (full kem) (.inl query)

/-- Root, initial64, raw opening and publication callbacks retain the original tail interface. -/
theorem full_tail (kem : K → K') :
    full (I := I) (D := D) (X := X) (Response := Response) kem ∘ₛ PqxdhBeaconPhase2Publication.tailLift =
      PqxdhBeaconPhase2Publication.tailLift := by
  funext query
  exact simulateQ_spec_query (full kem) (.inr query)

/-- The complete source owner commutes with private KEM handle mapping, including inactive calls and every terminal outcome. -/
theorem owner_map (kem : K → K') (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : State I D K) :
    (fun result => (result.1, PqxdhBeaconPhase1Publication.mapState id kem result.2)) <$>
      simulateQ (full (X := X) (Response := Response) kem) (PqxdhBeaconPhase2Publication.owner decode raw state) =
      PqxdhBeaconPhase2Publication.owner decode raw (PqxdhBeaconPhase1Publication.mapState id kem state) := by
  cases state with
  | mk beacon attempts =>
    cases beacon with
    | mk identity keyId pinned phase =>
      cases phase <;> simp only [PqxdhBeaconPhase2Publication.owner,
        PqxdhBeaconPhase1Publication.mapState, PqxdhBeaconPhase1Publication.mapPhase,
        simulateQ_pure, map_pure]
      case initSent control prekey oneTime key =>
        simp only [simulateQ_bind, map_bind]
        rw [← QueryImpl.simulateQ_compose, full_pre, QueryImpl.simulateQ_compose, prepare_map]
        apply bind_congr
        intro reply
        cases reply with
        | none => simp only [simulateQ_pure, map_pure]; rfl
        | some prepared =>
          simp only [simulateQ_bind, map_bind, simulateQ_pure, map_pure]
          rw [← QueryImpl.simulateQ_compose, full_tail]
          apply bind_congr
          intro staged
          exact congrArg pure (finish_map kem control ⟨⟨identity, keyId, pinned, .initSent control prekey oneTime key⟩, attempts⟩ staged)

def native (kem : K → K') :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response)
      (OracleComp (PqxdhBeaconPhase2Publication.NativeSpec I D K' X Response))
  | .inl query => simulateQ (fun request =>
      (PqxdhBeaconPhase2Publication.NativeSpec I D K' X Response).query (.inl request)) (preparation kem query)
  | .inr query => (PqxdhBeaconPhase2Publication.NativeSpec I D K' X Response).query (.inr query)

/-- Native raw KDF/hash/AEAD and root/initial/getter callbacks retain their exact original interface. -/
theorem native_tail (kem : K → K') :
    native (I := I) (D := D) (X := X) (Response := Response) kem ∘ₛ PqxdhBeaconPhase2Publication.nativeTailLift =
      PqxdhBeaconPhase2Publication.nativeTailLift := by
  funext query
  exact simulateQ_spec_query (native kem) (.inr query)

/-- The original native opening expansion commutes with private KEM handle translation. -/
theorem native_adapter (kem : K → K') :
    native (I := I) (D := D) (X := X) (Response := Response) kem ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter =
      PqxdhBeaconPhase2Publication.nativeAdapter ∘ₛ full kem := by
  funext query
  cases query with
  | inl query =>
    change simulateQ (native kem) (liftM ((PqxdhBeaconPhase2Publication.NativeSpec I D K X Response).query (.inl query))) = _
    refine (simulateQ_spec_query (native kem) (.inl query)).trans ?_
    change simulateQ (fun request => (liftM ((PqxdhBeaconPhase2Publication.NativeSpec I D K' X Response).query (.inl request)) : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec I D K' X Response) _))
      (preparation kem query) = simulateQ PqxdhBeaconPhase2Publication.nativeAdapter
        (simulateQ PqxdhBeaconPhase2Publication.preLift (preparation kem query))
    rw [← QueryImpl.simulateQ_compose]
    apply congrArg (fun handler => simulateQ handler (preparation kem query))
    funext request
    exact (simulateQ_spec_query PqxdhBeaconPhase2Publication.nativeAdapter (.inl request)).symm
  | inr query =>
    change simulateQ (native kem) (simulateQ PqxdhBeaconPhase2Publication.nativeTailLift
      (PqxdhBeaconPhase2Publication.nativeTailAdapter query)) =
        simulateQ PqxdhBeaconPhase2Publication.nativeAdapter
          (liftM ((PqxdhBeaconPhase2Publication.FullSpec I D K' X Response).query (.inr query)))
    rw [← QueryImpl.simulateQ_compose, native_tail]
    exact (simulateQ_spec_query PqxdhBeaconPhase2Publication.nativeAdapter (.inr query)).symm

/-- Complete native Phase2 execution retains original Optional output and mapped owner state through the same primitive expansion. -/
theorem native_owner_map (kem : K → K') (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : State I D K) :
    (fun result => (result.1, PqxdhBeaconPhase1Publication.mapState id kem result.2)) <$>
      simulateQ (native (X := X) (Response := Response) kem) (PqxdhBeaconPhase2Publication.nativeOwner decode raw state) =
      PqxdhBeaconPhase2Publication.nativeOwner decode raw (PqxdhBeaconPhase1Publication.mapState id kem state) := by
  simp only [PqxdhBeaconPhase2Publication.nativeOwner]
  rw [← QueryImpl.simulateQ_compose, native_adapter, QueryImpl.simulateQ_compose, ← simulateQ_map, owner_map]

/-- Arbitrary native interpretation retains the complete original auxiliary poststate, with only the private KEM representation mapped in the owner result. -/
theorem native_owner_run {Auxiliary : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (kem : K → K')
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K' X Response) (StateT Auxiliary m))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) (auxiliary : Auxiliary) :
    (fun result => ((result.1.1, PqxdhBeaconPhase1Publication.mapState id kem result.1.2), result.2)) <$>
      (simulateQ (handler ∘ₛ native kem) (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary =
      (simulateQ handler (PqxdhBeaconPhase2Publication.nativeOwner decode raw
        (PqxdhBeaconPhase1Publication.mapState id kem state))).run auxiliary := by
  rw [← native_owner_map kem decode raw state]
  simp only [simulateQ_map, StateT.run_map, QueryImpl.simulateQ_compose]

end BeaconcryptCore.Computational.PqxdhPhase2KemHandles

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.collect_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.collect_map

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.afterInputs_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.afterInputs_map

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.prepare_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.prepare_map

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.finish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.finish_map

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.full_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.full_pre

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.full_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.full_tail

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.owner_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.owner_map

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.native_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.native_tail

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.native_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.native_adapter

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.native_owner_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.native_owner_map

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemHandles.native_owner_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemHandles.native_owner_run
