-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenBeaconResult
import BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthCompiler
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth

/-! Every completed actual candidate-provider constructor either fails before KEM birth with the original roster, or creates the next genuine indexed pair and appends exactly the owner retaining that handle and key. Optional source aborts are kept as aborts of the whole client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenCreate
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemOpenBirth (borns)
open RegistrationNativeKemOpenFrame (lower)
open PqxdhKemIndCca
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def Transition (pairs : List (MlKem768PublicKey × KemSK)) (before after : State n mlSource KemSK) : Prop :=
  (borns after = borns before ∧ after.1.1.beacons = before.1.1.beacons) ∨
    ∃ pair owner, pairs[borns before]? = some pair ∧ owner.kemHandle = borns before ∧ owner.kemPublic = pair.1 ∧
      borns after = borns before + 1 ∧ after.1.1.beacons = before.1.1.beacons ++ [owner]

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- The actual native constructor derives next-slot birth and owner append together, including every failed pre-birth gate. -/
theorem create_transition (chosen : Bool) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before after : State n mlSource KemSK) (value : RustM (Option Nat))
    (supported : (some value, after) ∈ support
      (((simulateQ provider (simulateQ (lower chosen) (RegistrationNativeKemBeaconCompiler.beacon
        (RegistrationNativeBeaconFrontend.create setup mlSource edPin mlPin keyId)))).run).run before)) :
    Transition pairs before after := by
  obtain ⟨result, reached, called, _sameValue, ownersEq, privateEq, _phaseEq⟩ :=
    RegistrationNativeKemOpenBeaconResult.beacon_callback setup checks wire route representation created credential
      selected pairs publicKey real chosen (RegistrationNativeBeaconFrontend.create setup mlSource edPin mlPin keyId)
        before after value supported
  let implementation := (provider ∘ₛ lower chosen) ∘ₛ RegistrationNativeKemBeaconCompiler.trusted
  let first : State n mlSource KemSK := ((RegistrationNativeKemServerState.mask before.1.1, before.1.2), before.2)
  rw [RegistrationNativeBeaconBirth.create_program] at called
  simp only [simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨⟨prepared, middle⟩, preparedSupport, tail⟩ := called
  cases prepared with
  | none =>
      simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at tail
  | some prepared =>
      have counter := RegistrationNativeKemOpenBirthCompiler.trusted_keeps setup checks wire route representation created credential
        selected pairs publicKey real chosen _
        (RegistrationNativeKemBeaconFootprint.prepare_zero .create edPin mlPin keyId before.1.1.beacons
          (RegistrationWorldAgreementCompiler.erase before.1.1.server.world)) first middle prepared preparedSupport
      change borns middle = borns before at counter
      have original := RegistrationNativeOptionalSupport.completed_support implementation _ prepared first middle preparedSupport
      have prepareOwners := RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId before.1.1.beacons _ prepared original
      have noBirth (tag : RustM (Option Nat))
          (terminal : (some result, reached) ∈ support
            (pure (some ((tag, prepared.1.2), prepared.2), middle) : ProbComp _)) : Transition pairs before after := by
        simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at terminal
        obtain ⟨rfl, rfl⟩ := terminal
        refine Or.inl ⟨?_, ownersEq.trans prepareOwners⟩
        have finalCounter := congrArg PqxdhDynamicKemRouter.State.created privateEq
        exact finalCounter.trans counter
      cases actual : prepared.1.1 with
      | fail error =>
          simp only [actual, simulateQ_pure, OptionT.run_pure, StateT.run_pure, Option.elim_some] at tail
          exact noBirth (.fail error) tail
      | div =>
          simp only [actual, simulateQ_pure, OptionT.run_pure, StateT.run_pure, Option.elim_some] at tail
          exact noBirth .div tail
      | ok reply =>
          cases reply with
          | none =>
              simp only [actual, simulateQ_pure, OptionT.run_pure, StateT.run_pure, Option.elim_some] at tail
              exact noBirth (.ok none) tail
          | some ready =>
              simp only [actual, Option.elim_some] at tail
              rw [RegistrationNativeBeaconBirth.append_program] at tail
              simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
                StateT.run_bind, mem_support_bind_iff] at tail
              obtain ⟨⟨born, bornState⟩, generated, allocated⟩ := tail
              cases born with
              | none =>
                  simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
                    reduceCtorEq, false_and] at allocated
              | some born =>
                  have birth : (some born, bornState) ∈ support (((provider (.inr (.inl .create))).run).run middle) := by
                    simpa only [QueryImpl.apply_compose, RegistrationNativeKemBeaconCompiler.trusted, lower,
                      RegistrationNativeKemServerInterface.lift, RegistrationNativeKemFrontendInterface.lift,
                      RegistrationNativeKemRouting.route, simulateQ_spec_query] using generated
                  obtain ⟨pair, pairAt, birthReply, bornCounter, _birthContext, _birthPhase⟩ :=
                    RegistrationNativeKemOpenBirth.create_receipt setup checks wire route representation created credential
                      selected pairs publicKey real middle bornState born birth
                  simp only [Option.elim_some, StateT.run_bind, mem_support_bind_iff] at allocated
                  obtain ⟨⟨worldOwner, final⟩, allocation, terminal⟩ := allocated
                  cases worldOwner with
                  | none =>
                      simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
                        reduceCtorEq, false_and] at terminal
                  | some worldOwner =>
                      have lastCounter := RegistrationNativeKemOpenBirthCompiler.trusted_keeps setup checks wire route representation created credential
                        selected pairs publicKey real chosen
                        ((RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inl (.inr (.appendOwner keyId edPin .fresh))) :
                          OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Nat)
                        (by simp [RegistrationNativeKemBeaconFootprint.counted, isQueryBoundP_query_iff])
                        bornState final worldOwner (by simpa only [simulateQ_spec_query] using allocation)
                      simp only [Option.elim_some, simulateQ_pure, OptionT.run_pure, StateT.run_pure,
                        mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at terminal
                      obtain ⟨rfl, rfl⟩ := terminal
                      let owner := RegistrationNativeBeaconBirth.owner setup mlSource ready.pin ready.credentials ready.identity ready.prekey born worldOwner
                      refine Or.inr ⟨pair, owner, ?_, ?_, ?_, ?_, ?_⟩
                      · simpa only [counter] using pairAt
                      · change born.1 = borns before
                        rw [birthReply]
                        exact counter
                      · change born.2 = pair.1
                        exact congrArg Prod.snd birthReply
                      · have finalCounter := congrArg PqxdhDynamicKemRouter.State.created privateEq
                        change borns after = borns reached at finalCounter
                        omega
                      · simpa only [prepareOwners] using ownersEq

end BeaconcryptCore.Computational.RegistrationNativeKemOpenCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenCreate.create_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenCreate.create_transition
