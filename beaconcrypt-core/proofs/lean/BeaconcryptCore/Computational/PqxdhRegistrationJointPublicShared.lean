-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointInitializedAccept

/-! Public HMAC and the complete shared Server callbacks use no generated identity seed outside the private indexed accept interpreter. This retains the existing restricted Extract-ROM interpretation and complete native state; it does not assert a cryptographic replacement. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhSecretInputKdf
open PqxdhRegistrationJointFinish (State onNative)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Exact public branch: only admitted zero-salt/192-byte inputs access the existing shared table; every other evaluation stays real. No identity or scalar parameter is present. -/
noncomputable def publicFamily (hmac : HmacSha512) (key : HmacBlock) (message : Pqxdh.Bytes) :
    StateT PqxdhJointDhExtractFamily.State ProbComp HmacBlock := fun state =>
  if key = zeroSalt ∧ message.length = 192 then do
    let result ← (HmacOracle.randomOracle message).run state.cache
    pure (result.1, ⟨state.history ++ [.publicHmac key message result.1], result.2⟩)
  else
    let block := hmac.eval key message
    pure (block, { state with history := state.history ++ [.publicHmac key message block] })

/-- The complete family branch is definitionally independent of identity and scalar secrets, not merely equal in its reply marginal. -/
theorem family_source (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (key : HmacBlock) (message : Pqxdh.Bytes) :
    publicFamily setup.hmac key message =
      PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar (.inr (.publicHmac key message)) := by
  rfl

/-- The same public touch instrumentation, family cache and entire native state are retained without a private seed argument. -/
noncomputable def hmac (setup : Setup baseSpec KemSK) (key : HmacBlock) (message : Pqxdh.Bytes) :
    NativeGame KemSK HmacBlock := do
  if key = zeroSalt ∧ message.length = 192 then nativeTouch (.adversary message)
  fun state => (fun result => (result.1, (result.2, state.2))) <$>
    (publicFamily setup.hmac key message).run state.1

/-- Equality is of full state transformers, including the touch event, cache and primitive history for every incoming native state. -/
theorem hmac_source (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (key : HmacBlock) (message : Pqxdh.Bytes) :
    hmac setup key message = nativeHmac setup seed scalar key message := by
  funext state
  change (hmac setup key message).run state = (nativeHmac setup seed scalar key message).run state
  by_cases slice : key = zeroSalt ∧ message.length = 192
  all_goals simp only [hmac, nativeHmac, slice, and_self, ite_true, ite_false, StateT.run_bind]
  all_goals simp only [StateT.run, PqxdhServerRelatedRootConsumer.familyImpl,
    (PqxdhExtractRomFamily.rom_forward setup.hmac setup.joint setup.dh seed scalar).2.2,
    family_source setup seed scalar]
  all_goals first | rfl | rw [slice.1]
  rfl

/-- The complete seedless family branch charges the possible 64-byte table draw; off-domain HMAC remains deterministic native work. -/
theorem family_uniform (hmac : HmacSha512) (key : HmacBlock) (message : Pqxdh.Bytes)
    (state : PqxdhJointDhExtractFamily.State) :
    ((publicFamily hmac key message).run state).IsTotalQueryBound 64 := by
  simp only [publicFamily, StateT.run]
  split
  · simpa only [bind_pure_comp, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
      PqxdhServerAuthEntryFactor.extract_table_uniform message state.cache
  · trivial

/-- Public touch instrumentation introduces no extra uniform draw; the existing complete public-HMAC allowance remains 64. -/
theorem hmac_uniform (setup : Setup baseSpec KemSK) (key : HmacBlock) (message : Pqxdh.Bytes)
    (state : NativeState KemSK) : ((hmac setup key message).run state).IsTotalQueryBound 64 := by
  by_cases slice : key = zeroSalt ∧ message.length = 192
  all_goals simp only [hmac, slice, and_self, ite_true, ite_false, StateT.run_bind]
  all_goals simp only [StateT.run, nativeTouch, localState, pure_bind, IsTotalQueryBound, isQueryBound_map_iff]
  all_goals exact family_uniform setup.hmac _ message state.1

/-- The entire shared interface is implemented without a generated seed parameter. Acceptance uses the retained identity handle; build, public hashing and current Server-kernel reveals keep their original native code. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) :
    QueryImpl PqxdhRegistrationJointServiceSchedule.SharedSpec (StateT (State KemSK) ProbComp)
  | .accept raw => PqxdhRegistrationJointServerAccept.client setup codec checks identityIndex publicIdentity raw
  | .build index payload => onNative (nativeBuild setup codec checks index payload)
  | .hmac key message => onNative (hmac setup key message)
  | .hash bytes => onNative (nativeHash bytes)
  | .reveal keyId => onNative (localState fun state => (revealKernel keyId state, state))

/-- Source annotations change only the private acceptance trace; all other callbacks retain their literal native implementation. -/
noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) :
    QueryImpl PqxdhRegistrationJointServiceSchedule.SharedSpec (StateT (State KemSK) ProbComp)
  | .accept raw => PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw
  | .build index payload => onNative (nativeBuild setup codec checks index payload)
  | .hmac key message => onNative (nativeHmac setup seed PqxdhRegistrationSchedule.observationScalar key message)
  | .hash bytes => onNative (nativeHash bytes)
  | .reveal keyId => onNative (localState fun state => (revealKernel keyId state, state))

/-- Exact query simulation preserves the reply and complete private/native poststate on every accepting or rejecting branch. -/
theorem query_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : PqxdhRegistrationJointServiceSchedule.SharedSpec.Domain)
    (state : State KemSK) (owned : state.1.1.seeds[identityIndex]? = some seed) :
    (client setup codec checks identityIndex (setup.joint.publicKeys seed) query).run state =
      (source setup codec checks seed identityIndex query).run state := by
  cases query
  case accept raw => exact PqxdhRegistrationJointServerAccept.client_source setup codec checks seed identityIndex raw state owned
  all_goals simp only [client, source, hmac_source setup seed PqxdhRegistrationSchedule.observationScalar]

/-- Forgetting only private services recovers every literal native shared callback, including the complete response build/publication and permitted Server-kernel reveal. -/
theorem source_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : PqxdhRegistrationJointServiceSchedule.SharedSpec.Domain)
    (state : State KemSK) :
    (fun result => (result.1, result.2.2)) <$> (source setup codec checks seed identityIndex query).run state =
      (PqxdhRegistrationJointServiceSchedule.shared setup codec checks seed query).run state.2 := by
  cases query
  case accept raw => exact PqxdhRegistrationJointServerAccept.source_native setup codec checks seed identityIndex raw state
  all_goals simp only [source, onNative, PqxdhRegistrationJointServiceSchedule.shared, StateT.run, Functor.map_map, id_map']

/-- Every supported native callback retains the complete private pool, even when the public reply reports failure. -/
theorem native_slots (work : NativeGame KemSK Result) (state : State KemSK)
    (result : Result × State KemSK) (supported : result ∈ support ((onNative work).run state)) :
    result.2.1 = state.1 := by
  obtain ⟨reached, _, rfl⟩ : ∃ reached ∈ support (work.run state.2),
      (reached.1, (state.1, reached.2)) = result := by
    simpa only [onNative, StateT.run, support_map, Set.mem_image] using supported
  rfl

/-- All shared-source callbacks preserve exact private slots while retaining changed histories, cache and protocol state. -/
theorem source_slots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : PqxdhRegistrationJointServiceSchedule.SharedSpec.Domain)
    (state : State KemSK) (result : PqxdhRegistrationJointServiceSchedule.SharedSpec.Range query × State KemSK)
    (supported : result ∈ support ((source setup codec checks seed identityIndex query).run state)) :
    result.2.1.1.seeds = state.1.1.seeds ∧ result.2.1.2.keys = state.1.2.keys := by
  cases query
  case accept raw => exact PqxdhRegistrationJointServerAccept.source_slots setup codec checks seed identityIndex raw state result supported
  all_goals simpa only [native_slots _ state result supported] using (And.intro rfl rfl : state.1.1.seeds = state.1.1.seeds ∧ state.1.2.keys = state.1.2.keys)

end BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.family_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.family_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.hmac_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.hmac_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.family_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.family_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.hmac_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.hmac_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.source_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.source_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.native_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.native_slots

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.source_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared.source_slots
