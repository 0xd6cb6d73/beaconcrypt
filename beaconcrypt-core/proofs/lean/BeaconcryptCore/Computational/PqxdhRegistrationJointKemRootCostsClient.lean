import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCostsSkeleton
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpandCount
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills
import BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

/-!
# The random draws of the item 2 root clients (item 2, stage S8, clients)

This module bounds the coins of the root client of stage S2 (`PqxdhRegistrationJointKemRootExpand.rootClient`) and the random draws of the factored root client of stage S3b (`PqxdhRegistrationJointKemEntryFactor.entryClient`), for every oracle answer, by explicit bills derived from the source budget `certified` of theorem T5, `KemBound setup caps` and the runtime initialization bound `initBound`:

- the grouped client: every source request costs at most its weight `wSource` on the grouped interface (`groupedClient_cost`): a coin 1, a creation 64 (the identity creation's 32 and the prekey's 32), a bundle 32 (the one-time prekey), a raw accept `96 + encapsCost`, a build 64, a Beacon finish `decapsCost + 128` (its decapsulation, its root and its continuation's one commitment), a public HMAC and a hash 64, a reveal nothing, an identity or KEM read 1;
- the post-challenge phase of the skeleton (`postSkel_cost`): the Server's resumption 64 (`resume_cost`) plus the weighted source budget of the continuation suspended at the cut, which inherits every query bound of the source program (`PqxdhRegistrationJointKemRootExpand.sharedStart_inherit`);
- the prefix `sharedStart` (`sharedStart_total`): the challenger's key generation, the stopped-source prefix up to the selected raw accept (through the program equalities `PqxdhRegistrationJointKemRawChallenge.preRaw_source` and `PqxdhRegistrationJointKemRawOpaque.preRaw_opaque`, with the prechallenge bills `pre_uniform`, `pre_base` and `pre_decapsulations` of the raw-ordinal KEM adversary) and the challenger's encapsulation;
- `rootClient_coins` and `entryClient_cost`: the sum of the two.

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
open PqxdhRegistrationJointServiceCosts (Kind classify poolClass)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)

/-! ### The grouped Beacon finish -/

section Finish

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The Beacon preparation interface with the opaque handle: `decapsCost` per decapsulation, nothing otherwise. -/
def wPrep {I D K X Shared : Type} (caps : KemCaps) :
    (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared).Domain → ℕ
  | .decapsulate _ _ => caps.decapsCost
  | _ => 0

/-- The opaque-handle collector decapsulates at most once. -/
theorem collect_cost {I D K X Shared : Type} (caps : KemCaps) (identity : I) (prekey oneTime : D) (kem : K)
    (raw : Pqxdh.Bytes) :
    WBound (PqxdhBeaconPhase2Shared.collect (X := X) (Response := Response) (Shared := Shared) identity prekey oneTime
      kem raw) (wPrep caps) caps.decapsCost := by
  unfold PqxdhBeaconPhase2Shared.collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (rw [wBound_query_bind]; refine ⟨by simp [wPrep], ?_⟩)
    | (fail_if_no_progress simp only [Option.elim, OptionT.run_pure])
    | intro answer; cases answer

/-- The opaque-handle preparation decapsulates at most once. -/
theorem prepare_cost {I D K X Shared : Type} (caps : KemCaps) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    WBound (PqxdhBeaconPhase2Shared.prepare (X := X) (Response := Response) (Shared := Shared) control identity prekey
      oneTime kem raw) (wPrep caps) caps.decapsCost := by
  unfold PqxdhBeaconPhase2Shared.prepare
  refine wBound_mono (wBound_bind (a := caps.decapsCost) (b := 0) (collect_cost caps identity prekey oneTime kem raw)
    fun inputs _ => ?_) (by omega)
  rcases inputs with _ | inputs
  · exact wBound_pure _ _ _
  · unfold PqxdhBeaconPhase2Shared.afterInputs
    exact wBound_bind (a := 0) (b := 0) ((wBound_query _ _ _).mpr le_rfl) fun _ _ => wBound_pure _ _ _

/-- The grouped owner's interface: the preparation's weights, 128 for the grouped finish request. -/
def wOwner (caps : KemCaps) : (OwnerSpec Response).Domain → ℕ
  | .inl query => wPrep caps query
  | .inr _ => 128

theorem groupedOwner_cost (caps : KemCaps) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointBundle.Owner) :
    WBound (groupedOwner (Response := Response) raw state) (wOwner caps) (caps.decapsCost + 128) := by
  unfold groupedOwner
  split
  · refine wBound_bind ?_ fun prepared _ => ?_
    · exact wBound_simulate _ (wPrep caps) (wOwner caps) (fun query => (wBound_query _ _ _).mpr le_rfl)
        (prepare_cost caps _ _ _ _ _ raw)
    · rcases prepared with _ | prepared
      · exact wBound_pure _ _ _
      · exact wBound_bind (a := 128) (b := 0) ((wBound_query _ _ _).mpr le_rfl) fun _ _ => wBound_pure _ _ _
  · exact wBound_pure _ _ _

/-- Each callback of the grouped owner costs at most its weight on the grouped interface. -/
theorem groupedCompiler_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (caps : KemCaps) (query : (OwnerSpec Response).Domain) :
    WBound (groupedCompiler setup codec selected challenge query) (wG (KemSK := KemSK) caps) (wOwner caps query) := by
  rcases query with query | pending
  · cases query <;> simp only [groupedCompiler, PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation,
      simulateQ_pure, simulateQ_map, simulateQ_spec_query, groupedPoolLift]
    all_goals first
      | exact wBound_pure _ _ _
      | exact wBound_map _ ((wBound_query _ _ _).mpr (by simp [wG, wKind, classify, poolClass, wOwner, wPrep]))
  · exact (wBound_query _ _ _).mpr le_rfl

/-- A grouped Beacon finish costs at most its decapsulation and its grouped request. -/
theorem groupedFinish_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (caps : KemCaps) (address : Nat) (raw : Pqxdh.Bytes)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    WBound ((groupedFinish setup codec selected challenge address raw).run owners)
      (wG (KemSK := KemSK) (Response := Response) caps) (caps.decapsCost + 128) := by
  change WBound (match owners[address]? with
    | none => pure (none, owners)
    | some entry => _ : OracleComp (GSpec KemSK Response) _) _ _
  split
  · exact wBound_pure _ _ _
  · exact wBound_map _ (wBound_simulate _ (wOwner caps) _ (groupedCompiler_cost setup codec selected challenge caps)
      (groupedOwner_cost caps raw _))

end Finish

/-! ### The source requests -/

section Source

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

theorem kind_univ : (Finset.univ : Finset Kind) = {.identityCreate, .signing, .staticDh, .kemCreate, .decapsulate,
    .uniform, .other, .tail, .accept, .build, .hmac, .hash, .read} := by
  symm
  apply Finset.eq_univ_of_forall
  intro kind
  cases kind <;> simp

/-- The weight of a source request on the grouped interface. -/
def wSource (caps : KemCaps) : SourceKind → ℕ
  | .inl source => ![1, 64, 32, 96 + caps.encapsCost, 64, caps.decapsCost + 128, 64, 64, 0] source
  | .inr field => ![1, 1, 0, 0, 0] field

/-- Every source request other than a Beacon finish emits commands of total weight at most its own weight. -/
theorem command_sum (caps : KemCaps) (source : SourceKind) (other : source ≠ .inl 5) :
    ∑ kind, wKind caps kind * PqxdhRegistrationJointRevealCosts.cost kind source ≤ wSource caps source := by
  rw [kind_univ]
  rcases source with source | field
  · fin_cases source <;> simp_all [wKind, wSource, PqxdhRegistrationJointRevealCosts.cost,
      PqxdhRegistrationJointServiceCosts.cost, PqxdhRegistrationJointServiceCosts.createCap,
      PqxdhRegistrationJointServiceCosts.bundleCap, PqxdhRegistrationJointServiceCosts.finishCap]
  · fin_cases field <;> simp [wKind, wSource, PqxdhRegistrationJointRevealCosts.cost,
      PqxdhRegistrationJointRevealCosts.readCap]

/-- A source request answered by the source client costs at most the weighted sum of its command classes. -/
theorem liftGrouped_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (caps : KemCaps)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    WBound ((liftGrouped (Response := Response) (PqxdhRegistrationJointRevealSchedule.client setup codec query)).run
      owners) (wG caps) (∑ kind, wKind caps kind * PqxdhRegistrationJointRevealCosts.cost kind (sourceKind query)) := by
  change WBound (simulateQ groupedLift ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run owners))
    _ _
  refine wBound_simulate (groupedLift (KemSK := KemSK) (Response := Response)) (fun query => wKind caps (classify query))
    (wG caps) (fun query => (wBound_query _ _ _).mpr le_rfl) ?_
  exact wBound_kinds classify (wKind caps) _ fun kind =>
    PqxdhRegistrationJointRevealCosts.query_bound setup codec query owners kind

/-- Every source request costs at most its weight on the grouped interface. -/
theorem groupedClient_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (caps : KemCaps)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    WBound ((groupedClient setup codec selected challenge query).run owners) (wG (Response := Response) caps)
      (wSource caps (sourceKind query)) := by
  rcases query with (coin | request) | read
  · exact wBound_mono (liftGrouped_cost setup codec caps _ owners) (command_sum caps _ (by simp [sourceKind,
      PqxdhRegistrationSchedule.sourceKind]))
  · cases request with
    | finish address raw =>
        refine wBound_mono (groupedFinish_cost setup codec selected challenge caps address raw owners) (le_of_eq ?_)
        simp [wSource, sourceKind, PqxdhRegistrationSchedule.sourceKind]
    | _ => exact wBound_mono (liftGrouped_cost setup codec caps _ owners) (command_sum caps _ (by simp [sourceKind,
        PqxdhRegistrationSchedule.sourceKind]))
  · exact wBound_mono (liftGrouped_cost setup codec caps _ owners) (command_sum caps _ (by simp [sourceKind]))

/-- The weighted source budget in closed form. -/
def postBill (caps : KemCaps) (budget : SourceKind → ℕ) : ℕ :=
  64 + (budget (.inl 0) + 64 * budget (.inl 1) + 32 * budget (.inl 2) + (96 + caps.encapsCost) * budget (.inl 3) +
    64 * budget (.inl 4) + (caps.decapsCost + 128) * budget (.inl 5) + 64 * budget (.inl 6) + 64 * budget (.inl 7) +
    budget (.inr 0) + budget (.inr 1))

theorem source_sum (caps : KemCaps) (budget : SourceKind → ℕ) :
    64 + ∑ kind, wSource caps kind * budget kind = postBill caps budget := by
  simp only [postBill, Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.sum_univ_zero, wSource]
  simp
  ring

end Source

/-! ### The post-challenge phase -/

section Post

open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointAcceptCutTag (Tag)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext)
open PqxdhRegistrationJointKemRootExpand (Inherits)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R V : Type}

/-- The resumed client of the skeleton costs at most the Server's resumption and the weighted budget of the continuation. -/
theorem skelResume_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (game : GameState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat) (ciphertext : MlKem768Ciphertext)
    (services : Services V Response) (bills : ServiceBills services) (budget : SourceKind → ℕ)
    (inherits : ∀ reply kind, (next reply).IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = kind)
      (budget kind)) :
    WBound (skelResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed game owners
      next selected ciphertext services) (wEnc (V := V) caps) (64 + ∑ kind, wSource caps kind * budget kind) := by
  unfold skelResume
  refine wBound_bind (wBound_run _ (wResume caps) _ (fun query state => resumeImpl_cost caps setup.hmac game.sessions
    services query state) (resume_cost setup codec checks caps bounded identityIndex publicIdentity raw value ephemeral
      _ _ game consumed) _) fun answer _ => ?_
  refine wBound_run _ (wG caps) _ (fun query state => skelImpl_cost setup codec checks caps bounded identityIndex
    publicIdentity services bills query state) ?_ answer.2
  refine wBound_run _ (fun query => wSource caps (sourceKind (KemSK := KemSK) query)) _ (fun query current =>
    groupedClient_cost setup codec selected ciphertext caps query current) ?_ owners
  refine wBound_kinds sourceKind (wSource caps) budget fun kind => ?_
  unfold PqxdhRegistrationJointAcceptKemCut.tagged
  rw [isQueryBoundP_map_iff]
  exact inherits answer.1 kind

/-- The skeleton's post-challenge phase costs, in the skeleton's weight, at most the Server's resumption and the weighted budget of the continuation at the cut. -/
theorem postSkel_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (services : Services V Response)
    (bills : ServiceBills services) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (context : OpaqueContext Reader KemSK A X count) (budget : SourceKind → ℕ)
    (inherits : ∀ kind, Inherits (fun query => sourceKind (KemSK := KemSK) query = kind) (budget kind) context) :
    WBound (postSkel setup codec checks decision count selected services chosen challenge context) (wSkel (V := V))
      (64 + ∑ kind, wSource caps kind * budget kind) := by
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, next⟩),
    state, runtime⟩
  · trivial
  · trivial
  · trivial
  · simp only [postSkel]
    split
    · refine wBound_map _ (lower_cost setup caps bounded _ _ _ _ _ _ ?_ _)
      exact skelResume_cost setup codec checks caps bounded _ _ _ raw value ephemeral consumed native.2 owners next
        selected.val challenge services bills budget fun reply kind => inherits kind reply
    · trivial

end Post

/-! ### The prefix -/

section Prefix

open PqxdhRegistrationJointKemCommands (SourceSpec)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The prechallenge bill of the stopped-source prefix: the uniform allowance of the raw-ordinal KEM adversary's prechallenge phase, with its base queries and logical decapsulations expanded by `KemBound`. -/
def preBill (caps : KemCaps) (qInit : Nat) (supplied : Option Pqxdh.Bytes) (count : Nat) (budget : SourceKind → ℕ) :
    ℕ :=
  ((qInit + if supplied.isNone then 32 else 0) + (caps.keygenCost * count +
    PqxdhRegistrationJointKemPostBills.uniformCap caps (budget (.inl 1)) (budget (.inl 5))
      (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))) +
    caps.baseUniform * (caps.decapsBase * budget (.inl 5)) + caps.decapsCost * budget (.inl 5)

/-- The stopped-source prefix up to the selected raw accept draws at most `preBill`. -/
theorem sourcePreOpaque_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X)
    (budget : SourceKind → ℕ)
    (certified : ∀ source, work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    (PqxdhRegistrationJointKemRawOpaque.sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied
      decision work runtime count selected index chosen).IsTotalQueryBound (preBill caps qInit supplied count budget) := by
  have total := PqxdhPrivateRootGameBudgets.evalKem_uniform_bound setup.baseImpl setup.kem chosen.2 caps.baseUniform
    caps.decapsCost bounded.base (fun ciphertext => PqxdhServerAuthSourceCosts.ambient_uniform setup.baseImpl
      caps.baseUniform bounded.base _ caps.decapsUniform caps.decapsBase (bounded.decapsUniform _ _)
      (bounded.decapsBase _ _))
    (PqxdhRegistrationJointKemRawChallenge.preRaw setup codec checks ensureInit supplied decision work runtime count
      selected index chosen.1) _ _ _
    (PqxdhRegistrationJointKemRawBills.pre_uniform setup codec checks caps bounded ensureInit qInit initBound supplied
      decision work budget certified runtime count selected index chosen.1)
    (PqxdhRegistrationJointKemRawBills.pre_base setup codec checks caps bounded ensureInit supplied decision work
      budget certified runtime count selected index chosen.1)
    (PqxdhRegistrationJointKemRawBills.pre_decapsulations setup codec checks caps bounded ensureInit supplied decision
      work budget certified runtime count selected index chosen.1)
  rw [PqxdhRegistrationJointKemRawChallenge.preRaw_source, PqxdhRegistrationJointKemRawOpaque.preRaw_opaque,
    IsTotalQueryBound, isQueryBound_map_iff] at total
  exact total

/-- The prefix bill: the challenger's key generation, the stopped-source prefix and the challenger's encapsulation. -/
def prefixBill (caps : KemCaps) (qInit : Nat) (supplied : Option Pqxdh.Bytes) (count : Nat) (budget : SourceKind → ℕ) :
    ℕ :=
  caps.keygenCost + preBill caps qInit supplied count budget + caps.encapsCost

/-- G1's prefix of the KEM-ideal branch draws at most `prefixBill`. -/
theorem sharedStart_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X)
    (budget : SourceKind → ℕ)
    (certified : ∀ source, work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsTotalQueryBound (prefixBill caps qInit supplied count budget) := by
  unfold sharedStart prefixBill
  have encaps : ∀ key, (simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)).IsTotalQueryBound
      caps.encapsCost := fun key => PqxdhServerAuthSourceCosts.ambient_uniform setup.baseImpl caps.baseUniform
    bounded.base _ caps.encapsUniform caps.encapsBase (bounded.encapsUniform key) (bounded.encapsBase key)
  refine (isTotalQueryBound_bind (n₂ := preBill caps qInit supplied count budget + (caps.encapsCost + 0))
    (PqxdhServerAuthSourceCosts.keygen_uniform setup caps bounded) fun chosen => ?_).mono (by omega)
  refine isTotalQueryBound_bind (sourcePreOpaque_total setup codec checks caps bounded ensureInit qInit initBound
    supplied decision work budget certified runtime count selected index chosen) fun context => ?_
  refine isTotalQueryBound_bind (encaps chosen.1) fun encapsulated => ?_
  trivial

end Prefix

/-! ### The root clients -/

section Clients

open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemEntryFactor (EntrySpec)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The coin bill of the root clients: the prefix and the post-challenge phase. -/
def rootBill (caps : KemCaps) (qInit : Nat) (supplied : Option Pqxdh.Bytes) (count : Nat) (budget : SourceKind → ℕ) :
    ℕ :=
  prefixBill caps qInit supplied count budget + postBill caps budget

/-- Stage S8, the coins of the root client of stage S2: at most `rootBill` for every oracle answer. -/
theorem rootClient_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X)
    (budget : SourceKind → ℕ)
    (certified : ∀ source, work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (PqxdhRegistrationJointKemRootExpand.rootClient (Reader := Reader) setup codec checks ensureInit supplied decision
      work runtime count selected index).IsQueryBoundP PqxdhCorrelatedExpandQueryBounds.IsCoin
      (rootBill caps qInit supplied count budget) := by
  unfold PqxdhRegistrationJointKemRootExpand.rootClient PqxdhRegistrationJointKemRootExpand.internalize rootBill
  refine isQueryBoundP_bind (PqxdhCorrelatedExpandQueryBounds.rootCoins_uniform _ _ (sharedStart_total setup codec
    checks caps bounded ensureInit qInit initBound supplied decision work budget certified runtime count selected index))
    fun start reached => ?_
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine isQueryBoundP_of_wBound _ (w := wRoot) (fun query coin => ?_) ?_
  · rcases query with _ | _
    · exact le_rfl
    · exact coin.elim
  · refine wBound_run _ wSkel wRoot (fun query cache => publicLocal_cost query cache) ?_ start.1
    rw [← source_sum]
    refine postSkel_cost setup codec checks caps bounded decision count selected _
      (nativeServices_bills setup codec checks) start.2.1 start.2.2.2 start.2.2.1 budget fun kind => ?_
    exact PqxdhRegistrationJointKemRootExpand.sharedStart_inherit (fun query => sourceKind query = kind) setup codec
      checks ensureInit supplied decision work runtime count selected index (budget kind) (certified kind) start
      (OracleComp.mem_support_of_mem_support_liftComp _ _ start reached)

/-- The factored root client's interface: one per coin, `r` per hidden read. -/
def wEntry {V : Type} (r : ℕ) : (EntrySpec V).Domain → ℕ
  | .inl _ => 1
  | .inr _ => r

theorem publicLocalV_cost {V : Type} (query : (SkelSpec V).Domain) (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache) :
    WBound ((PqxdhRegistrationJointKemEntryFactor.publicLocalV V query).run cache) (wEntry 0) (wSkel query) := by
  rcases query with coin | (message | point)
  · change WBound ((fun reply => (reply, cache)) <$>
      (liftM ((EntrySpec V).query (.inl coin)) : OracleComp (EntrySpec V) _)) _ _
    exact wBound_map _ ((wBound_query _ _ _).mpr le_rfl)
  · change WBound ((fun reply => (reply, cache)) <$>
      (liftM ((EntrySpec V).query (.inr message)) : OracleComp (EntrySpec V) _)) _ _
    exact wBound_map _ ((wBound_query _ _ _).mpr le_rfl)
  · change WBound (OracleComp.liftComp ((PqxdhSecretInputKdf.HmacOracle.randomOracle point).run cache) (EntrySpec V))
      _ _
    exact wBound_liftComp_inl (fun _ => 1) _ (fun _ => rfl)
      (wBound_of_total (PqxdhServerAuthNativeUniformCosts.extract_table_uniform point cache))

/-- Stage S8, the coins of the factored root client of stage S3b: at most `rootBill` coins for every oracle answer. -/
theorem entryClient_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X)
    (budget : SourceKind → ℕ)
    (certified : ∀ source, work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    WBound (PqxdhRegistrationJointKemEntryFactor.entryClient (Reader := Reader) setup codec checks ensureInit supplied
      decision work runtime count selected index) (wEntry 0) (rootBill caps qInit supplied count budget) := by
  unfold PqxdhRegistrationJointKemEntryFactor.entryClient PqxdhRegistrationJointKemEntryFactor.internalizeV rootBill
  refine wBound_bind (wBound_liftComp_inl (fun _ => 1) _ (fun _ => rfl) (wBound_of_total (sharedStart_total setup
    codec checks caps bounded ensureInit qInit initBound supplied decision work budget certified runtime count selected
    index))) fun start reached => ?_
  rw [StateT.run'_eq]
  refine wBound_map _ (wBound_run _ wSkel (wEntry 0) (fun query cache => publicLocalV_cost query cache) ?_ start.1)
  rw [← source_sum]
  refine postSkel_cost setup codec checks caps bounded decision count selected _
    (factoredServices_bills setup codec checks) start.2.1 start.2.2.2 start.2.2.1 budget fun kind => ?_
  exact PqxdhRegistrationJointKemRootExpand.sharedStart_inherit (fun query => sourceKind query = kind) setup codec
    checks ensureInit supplied decision work runtime count selected index (budget kind) (certified kind) start
    (OracleComp.mem_support_of_mem_support_liftComp _ _ start reached)

end Clients

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.collect_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.collect_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.prepare_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.prepare_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.groupedOwner_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.groupedOwner_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.groupedCompiler_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.groupedCompiler_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.groupedFinish_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.groupedFinish_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.kind_univ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.kind_univ

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.command_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.command_sum

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.liftGrouped_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.liftGrouped_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.groupedClient_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.groupedClient_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.source_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.source_sum

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.skelResume_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.skelResume_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.postSkel_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.postSkel_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.sourcePreOpaque_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.sourcePreOpaque_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.sharedStart_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.sharedStart_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.rootClient_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.rootClient_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.publicLocalV_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.publicLocalV_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.entryClient_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.entryClient_coins
