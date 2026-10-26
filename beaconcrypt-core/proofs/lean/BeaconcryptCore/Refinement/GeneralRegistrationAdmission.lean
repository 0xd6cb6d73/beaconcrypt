import BeaconcryptCore.Refinement.RatchetReceiveStructural

/-!
# Complete empty-cache raw receive admission

The raw receive capability uses one case for each admitted initial sequence, 1 through 51. Production registration completion applies a separate sequence-one check after successful opening, so targets 2 through 51 do not complete registration. Its prefix recursion derives the target separately from the skipped cache, with newest-first symbolic entries. This file relates that recursion to the existing arbitrary-interpreter extracted receive execution and preserves its complete published state for subsequent operations. Cryptographic authentication, the raw-byte decoder, and the nonempty eight-byte-prefix parser remain separate interfaces.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

/-- The three fields returned by the generated `general_prefix_n` symbolic macro. -/
structure RegistrationPrefix (Chain Material : Type) where
  target : Material
  next : Chain
  skipped : List (Nat × Material)

/-- Index `n` denotes target sequence `n + 1`, with exactly `n` skipped keys. -/
def registrationPrefix {Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (chain : Chain) :
    Nat → RegistrationPrefix Chain Material
  | 0 => ⟨cr.kdfMsg chain, cr.kdfChain chain, []⟩
  | n + 1 =>
    let previous := registrationPrefix cr chain n
    ⟨cr.kdfMsg previous.next, cr.kdfChain previous.next,
      (n + 1, previous.target) :: previous.skipped⟩

/-- Every generated prefix has the exact evolving chain, target, and newest-first cache. -/
theorem registrationPrefix_exact {Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (chain : Chain) (n : Nat) :
    registrationPrefix cr chain n =
      ⟨Ratchet.msgKeyAt cr chain n, Ratchet.chainAt cr chain (n + 1),
        ((List.range n).map (fun j => (j + 1, Ratchet.msgKeyAt cr chain j))).reverse⟩ := by
  induction n with
  | zero => simp [registrationPrefix, Ratchet.msgKeyAt, Ratchet.chainAt]
  | succ n ih =>
    simp [registrationPrefix, ih, Ratchet.msgKeyAt, Ratchet.chainAt,
      Function.iterate_succ_apply', List.range_succ]

/-- Every cache member has a positive earlier literal sequence, for arbitrary opaque chains and material functions. -/
theorem registrationPrefix_member_sequence {Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (chain : Chain) (n sequence : Nat)
    (material : Material)
    (hmem : (sequence, material) ∈ (registrationPrefix cr chain n).skipped) :
    1 ≤ sequence ∧ sequence ≤ n := by
  simp only [registrationPrefix_exact, List.mem_reverse, List.mem_map, List.mem_range,
    Prod.mk.injEq] at hmem
  omega

/-- Every generated ordered cache-hit case preserves a member's unchanged sequence tag. -/
theorem registrationPrefix_selected_case_sequence {Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (chain : Chain) (n sequence : Nat)
    (material : Material) (before tail : List (Nat × Material))
    (hcase : (registrationPrefix cr chain n).skipped = before ++ (sequence, material) :: tail) :
    1 ≤ sequence ∧ sequence ≤ n := by
  apply registrationPrefix_member_sequence cr chain n sequence material
  simp [hcase]

/-- The private sender token retains the complete public/session context and a proof-only prefix history. -/
structure RegistrationSendToken (Context Chain Material : Type) where
  context : Context
  sequence : Nat
  chain : Chain
  prior : List (Nat × Material)

/-- The next successful send preserves its context and advances exactly one source chain/sequence step. -/
def registrationSendAdvance {Context Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT)
    (token : RegistrationSendToken Context Chain Material) :
    RegistrationSendToken Context Chain Material :=
  ⟨token.context, token.sequence + 1, cr.kdfChain token.chain,
    (token.sequence, cr.kdfMsg token.chain) :: token.prior⟩

/-- Index `n` denotes the source token immediately before record `n + 1`. -/
def registrationSendTokenAt {Context Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (context : Context)
    (initial : Chain) (n : Nat) : RegistrationSendToken Context Chain Material :=
  ⟨context, n + 1, Ratchet.chainAt cr initial n,
    ((List.range n).map (fun j => (j + 1, Ratchet.msgKeyAt cr initial j))).reverse⟩

/-- Every worker step preserves exact source indices and the entire retained context. -/
theorem registrationSendToken_advance {Context Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (context : Context)
    (initial : Chain) (n : Nat) :
    registrationSendAdvance cr (registrationSendTokenAt cr context initial n) =
      registrationSendTokenAt cr context initial (n + 1) := by
  simp [registrationSendAdvance, registrationSendTokenAt, Ratchet.chainAt,
    Ratchet.msgKeyAt, Function.iterate_succ_apply', List.range_succ]

/-- The worker's origin event carries the same target/next/cache tuple as initial receive. -/
theorem registrationSendToken_plan {Context Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (context : Context)
    (initial : Chain) (n : Nat) :
    let token := registrationSendTokenAt cr context initial n
    (⟨cr.kdfMsg token.chain, cr.kdfChain token.chain, token.prior⟩ :
      RegistrationPrefix Chain Material) = registrationPrefix cr initial n := by
  simp [registrationSendTokenAt, registrationPrefix_exact, Ratchet.msgKeyAt,
    Ratchet.chainAt, Function.iterate_succ_apply']

/-- The sole token installed after the first publication is the exact record-two token. -/
theorem registrationSendToken_after_first {Context Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (context : Context) (initial : Chain) :
    (⟨context, 2, cr.kdfChain initial, [(1, cr.kdfMsg initial)]⟩ :
      RegistrationSendToken Context Chain Material) =
      registrationSendTokenAt cr context initial 1 := by
  rfl

/-- The publicly sufficient state after a next-chain disclosure; proof history is absent. -/
def registrationSendPublicState {Context Chain Material : Type}
    (token : RegistrationSendToken Context Chain Material) : Ratchet.SendState Chain :=
  ⟨token.chain, token.sequence⟩

/-- The worker emits the existing seal with the complete public context at its actual sequence. -/
def registrationSendStep {Context Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (associatedData : Context → Nat → AD)
    (token : RegistrationSendToken Context Chain Material) (plaintext : PT) :
    Ratchet.Msg CT × RegistrationSendToken Context Chain Material :=
  ((Ratchet.sendStep cr (registrationSendPublicState token)
    (associatedData token.context token.sequence) plaintext).1, registrationSendAdvance cr token)

/-- Adaptive requests and observations can retain the complete scheduler, tape and transcript. -/
def registrationSendObservedRun {Context Chain Material AD PT CT Environment : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (associatedData : Context → Nat → AD)
    (request : Environment → Option (PT × Environment))
    (observe : Environment → Ratchet.Msg CT → Environment) :
    Nat → Environment → RegistrationSendToken Context Chain Material →
      Environment × RegistrationSendToken Context Chain Material
  | 0, env, token => (env, token)
  | fuel + 1, env, token =>
    match request env with
    | none => (env, token)
    | some (plaintext, nextEnv) =>
      let emitted := registrationSendStep cr associatedData token plaintext
      registrationSendObservedRun cr associatedData request observe fuel
        (observe nextEnv emitted.1) emitted.2

/-- A simulator with the disclosed state computes the same public KDF and seal operations. -/
def registrationSendPublicRun {Chain Material AD PT CT Environment : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (associatedData : Nat → AD)
    (request : Environment → Option (PT × Environment))
    (observe : Environment → Ratchet.Msg CT → Environment) :
    Nat → Environment → Ratchet.SendState Chain → Environment × Ratchet.SendState Chain
  | 0, env, state => (env, state)
  | fuel + 1, env, state =>
    match request env with
    | none => (env, state)
    | some (plaintext, nextEnv) =>
      let emitted := Ratchet.sendStep cr state (associatedData state.n) plaintext
      registrationSendPublicRun cr associatedData request observe fuel
        (observe nextEnv emitted.1) emitted.2

/-- Exact adaptive suffix simulation from the actual disclosed next chain, for every finite fuel. -/
theorem registrationSendObservedRun_public {Context Chain Material AD PT CT Environment : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (associatedData : Context → Nat → AD)
    (request : Environment → Option (PT × Environment))
    (observe : Environment → Ratchet.Msg CT → Environment)
    (fuel : Nat) (env : Environment) (token : RegistrationSendToken Context Chain Material) :
    let actual := registrationSendObservedRun cr associatedData request observe fuel env token
    (actual.1, registrationSendPublicState actual.2) =
      registrationSendPublicRun cr (associatedData token.context) request observe fuel env
        (registrationSendPublicState token) := by
  induction fuel generalizing env token with
  | zero => rfl
  | succ fuel ih =>
    cases hrequest : request env with
    | none => simp [registrationSendObservedRun, registrationSendPublicRun, hrequest]
    | some chosen =>
      simpa only [registrationSendObservedRun, registrationSendPublicRun, hrequest,
        registrationSendStep, registrationSendAdvance, registrationSendPublicState,
        Ratchet.sendStep] using ih
          (observe chosen.2 (registrationSendStep cr associatedData token chosen.1).1)
          (registrationSendAdvance cr token)

/-- Later output indices cannot equal a retained pre-disclosure target; source executions stop before overflow. -/
theorem registrationSendAfterCutoff_index {Chain Material AD PT CT : Type}
    (cr : Ratchet.Crypto Chain Material AD PT CT) (state : Ratchet.SendState Chain)
    (associatedData : Nat → AD) (plaintext : Nat → PT) (cutoff i : Nat)
    (hnext : state.n = cutoff + 1) :
    cutoff < (Ratchet.sentMsg cr state associatedData plaintext i).idx := by
  simp only [Ratchet.sentMsg_eq, hnext]
  omega

/-- Source last-slot swap removal in the newest-first symbolic list. -/
def registrationCacheSwap {α : Type} (cache : List α) (index : Nat) : List α :=
  match cache with
  | [] => []
  | last :: tail => if index = 0 then tail else tail.set (index - 1) last

/-- Every ordered generated destructor case moves the newest entry into the consumed position. -/
theorem registrationCacheSwap_case {α : Type} (last target : α) (before tail : List α) :
    registrationCacheSwap (last :: (before ++ target :: tail)) (before.length + 1) =
      before ++ last :: tail := by
  simp [registrationCacheSwap]

/-- Consuming any live symbolic slot frees exactly one position. -/
theorem registrationCacheSwap_length {α : Type} (cache : List α) (index : Nat) :
    (registrationCacheSwap cache index).length = cache.length - 1 := by
  cases cache with
  | nil => rfl
  | cons last tail => simp only [registrationCacheSwap]; split <;> simp

/-- The generated ordered cases have the exact source swap lookup at every remaining position. -/
theorem registrationCacheSwap_lookup {α : Type} (cache : List α) (index j : Nat)
    (hj : j < cache.length - 1) :
    (registrationCacheSwap cache index)[j]? =
      if index ≠ 0 ∧ j = index - 1 then cache[0]? else cache[j + 1]? := by
  cases cache with
  | nil => simp at hj
  | cons last tail =>
    simp only [List.length_cons, Nat.add_sub_cancel] at hj
    by_cases hindex : index = 0
    · simp [registrationCacheSwap, hindex, hj]
    · by_cases hji : j = index - 1
      · subst j
        simp [registrationCacheSwap, hindex, hj]
      · simp [registrationCacheSwap, hindex, hji, Ne.symm hji, hj]

/-- Every symbolic cache entry is the exact corresponding active source material slot. -/
def NewestCacheRepresents {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (cache : List (Nat × Material)) : Prop :=
  cache.length = state.control.receive_cache.len.val ∧
    ∀ j, j < cache.length →
      cache[j]? = _root_.Option.map
        (fun cached : ratchet.refined.CachedReceiveKey Material => (cached.sequence.val, cached.material))
        state.receive_slots.val[cache.length - 1 - j]!

/-- Valid extracted caches make the generated ordered lookup's matching sequence position unique. -/
theorem NewestCacheRepresents.sequence_unique {SendChain ReceiveChain Material : Type}
    {state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material}
    {cache : List (Nat × Material)} (h : NewestCacheRepresents state cache)
    (hvalid : ratchet.refined.ValidRefined state)
    (i j sequence : Nat) (leftMaterial rightMaterial : Material)
    (hi : i < cache.length) (hj : j < cache.length)
    (hleft : cache[i]? = some (sequence, leftMaterial))
    (hright : cache[j]? = some (sequence, rightMaterial)) : i = j := by
  obtain ⟨left, hleftSlot, hleftTag⟩ := hvalid.slots.live hvalid.control.capacity
    (cache.length - 1 - i) (by have := h.1; omega)
  obtain ⟨right, hrightSlot, hrightTag⟩ := hvalid.slots.live hvalid.control.capacity
    (cache.length - 1 - j) (by have := h.1; omega)
  have hleftValue : left.sequence.val = sequence := by
    have heq := congrArg (_root_.Option.map Prod.fst) ((h.2 i hi).symm.trans hleft)
    simpa only [hleftSlot, core.option.Option.Some, _root_.Option.map_some,
      _root_.Option.some.injEq] using heq
  have hrightValue : right.sequence.val = sequence := by
    have heq := congrArg (_root_.Option.map Prod.fst) ((h.2 j hj).symm.trans hright)
    simpa only [hrightSlot, core.option.Option.Some, _root_.Option.map_some,
      _root_.Option.some.injEq] using heq
  have hslots := hvalid.control.slot_unique (cache.length - 1 - i) (cache.length - 1 - j)
    (by have := h.1; omega) (by have := h.1; omega)
    (hleftTag.symm.trans ((UScalar.eq_of_val_eq (hleftValue.trans hrightValue.symm)).trans hrightTag))
  omega

/-- Every source-prepared cached key selects one of the fifty generated symbolic destructor positions with its exact sequence and material. -/
theorem cached_symbolic_position_is_exhaustive {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (cache : List (Nat × Material)) (sequence : Std.U64)
    (prepared : ratchet.refined.PreparedCachedReceive)
    (hvalid : ratchet.refined.ValidRefined state)
    (hprepared : ratchet.refined.CachedPreparationFacts state sequence prepared)
    (hcache : NewestCacheRepresents state cache) :
    ∃ index : Fin 50, ∃ material,
      index.val = cache.length - 1 - prepared.target_slot.val ∧
      cache[index.val]? = some (sequence.val, material) := by
  have hcap : cache.length ≤ 50 := hcache.1 ▸ hvalid.control.capacity
  have htarget : prepared.target_slot.val < cache.length := by
    simpa only [hcache.1] using hprepared.target_live
  let index := cache.length - 1 - prepared.target_slot.val
  have hindex : index < cache.length := by dsimp [index]; omega
  obtain ⟨material, hslot⟩ := hprepared.target_material
  refine ⟨⟨index, by omega⟩, material, rfl, ?_⟩
  have hsourceIndex : cache.length - 1 - index = prepared.target_slot.val := by
    dsimp [index]; omega
  simpa only [hsourceIndex, hslot, core.option.Option.Some, _root_.Option.map_some] using
    hcache.2 index hindex

/-- Extracted cached publication implements the generated symbolic swap at every active slot. -/
theorem cached_publication_represents_symbolic_swap {SendChain ReceiveChain Material : Type}
    (state : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material)
    (cache : List (Nat × Material))
    (sequence : Std.U64) (prepared : ratchet.refined.PreparedCachedReceive)
    (hvalid : ratchet.refined.ValidRefined state)
    (hprepared : ratchet.refined.CachedPreparationFacts state sequence prepared)
    (hcache : NewestCacheRepresents state cache) :
    ∃ published, ratchet.refined.publish_cached_receive state prepared = ok published ∧
      ratchet.refined.ValidRefined published ∧
      published.send_chain = state.send_chain ∧
      published.receive_chain = state.receive_chain ∧
      NewestCacheRepresents published
        (registrationCacheSwap cache (cache.length - 1 - prepared.target_slot.val)) := by
  obtain ⟨published, hpublish, hvalidPublished, _, _, hlength, _, _, _⟩ :=
    hprepared.publication state hvalid sequence prepared
  obtain ⟨other, hother, _, hsend, hreceive, hslots⟩ :=
    ratchet.refined.publish_cached_receive_exact state prepared
      hprepared.target_bound hprepared.last_bound
  have heq : other = published := RustM.ok.inj (hother.symm.trans hpublish)
  subst other
  refine ⟨published, hpublish, hvalidPublished, hsend, hreceive, ?_, ?_⟩
  · simp only [registrationCacheSwap_length, hlength, hcache.1]
  · intro j hj
    have hjold : j < cache.length - 1 := by
      simpa only [registrationCacheSwap_length] using hj
    have hcap : cache.length ≤ 50 := hcache.1 ▸ hvalid.control.capacity
    have htarget : prepared.target_slot.val < cache.length := by
      simpa only [hcache.1] using hprepared.target_live
    have hlast : prepared.last_slot.val = cache.length - 1 := by
      simpa only [hcache.1] using hprepared.last_value
    rw [registrationCacheSwap_length, registrationCacheSwap_lookup cache _ j hjold]
    rw [hslots _ (by omega)]
    have hnotlast : cache.length - 1 - 1 - j ≠ prepared.last_slot.val := by omega
    rw [ite_eq_right hnotlast]
    by_cases hselected : cache.length - 1 - prepared.target_slot.val ≠ 0 ∧
        j = cache.length - 1 - prepared.target_slot.val - 1
    · have htargetIndex : cache.length - 1 - 1 - j = prepared.target_slot.val := by omega
      rw [ite_eq_left hselected, ite_eq_left htargetIndex]
      simpa only [Nat.sub_zero, hlast] using hcache.2 0 (by omega)
    · have hotherIndex : cache.length - 1 - 1 - j ≠ prepared.target_slot.val := by omega
      rw [ite_eq_right hselected, ite_eq_right hotherIndex]
      have hindex : cache.length - 1 - (j + 1) = cache.length - 1 - 1 - j := by omega
      simpa only [hindex] using hcache.2 (j + 1) (by omega)

/-- Exact representation of the generated plan in all active source cache slots; validity also fixes every inactive slot. -/
structure RegistrationPublicationRefines {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (published : ratchet.refined.RefinedRatchet ratchet.RatchetChain ratchet.RatchetChain ratchet.RatchetMaterial) : Prop where
  valid : ratchet.refined.ValidRefined published
  sendSequence : published.control.send_sequence = entry.refined.control.send_sequence
  sendChain : published.send_chain = entry.refined.send_chain
  receiveSequence : published.control.receive_sequence = target
  receiveChain : published.receive_chain =
    (registrationPrefix cr entry.refined.receive_chain (target.val - 1)).next
  cacheLength : published.control.receive_cache.len.val =
    (registrationPrefix cr entry.refined.receive_chain (target.val - 1)).skipped.length
  activeCache : ∀ j, j < target.val - 1 →
    ∃ cached : ratchet.refined.CachedReceiveKey ratchet.RatchetMaterial,
      published.receive_slots.val[j]! = core.option.Option.Some cached ∧
      (registrationPrefix cr entry.refined.receive_chain (target.val - 1)).skipped.reverse[j]? =
        some (cached.sequence.val, cached.material)
  targetAbsent : lookup_receive_key published.control target = ok core.option.Option.None

/-- The general extracted publication theorem discharges the generated symbolic cache and chain representation for every admitted initial target. -/
theorem RelativeFutureResult.registration_prefix {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (target : Std.U64)
    (published : ratchet.refined.RefinedRatchet ratchet.RatchetChain ratchet.RatchetChain ratchet.RatchetMaterial)
    (h : RelativeFutureResult cr entry target published)
    (hzero : entry.refined.control.receive_sequence.val = 0)
    (hempty : entry.refined.control.receive_cache.len.val = 0)
    (hpositive : 1 ≤ target.val) :
    RegistrationPublicationRefines cr entry target published := by
  refine ⟨h.valid, h.sendSequence, h.sendChain, h.receiveSequence, ?_, ?_, ?_, h.targetAbsent⟩
  · simpa [registrationPrefix_exact, hzero, Nat.sub_add_cancel hpositive] using h.receiveChain
  · simpa [registrationPrefix_exact, hzero, hempty] using h.length
  · intro j hj
    obtain ⟨cached, hslot, hsequence, hmaterial⟩ := h.staged j (by simpa [hzero] using hj)
    refine ⟨cached, ?_, ?_⟩
    · simpa [hempty] using hslot
    · simp [registrationPrefix_exact, hsequence, hzero, hmaterial, hj]

/-- The admitted source publication supplies the exact list premise of the cached swap theorem. -/
theorem RegistrationPublicationRefines.newest_cache {AD PT CT : Type}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {entry : ConcreteRatchetKernel} {target : Std.U64}
    {published : ratchet.refined.RefinedRatchet ratchet.RatchetChain ratchet.RatchetChain ratchet.RatchetMaterial}
    (h : RegistrationPublicationRefines cr entry target published) :
    NewestCacheRepresents published
      (registrationPrefix cr entry.refined.receive_chain (target.val - 1)).skipped := by
  refine ⟨h.cacheLength.symm, ?_⟩
  intro j hj
  let skipped := (registrationPrefix cr entry.refined.receive_chain (target.val - 1)).skipped
  have hlength : skipped.length = target.val - 1 := by
    simp [skipped, registrationPrefix_exact]
  have hj' : j < skipped.length := hj
  obtain ⟨cached, hslot, hpair⟩ := h.activeCache (skipped.length - 1 - j) (by omega)
  have hreverse : skipped.reverse[skipped.length - 1 - j]? = skipped[j]? :=
    List.getElem?_reverse' (by omega)
  change skipped.reverse[skipped.length - 1 - j]? = some (cached.sequence.val, cached.material) at hpair
  rw [hreverse] at hpair
  change skipped[j]? = _
  rw [hpair, hslot]
  rfl

/-- Every prepared cached target after an admitted publication is one of its earlier positive sequences. -/
theorem RegistrationPublicationRefines.cached_target_is_earlier {AD PT CT : Type}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {entry : ConcreteRatchetKernel} {target sequence : Std.U64}
    {published : ratchet.refined.RefinedRatchet ratchet.RatchetChain ratchet.RatchetChain ratchet.RatchetMaterial}
    {prepared : ratchet.refined.PreparedCachedReceive}
    (h : RegistrationPublicationRefines cr entry target published)
    (hprepared : ratchet.refined.CachedPreparationFacts published sequence prepared) :
    1 ≤ sequence.val ∧ sequence.val < target.val := by
  obtain ⟨index, material, _, hlookup⟩ := cached_symbolic_position_is_exhaustive
    published _ sequence prepared h.valid hprepared h.newest_cache
  have hmem := List.mem_of_getElem? hlookup
  simp only [registrationPrefix_exact, List.mem_reverse, List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
  omega

/-- All 51 raw-receiver admitted initial targets reach the exact generated symbolic plan in exactly `target` KDF calls; every successful callback preserves the entire published state relation. -/
theorem initial_registration_prepares_every_admitted_target {AD PT CT Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (hvalid : ratchet.refined.ValidRefined entry.refined)
    (hzero : entry.refined.control.receive_sequence.val = 0)
    (hempty : entry.refined.control.receive_cache.len.val = 0)
    (hpositive : 1 ≤ target.val) (hbound : target.val ≤ 51) :
    ∃ pending opened,
      begin_receive entry target context = ok (ReceiveEffect.ReceiveKdfRequested pending) ∧
      ReceiveKdfTrace execute (ReceiveEffect.ReceiveKdfRequested pending)
        (ReceiveEffect.ReceiveOpenRequested opened) target.val ∧
      opened.entry = entry ∧ opened.context = context ∧
      opened.material = ok (core.option.Option.Some
        (registrationPrefix (withInterpreter cr execute) entry.refined.receive_chain (target.val - 1)).target) ∧
      ∀ (Output : Type) (plaintext : Output), ∃ published,
        opened.finish (core.option.Option.Some plaintext) =
          ok ({ refined := published }, core.option.Option.Some plaintext) ∧
        RegistrationPublicationRefines (withInterpreter cr execute) entry target published := by
  obtain ⟨pending, opened, hbegin, htrace, hopen⟩ := relative_begin_receive_future_trace cr execute
    entry context target hvalid (by omega) (by omega)
  refine ⟨pending, opened, hbegin, by simpa [hzero] using htrace,
    hopen.choose_spec.1, hopen.choose_spec.2.1, ?_, ?_⟩
  · simpa [registrationPrefix_exact, hzero] using
      hopen.material_exact (withInterpreter cr execute) entry context target opened
  · intro Output plaintext
    obtain ⟨published, hfinish, hpublished⟩ := hopen.finish_some
      (withInterpreter cr execute) entry context target opened plaintext
    exact ⟨published, hfinish,
      hpublished.registration_prefix (withInterpreter cr execute) entry target published hzero hempty hpositive⟩

/-- Every initial target above 51 rejects before either KDF or authenticated opening. -/
theorem initial_registration_rejects_above_51 {Context : Type}
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (hzero : entry.refined.control.receive_sequence.val = 0)
    (hempty : entry.refined.control.receive_cache.len.val = 0)
    (hlarge : 51 < target.val) :
    begin_receive entry target context = ok (ReceiveEffect.ReceiveRejected entry context) :=
  begin_receive_capacity_rejected entry target context (by omega) (by omega)

/-- Sequence zero rejects from every structurally valid empty initial cache. -/
theorem initial_registration_rejects_zero {Context : Type}
    (entry : ConcreteRatchetKernel) (context : Context)
    (hvalid : ratchet.refined.ValidRefined entry.refined)
    (hempty : entry.refined.control.receive_cache.len.val = 0) :
    begin_receive entry 0#u64 context = ok (ReceiveEffect.ReceiveRejected entry context) :=
  begin_receive_old_missing entry 0#u64 context (by scalar_tac)
    (lookup_receive_key_of_not_mem entry.refined.control 0#u64 hvalid.control.capacity
      (by simp [cacheSeqs, hempty]))

/-- This is an exhaustive finite split of every admitted raw-receiver `u64` target, not a production registration-completion rule. -/
theorem initial_registration_case_is_exhaustive (target : Std.U64)
    (hpositive : 1 ≤ target.val) (hbound : target.val ≤ 51) :
    ∃ index : Fin 51, index.val + 1 = target.val :=
  ⟨⟨target.val - 1, by omega⟩, Nat.sub_add_cancel hpositive⟩

/-- Any admitted committed state rejects its consumed registration target, even if the later callback and interpreter change. -/
theorem RegistrationPublicationRefines.replay {AD PT CT Context Output : Type}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {entry : ConcreteRatchetKernel} {target : Std.U64}
    {published : ratchet.refined.RefinedRatchet ratchet.RatchetChain ratchet.RatchetChain ratchet.RatchetMaterial}
    (h : RegistrationPublicationRefines cr entry target published) (hpositive : 1 ≤ target.val)
    (execute : KdfInterpreter) (context : Context)
    (reply : ReceiveOpen Context → core.option.Option Output) :
    receiveNext execute { refined := published } target context reply =
      ok ({ refined := published }, core.option.Option.None) :=
  (show ReceiveSuccess target { refined := published } from
    ⟨h.valid, by omega, by simp [h.receiveSequence], h.targetAbsent⟩).replay execute context reply

/-- Arbitrary finite mixed callback traffic continues from any admitted committed state; there is no fixed cached-1/future-4 trace premise. -/
theorem RegistrationPublicationRefines.continue {AD PT CT Context Output : Type}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {entry : ConcreteRatchetKernel} {target : Std.U64}
    {published : ratchet.refined.RefinedRatchet ratchet.RatchetChain ratchet.RatchetChain ratchet.RatchetMaterial}
    (h : RegistrationPublicationRefines cr entry target published)
    (execute : KdfInterpreter) (actions : List (RoleAction Context Output)) :
    ∃ finalState outputs,
      executeHistory execute { refined := published } actions = ok (finalState, outputs) ∧
      outputs.length = actions.length ∧ ratchet.refined.ValidRefined finalState.refined :=
  executeHistory_preserves_validity cr execute actions { refined := published } h.valid

end beaconcrypt_core.ratchet.concrete

/-- info: 'beaconcrypt_core.ratchet.concrete.registrationPrefix_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationPrefix_exact

/-- info: 'beaconcrypt_core.ratchet.concrete.registrationCacheSwap_case' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationCacheSwap_case

/-- info: 'beaconcrypt_core.ratchet.concrete.registrationCacheSwap_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationCacheSwap_length

/-- info: 'beaconcrypt_core.ratchet.concrete.registrationCacheSwap_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationCacheSwap_lookup

/-- info: 'beaconcrypt_core.ratchet.concrete.NewestCacheRepresents.sequence_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.NewestCacheRepresents.sequence_unique

/-- info: 'beaconcrypt_core.ratchet.concrete.cached_symbolic_position_is_exhaustive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.cached_symbolic_position_is_exhaustive

/-- info: 'beaconcrypt_core.ratchet.concrete.cached_publication_represents_symbolic_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.cached_publication_represents_symbolic_swap

/-- info: 'beaconcrypt_core.ratchet.concrete.RelativeFutureResult.registration_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.RelativeFutureResult.registration_prefix

/-- info: 'beaconcrypt_core.ratchet.concrete.RegistrationPublicationRefines.newest_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.RegistrationPublicationRefines.newest_cache

/-- info: 'beaconcrypt_core.ratchet.concrete.initial_registration_prepares_every_admitted_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.initial_registration_prepares_every_admitted_target

/-- info: 'beaconcrypt_core.ratchet.concrete.initial_registration_rejects_above_51' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.initial_registration_rejects_above_51

/-- info: 'beaconcrypt_core.ratchet.concrete.initial_registration_rejects_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.initial_registration_rejects_zero

/-- info: 'beaconcrypt_core.ratchet.concrete.initial_registration_case_is_exhaustive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.initial_registration_case_is_exhaustive

/-- info: 'beaconcrypt_core.ratchet.concrete.RegistrationPublicationRefines.replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.RegistrationPublicationRefines.replay

/-- info: 'beaconcrypt_core.ratchet.concrete.RegistrationPublicationRefines.continue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.RegistrationPublicationRefines.continue

/-- info: 'beaconcrypt_core.ratchet.concrete.registrationSendToken_advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationSendToken_advance
/-- info: 'beaconcrypt_core.ratchet.concrete.registrationSendToken_plan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationSendToken_plan
/-- info: 'beaconcrypt_core.ratchet.concrete.registrationSendToken_after_first' does not depend on any axioms -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationSendToken_after_first

/-- info: 'beaconcrypt_core.ratchet.concrete.registrationSendObservedRun_public' depends on axioms: [propext] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationSendObservedRun_public
/-- info: 'beaconcrypt_core.ratchet.concrete.registrationSendAfterCutoff_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationSendAfterCutoff_index

/--
info: 'beaconcrypt_core.ratchet.concrete.RegistrationPublicationRefines.cached_target_is_earlier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.RegistrationPublicationRefines.cached_target_is_earlier

/--
info: 'beaconcrypt_core.ratchet.concrete.registrationPrefix_member_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationPrefix_member_sequence
/--
info: 'beaconcrypt_core.ratchet.concrete.registrationPrefix_selected_case_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.registrationPrefix_selected_case_sequence
