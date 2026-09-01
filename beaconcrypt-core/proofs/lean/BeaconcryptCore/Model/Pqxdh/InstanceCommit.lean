import BeaconcryptCore.Model.Pqxdh.Instance
import BeaconcryptCore.Model.Pqxdh.Acceptance

/-!
# Non-vacuity of the commitment hypotheses

`BeaconcryptCore.Model.Pqxdh.Commit` states the commitment properties of the record
layer under two hypotheses about BLAKE2b-512, both restricted to the pair of record
contexts at hand:

* `Pqxdh.NoCtxCollision` — no collision between the two commitment inputs.  It holds
  for any instance when the two contexts coincide (`Pqxdh.noCtxCollision_self`), so
  it is satisfiable.
* `Pqxdh.CtxDistinct` — the two contexts commit to different values.  This is the
  hypothesis every *rejection* result uses, so it deserves an instance in which it
  provably holds for genuinely different contexts.

This file provides such an instance.  `Pqxdh.Toy.tailCrypto` is the toy instance of
`BeaconcryptCore.Model.Pqxdh.Instance` with its "hash" replaced by the last 64 bytes
of the input.  At the field lengths the protocol fixes, those 64 bytes end with
`LE64(seq) ‖ LE64(sid)`, so two record contexts with different sequence numbers — or
different sender identifiers — provably commit to different values.  A *global*
injectivity assumption on a 64-byte digest would be inconsistent; this is the honest
substitute.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Pqxdh
namespace Toy

/-- The toy primitives with the "hash" replaced by the trailing 64 bytes of its
input.  Like `Pqxdh.Toy.toyCrypto` it is completely insecure; it exists only to
witness that `Pqxdh.CtxDistinct` is satisfiable for genuinely different record
contexts. -/
def tailCrypto : Crypto :=
  { toyCrypto with
    blake2b := fun x => padTo 64 (x.drop (x.length - 64))
    blake2b_length := by intro x; simp }

/-- The commitment input of a well-formed record context is 229 bytes long. -/
theorem ctxPreimage_length {mk : Bytes × Bytes} {ad : RecordAD} {t : Bytes}
    (hw : RecordWf mk ad) (ht : t.length = 16) :
    (ctxPreimage mk ad t).length = 229 := by
  simp [ctxPreimage, hw.key, hw.nonce, hw.bytes, ht]

/-- Under `tailCrypto` the commitment of a well-formed record context is the trailing
64 bytes of its input, and therefore ends with `LE64(seq) ‖ LE64(sid)`. -/
theorem tailCrypto_ctxCommit {mk : Bytes × Bytes} {ad : RecordAD} {t : Bytes}
    (hw : RecordWf mk ad) (ht : t.length = 16) :
    ctxCommit tailCrypto mk ad t
      = (mk.1 ++ mk.2 ++ ad.bytes ++ t).drop 165 ++ LE64 ad.seq ++ LE64 ad.sid := by
  have hp : (ctxPreimage mk ad t).length = 229 := ctxPreimage_length hw ht
  have h1 : (mk.1 ++ mk.2 ++ ad.bytes ++ t ++ LE64 ad.seq).length = 221 := by
    simp [hw.key, hw.nonce, hw.bytes, ht]
  have h2 : (mk.1 ++ mk.2 ++ ad.bytes ++ t).length = 213 := by
    simp [hw.key, hw.nonce, hw.bytes, ht]
  have hdrop : (ctxPreimage mk ad t).drop 165
      = (mk.1 ++ mk.2 ++ ad.bytes ++ t).drop 165 ++ LE64 ad.seq ++ LE64 ad.sid := by
    rw [ctxPreimage,
      List.drop_append_of_le_length (by omega : 165 ≤
        (mk.1 ++ mk.2 ++ ad.bytes ++ t ++ LE64 ad.seq).length),
      List.drop_append_of_le_length (by omega : 165 ≤
        (mk.1 ++ mk.2 ++ ad.bytes ++ t).length)]
  have hlen : ((mk.1 ++ mk.2 ++ ad.bytes ++ t).drop 165 ++ LE64 ad.seq
      ++ LE64 ad.sid).length = 64 := by
    simp only [List.length_append, List.length_drop, LE64_length, h2]
  rw [ctxCommit_eq]
  show padTo 64 ((ctxPreimage mk ad t).drop ((ctxPreimage mk ad t).length - 64)) = _
  rw [hp, show (229 : ℕ) - 64 = 165 from rfl, hdrop, padTo_of_length hlen]

/-- **The rejection hypothesis is satisfiable.**  Over `tailCrypto`, two well-formed
record contexts with different wire sequence numbers commit to different values, so
`Pqxdh.CtxDistinct` — the hypothesis of every re-labelling rejection result — is not
vacuous. -/
theorem tailCrypto_ctxDistinct_of_seq_ne {mk mk' : Bytes × Bytes} {ad ad' : RecordAD}
    (hw : RecordWf mk ad) (hw' : RecordWf mk' ad') (hne : ad.seq ≠ ad'.seq) :
    CtxDistinct tailCrypto mk mk' ad ad' := by
  intro t ht hcol
  rw [tailCrypto_ctxCommit hw ht, tailCrypto_ctxCommit hw' ht] at hcol
  obtain ⟨h1, -⟩ := List.append_inj' hcol (by simp)
  obtain ⟨-, h2⟩ := List.append_inj' h1 (by simp)
  exact hne (LE64_inj hw.seq hw'.seq h2)

/-- Likewise for the sender identifier: two well-formed record contexts from different
senders commit to different values. -/
theorem tailCrypto_ctxDistinct_of_sid_ne {mk mk' : Bytes × Bytes} {ad ad' : RecordAD}
    (hw : RecordWf mk ad) (hw' : RecordWf mk' ad') (hne : ad.sid ≠ ad'.sid) :
    CtxDistinct tailCrypto mk mk' ad ad' := by
  intro t ht hcol
  rw [tailCrypto_ctxCommit hw ht, tailCrypto_ctxCommit hw' ht] at hcol
  obtain ⟨-, h1⟩ := List.append_inj' hcol (by simp)
  exact hne (LE64_inj hw.sid hw'.sid h1)

/-- Consequently, over `tailCrypto`, a record sealed at one sequence number really
does fail to open at another: an instance of `Pqxdh.openRecord_relabelled` with all
hypotheses discharged. -/
theorem tailCrypto_openRecord_wrong_seq {mk : Bytes × Bytes} {ad : RecordAD} {pt : Bytes}
    {seq' : ℕ} (hw : RecordWf mk ad) (hseq : seq' < 2 ^ 64) (hne : seq' ≠ ad.seq) :
    openRecord tailCrypto mk { ad with seq := seq' } (sealRecord tailCrypto mk ad pt).encode
      = none :=
  openRecord_relabelled tailCrypto
    (tailCrypto_ctxDistinct_of_seq_ne hw ⟨hw.key, hw.nonce, hw.bytes, hseq, hw.sid⟩
      (fun hc => hne hc.symm))

/-! ## The rejection results apply to a concrete run

`Pqxdh.Toy.demoTail` is the concrete honest registration of
`BeaconcryptCore.Model.Pqxdh.Instance` run over `tailCrypto`.  All the hypotheses of
`Pqxdh.HonestRun.beacon_rejects_reordered_record` are discharged for it, so that
result is not vacuous either. -/

/-- The concrete honest registration, over `tailCrypto`. -/
def demoTail : HonestRun := { demo with c := tailCrypto }

/-- It is still an honest run. -/
theorem demoTail_ok : demoTail.Ok :=
  ⟨by decide, by decide, by decide, rfl, by decide⟩

/-- The associated data of the concrete run has the protocol's length. -/
theorem demoTail_ad_length : demoTail.ad.length = 153 :=
  assocData_length (tailCrypto.edPub_length _) (tailCrypto.edPub_length _)

/-- **A concrete instance of the re-labelling rejection.**  The beacon of the concrete
run aborts with `BadRecord` when the server's first record is presented at wire
sequence number 3 instead of the 1 it was sealed at. -/
theorem demoTail_rejects_reordered_record :
    beaconFinish demoTail.c demoTail.beaconInitSent
        { demoTail.response with
          appFrame := { demoTail.response.appFrame with seq := 3 } }
      = (.error .badRecord, .aborted) := by
  refine demoTail.beacon_rejects_reordered_record demoTail_ok ?_ (by decide)
  refine tailCrypto_ctxDistinct_of_seq_ne
    (recordWf_msgMaterial tailCrypto demoTail.chains.1 demoTail_ad_length
      (by decide) (by decide))
    (recordWf_msgKeyAt tailCrypto demoTail.chains.1 (3 - 1) demoTail_ad_length
      (by decide) (by decide)) (by decide)

end Toy
end Pqxdh
