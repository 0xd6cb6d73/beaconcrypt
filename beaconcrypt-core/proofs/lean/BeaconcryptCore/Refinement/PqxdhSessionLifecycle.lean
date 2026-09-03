import BeaconcryptCore.Refinement.PqxdhConcreteSession
import BeaconcryptCore.Refinement.RatchetCachedLifecycle
import BeaconcryptCore.Refinement.RatchetReceiveReachability

/-! Composition of concrete lifetime reachability into the paired PQXDH session. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.PqxdhConcreteSession

theorem concreteSession_iff_roles {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (beaconOrigin serverOrigin : ratchet.RatchetChain) (beacon server : ConcreteRatchetKernel) :
    ConcreteSession cr beaconOrigin serverOrigin beacon server ↔
      RoleReachable cr beaconOrigin serverOrigin beacon ∧ RoleReachable cr serverOrigin beaconOrigin server :=
  ⟨fun ⟨bs, br, ss, sr, hb, hs, hbc, hsc⟩ => ⟨⟨bs, br, hb, hbc⟩, ⟨ss, sr, hs, hsc⟩⟩,
    fun ⟨⟨bs, br, hb, hbc⟩, ⟨ss, sr, hs, hsc⟩⟩ => ⟨bs, br, ss, sr, hb, hs, hbc, hsc⟩⟩

theorem ConcreteSession.swap {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (beaconOrigin serverOrigin : ratchet.RatchetChain) (beacon server : ConcreteRatchetKernel)
    (h : ConcreteSession cr beaconOrigin serverOrigin beacon server) :
    ConcreteSession cr serverOrigin beaconOrigin server beacon :=
  (concreteSession_iff_roles cr serverOrigin beaconOrigin server beacon).mpr
    ((concreteSession_iff_roles cr beaconOrigin serverOrigin beacon server).mp h).symm

/-- A complete beacon send attempt preserves the paired lifetime invariant for any seal callback. -/
theorem ConcreteSession.seal_beacon_preserves {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (beaconOrigin serverOrigin : ratchet.RatchetChain)
    (beacon server : ConcreteRatchetKernel)
    (h : ConcreteSession (withInterpreter cr execute) beaconOrigin serverOrigin beacon server)
    (context : Context)
    (sealCallback : ratchet.RatchetMaterial → Std.U64 → Context → core.option.Option Output) :
    ∃ next output, sealNext execute beacon context sealCallback = ok (next, output) ∧
      ConcreteSession (withInterpreter cr execute) beaconOrigin serverOrigin next server :=
  let roles := (concreteSession_iff_roles _ _ _ _ _).mp h
  (sealNext_preserves_reachability cr execute beaconOrigin serverOrigin beacon roles.1 context sealCallback).elim
    fun next hn => hn.elim fun output hout =>
      ⟨next, output, hout.1, (concreteSession_iff_roles _ _ _ _ _).mpr ⟨hout.2, roles.2⟩⟩

/-- The reverse direction has the same complete send-attempt preservation property. -/
theorem ConcreteSession.seal_server_preserves {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (beaconOrigin serverOrigin : ratchet.RatchetChain)
    (beacon server : ConcreteRatchetKernel)
    (h : ConcreteSession (withInterpreter cr execute) beaconOrigin serverOrigin beacon server)
    (context : Context)
    (sealCallback : ratchet.RatchetMaterial → Std.U64 → Context → core.option.Option Output) :
    ∃ next output, sealNext execute server context sealCallback = ok (next, output) ∧
      ConcreteSession (withInterpreter cr execute) beaconOrigin serverOrigin beacon next :=
  (ConcreteSession.seal_beacon_preserves cr execute serverOrigin beaconOrigin server beacon
    (ConcreteSession.swap _ _ _ _ _ h) context sealCallback).elim fun next hn => hn.elim fun output hout =>
      ⟨next, output, hout.1, ConcreteSession.swap _ _ _ _ _ hout.2⟩

/-- Any refinement witnesses for a reachable kernel have the same send origin and counter. -/
theorem role_send_origin_of_refines {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : ratchet.RatchetChain) (kernel : ConcreteRatchetKernel)
    (hrole : RoleReachable cr sendOrigin receiveOrigin kernel)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (hkernel : KernelRefines cr receiveOrigin send receive kernel) :
    send.ck = Ratchet.chainAt cr sendOrigin send.n :=
  hrole.elim fun _ hrest => hrest.elim fun _ hother =>
    (hkernel.sendChain.symm.trans hother.1.sendChain).trans
      (hother.2.trans (congrArg (Ratchet.chainAt cr sendOrigin)
        (hother.1.sendSequence.symm.trans hkernel.sendSequence)))

/-- Finishing an admitted cached server opening preserves the paired session for every optional callback result. -/
theorem ConcreteSession.finish_cached_server_preserves {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (beaconOrigin serverOrigin : ratchet.RatchetChain) (beacon : ConcreteRatchetKernel)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (index : Nat) (material : ratchet.RatchetMaterial) (pending : ReceiveOpen Context)
    (h : ConcreteSession cr beaconOrigin serverOrigin beacon pending.entry)
    (hpending : CachedOpenRefines cr beaconOrigin send receive index material pending)
    (opened : core.option.Option Output) :
    ∃ next, pending.finish opened = ok (next, opened) ∧
      ConcreteSession cr beaconOrigin serverOrigin beacon next := by
  have roles := (concreteSession_iff_roles _ _ _ _ _).mp h
  have hsend := role_send_origin_of_refines cr serverOrigin beaconOrigin pending.entry roles.2 send receive
    hpending.choose_spec.choose_spec.2.2.2.2.1
  exact (CachedOpenRefines.finish_preserves_reachability cr serverOrigin beaconOrigin send receive index material
    pending hpending hsend opened).elim fun next hn =>
      ⟨next, hn.1, (concreteSession_iff_roles _ _ _ _ _).mpr ⟨roles.1, hn.2⟩⟩

theorem ConcreteSession.finish_cached_beacon_preserves {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (beaconOrigin serverOrigin : ratchet.RatchetChain) (server : ConcreteRatchetKernel)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (index : Nat) (material : ratchet.RatchetMaterial) (pending : ReceiveOpen Context)
    (h : ConcreteSession cr beaconOrigin serverOrigin pending.entry server)
    (hpending : CachedOpenRefines cr serverOrigin send receive index material pending)
    (opened : core.option.Option Output) :
    ∃ next, pending.finish opened = ok (next, opened) ∧
      ConcreteSession cr beaconOrigin serverOrigin next server :=
  (ConcreteSession.finish_cached_server_preserves cr serverOrigin beaconOrigin server send receive index material
    pending (ConcreteSession.swap _ _ _ _ _ h) hpending opened).elim fun next hn =>
      ⟨next, hn.1, ConcreteSession.swap _ _ _ _ _ hn.2⟩

/-- A complete beacon send followed by any complete server receive attempt preserves the session, for every target and both callback outcomes. -/
theorem beacon_seal_server_open_preserves_concrete_session {AD PT CT SealContext Ciphertext OpenContext Plaintext : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (beaconOrigin serverOrigin : ratchet.RatchetChain)
    (beacon server : ConcreteRatchetKernel)
    (h : ConcreteSession (withInterpreter cr execute) beaconOrigin serverOrigin beacon server)
    (target : Std.U64) (sealContext : SealContext)
    (sealCallback : ratchet.RatchetMaterial → Std.U64 → SealContext → core.option.Option Ciphertext)
    (openContext : OpenContext) (openReply : ReceiveOpen OpenContext → core.option.Option Plaintext) :
    ∃ nextBeacon ciphertext nextServer plaintext,
      sealNext execute beacon sealContext sealCallback = ok (nextBeacon, ciphertext) ∧
      receiveNext execute server target openContext openReply = ok (nextServer, plaintext) ∧
      ConcreteSession (withInterpreter cr execute) beaconOrigin serverOrigin nextBeacon nextServer :=
  let roles := (concreteSession_iff_roles _ _ _ _ _).mp h
  (sealNext_preserves_reachability cr execute beaconOrigin serverOrigin beacon roles.1 sealContext sealCallback).elim
    fun nextBeacon hs => hs.elim fun ciphertext hseal =>
  (receiveNext_preserves_reachability cr execute serverOrigin beaconOrigin server target openContext openReply roles.2).elim
    fun nextServer hr => hr.elim fun plaintext hopen =>
      ⟨nextBeacon, ciphertext, nextServer, plaintext, hseal.1, hopen.1,
        (concreteSession_iff_roles _ _ _ _ _).mpr ⟨hseal.2, hopen.2⟩⟩

/-- The reverse role direction preserves the same paired session for every complete callback-driven send and receive attempt. -/
theorem server_seal_beacon_open_preserves_concrete_session {AD PT CT SealContext Ciphertext OpenContext Plaintext : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (beaconOrigin serverOrigin : ratchet.RatchetChain)
    (beacon server : ConcreteRatchetKernel)
    (h : ConcreteSession (withInterpreter cr execute) beaconOrigin serverOrigin beacon server)
    (target : Std.U64) (sealContext : SealContext)
    (sealCallback : ratchet.RatchetMaterial → Std.U64 → SealContext → core.option.Option Ciphertext)
    (openContext : OpenContext) (openReply : ReceiveOpen OpenContext → core.option.Option Plaintext) :
    ∃ nextServer ciphertext nextBeacon plaintext,
      sealNext execute server sealContext sealCallback = ok (nextServer, ciphertext) ∧
      receiveNext execute beacon target openContext openReply = ok (nextBeacon, plaintext) ∧
      ConcreteSession (withInterpreter cr execute) beaconOrigin serverOrigin nextBeacon nextServer :=
  (beacon_seal_server_open_preserves_concrete_session cr execute serverOrigin beaconOrigin server beacon
    (ConcreteSession.swap _ _ _ _ _ h) target sealContext sealCallback openContext openReply).elim
    fun nextServer hs => hs.elim fun ciphertext hb => hb.elim fun nextBeacon hp => hp.elim fun plaintext hout =>
      ⟨nextServer, ciphertext, nextBeacon, plaintext, hout.1, hout.2.1, ConcreteSession.swap _ _ _ _ _ hout.2.2⟩

end BeaconcryptCore.Refinement.PqxdhConcreteSession
