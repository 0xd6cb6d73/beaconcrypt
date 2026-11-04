-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerBuildTrace
/-! An exact free source form of the SDK Builder prefix. Its leaves are the actual source pin getter, map read, map reservation and full source record/installer suffix. Every Rust result and optional refusal follows the literal extracted control flow. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgram
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperStorage (PeerMap)
open AdapterPublicServerBuildBody (Server Reply)
open AdapterPublicServerBuildTrace (Publication Word)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
abbrev Spec :=(Server →ₒ RegistrationNativeServerPinRecompute.PinReply)+
  (((PeerMap×U64) →ₒ RustM Bool)+
    ((PeerMap →ₒ RustM (core.result.Result Unit platform.ReserveError×PeerMap))+
      ((Server×registration.ServerInitialKdf) →ₒ (Publication×RustM Reply))))

private def returned {A :Type} (_self :Server) (result :RustM A) (next :A→OracleComp Spec Word) :OracleComp Spec Word :=
  match result with
  | .fail error=>pure (none,.fail error)
  | .div=>pure (none,.div)
  | .ok value=>next value

private def checked {A Error :Type} (self :Server) (result :RustM (core.result.Result A Error))
    (next :A→OracleComp Spec Word) :OracleComp Spec Word :=
  match result with
  | .fail error=>pure (none,.fail error)
  | .div=>pure (none,.div)
  | .ok (.Err _)=>pure (none,.ok (.None,self))
  | .ok (.Ok value)=>next value

def reserved (self :Server) (initial :registration.ServerInitialKdf) :OracleComp Spec Word :=do
  let reply←Spec.query (.inr (.inr (.inl self.known_ids)))
  returned self reply fun result=>
    let current:={self with known_ids:=result.2}
    match result.1 with
    | .Err _=>pure (none,.ok (.None,current))
    | .Ok _=>(fun result=>(some result.1,result.2)) <$>Spec.query (.inr (.inr (.inr (current,initial))))

def lookup (self :Server) (pending :peer.CompletionLookup) (plaintext :Slice U8) :OracleComp Spec Word :=
  returned self pending.request fun identifier=>
  returned self (CoreModels.core.slice.Slice.len plaintext) fun size=>
  returned self (transport.registration_response_len size identifier) fun optional=>
    match optional with
    | .None=>pure (none,.ok (.None,self))
    | .Some _=>do
      let reply←Spec.query (.inr (.inl (self.known_ids,identifier)))
      returned self reply fun occupied=>checked self (pending.resume occupied) (reserved self)

def program (self :Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :OracleComp Spec Word :=
  returned self (transport.normalize_registration_application data) fun application=>
  returned self (beaconcrypt_public_wrapper.server.registration_application_bytes application) fun plaintext=>do
    let reply←Spec.query (.inl self)
    returned self reply fun optional=>
      match optional with
      | .None=>pure (none,.ok (.None,self))
      | .Some pin=>checked self (peer.begin_completion_lookup self.control pin token.registration plaintext)
          (fun pending=>lookup self pending plaintext)

variable {m :Type→Type} [Monad m] [LawfulMonad m]
variable [localOps :LocalOperations (RustT m)] [crypto :CryptoOperations (RustT m)]
variable [children :ChildOperations (RustT m)] [containers :ContainerOperations (RustT m)]

noncomputable def handler (completion :Server → registration.ServerInitialKdf→m (Publication×RustM Reply)) :QueryImpl Spec m
  | .inl self=>(beaconcrypt_public_request.server.Server.authentication_pin (m:=RustT m) self).run
  | .inr (.inl (known,identifier))=>
      (containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) known identifier).run
  | .inr (.inr (.inl known))=>
      (containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator known 1#usize).run
  | .inr (.inr (.inr (self,initial)))=>completion self initial

variable (completion :Server → registration.ServerInitialKdf→m (Publication×RustM Reply))

private theorem reserved_source (self :Server) (initial :registration.ServerInitialKdf) :
    simulateQ (handler completion) (reserved self initial)=AdapterPublicServerBuildTrace.reserved completion self initial := by
  unfold reserved AdapterPublicServerBuildTrace.reserved AdapterPublicServerBuildTrace.invoke
  rw [simulateQ_bind,simulateQ_spec_query]
  apply bind_congr
  intro reply
  cases reply with
  | fail error | div=>rfl
  | ok result=>
    rcases result with ⟨reply,known⟩
    cases reply with
    | Err error=>rfl
    | Ok value=>
      simp only [returned,simulateQ_map,simulateQ_spec_query,handler]
      rfl

private theorem lookup_source (self :Server) (pending :peer.CompletionLookup) (plaintext :Slice U8) :
    simulateQ (handler completion) (lookup self pending plaintext)=AdapterPublicServerBuildTrace.lookup completion self pending plaintext := by
  have wrapped :∀size identifier,(beaconcrypt_public_request.server.registration_response_len (m:=RustT m) size identifier).run=
    pure (transport.registration_response_len size identifier):=fun _ _=>rfl
  unfold lookup AdapterPublicServerBuildTrace.lookup AdapterPublicServerBuildTrace.invoke
  simp only [RustT.run_liftRust,pure_bind,wrapped]
  cases requested:pending.request with
  | fail error | div=>rfl
  | ok identifier=>
    simp only [returned]
    cases sizeEq:CoreModels.core.slice.Slice.len plaintext with
    | fail error | div=>rfl
    | ok size=>
      dsimp only
      cases optionalEq:transport.registration_response_len size identifier with
      | fail error | div=>rfl
      | ok optional=>
        dsimp only
        cases optional with
        | none=>rfl
        | some capacity=>
          simp only [simulateQ_bind,simulateQ_spec_query,handler]
          apply bind_congr
          intro reply
          cases reply with
          | fail error | div=>rfl
          | ok occupied=>
            dsimp only
            cases resumed:pending.resume occupied with
            | fail error | div=>rfl
            | ok result=>cases result with
              | Err previous=>rfl
              | Ok initial=>
                simpa only [checked,AdapterPublicServerBuildTrace.checked,resumed] using reserved_source completion self initial

theorem source (self :Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) :
    simulateQ (handler completion) (program self token data)=AdapterPublicServerBuildTrace.build completion self token data := by
  unfold program AdapterPublicServerBuildTrace.build AdapterPublicServerBuildTrace.invoke
  simp only [RustT.run_liftRust,pure_bind]
  cases normalized:transport.normalize_registration_application data with
  | fail error | div=>rfl
  | ok application=>
    simp only [returned]
    cases bytes:beaconcrypt_public_wrapper.server.registration_application_bytes application with
    | fail error | div=>rfl
    | ok plaintext=>
      simp only [simulateQ_bind,simulateQ_spec_query,handler]
      apply bind_congr
      intro reply
      cases reply with
      | fail error | div=>rfl
      | ok optional=>
        dsimp only
        cases optional with
        | none=>rfl
        | some pin=>
          dsimp only
          cases began:peer.begin_completion_lookup self.control pin token.registration plaintext with
          | fail error | div=>rfl
          | ok result=>cases result with
            | Err previous=>rfl
            | Ok pending=>
              simpa only [checked,AdapterPublicServerBuildTrace.checked,began] using lookup_source completion self pending plaintext

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgram


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgram.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgram.source
