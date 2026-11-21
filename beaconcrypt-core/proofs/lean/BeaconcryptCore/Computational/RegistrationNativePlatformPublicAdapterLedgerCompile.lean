import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerScope
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSendRepresentability (slice)
abbrev SourceSpec :=RegistrationNativePlatformPublicAdapterInterface.Spec
abbrev Spec :=RegistrationNativePlatformPublicAdapterLowSpec.Spec

noncomputable def lower :QueryImpl RegistrationNativeInterface.Spec (OracleComp Spec)
  | .inl coin=>(RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inl coin) :OracleComp Spec _)
  | .inr (.create ed ml kid)=>
    if efits :ed.length≤Usize.max then
      if mfits :ml.length≤Usize.max then RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.create (slice ed efits) (slice ml mfits) kid))
      else pure none
    else pure none
  | .inr (.bundle owner)=>RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.bundle owner))
  | .inr (.accept raw)=>if fits :raw.length≤Usize.max then RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.accept (slice raw fits))) else pure none
  | .inr (.build handle payload)=>match payload with
    | none=>RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.build handle none))
    | some bytes=>if fits :bytes.length≤Usize.max then RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.build handle (some (slice bytes fits)))) else pure none
  | .inr (.finish owner raw)=>if fits :raw.length≤Usize.max then RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.finish owner (slice raw fits))) else pure none
  | .inr (.hmac key message)=>RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.hmac key message))
  | .inr (.hash bytes)=>RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.hash bytes))
  | .inr (.serverSend kid bytes)=>if fits :bytes.length≤Usize.max then RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.serverSend kid (slice bytes fits))) else Spec.query (.inr (.serverSend kid bytes fits))
  | .inr (.serverRaw raw)=>if fits :raw.length≤Usize.max then RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.serverRaw (slice raw fits))) else pure .None
  | .inr (.beaconSend owner bytes)=>if fits :bytes.length≤Usize.max then RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.beaconSend owner (slice bytes fits))) else Spec.query (.inr (.beaconSend owner bytes fits))
  | .inr (.beaconRaw owner raw)=>if fits :raw.length≤Usize.max then RegistrationNativePlatformPublicAdapterLowSpec.publicQuery (.inr (.beaconRaw owner (slice raw fits))) else pure .None

noncomputable def program {Reader Response A :Type} (crypto :Pqxdh.Crypto) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
    (work :OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) A) :
    OracleComp Spec (A×RegistrationNativeLedger.State) :=
  simulateQ lower (RegistrationNativeLedger.wrap crypto codec serverKid bounds
    (RegistrationNativeInterface.asModeO mode (RegistrationNativePlatformPublicAdapterInterface.compile mode work)))

private theorem bytes_bound (raw :Slice U8) :(TranscriptAuthParts.absSlice raw).length≤Usize.max :=by
  simpa only [TranscriptAuthParts.absSlice,List.length_map] using raw.property

theorem original (query :SourceSpec.Domain) :
    simulateQ lower (RegistrationNativePlatformPublicAdapterInterface.adapter query)=
      (RegistrationNativePlatformPublicAdapterLowSpec.publicQuery query :OracleComp Spec _) :=by
  rcases query with coin|command
  · rfl
  · cases command with
    | build handle payload=>
      cases payload <;>simp [RegistrationNativePlatformPublicAdapterInterface.adapter,
        RegistrationNativePlatformPublicAdapterInterface.nativeCommand,lower,bytes_bound];
        repeat' rw [RegistrationNativePlatformPublicAdapterSendRepresentability.slice_roundtrip]
    | create ed ml kid=>
      simp [RegistrationNativePlatformPublicAdapterInterface.adapter,
        RegistrationNativePlatformPublicAdapterInterface.nativeCommand,lower,bytes_bound];
        repeat' rw [RegistrationNativePlatformPublicAdapterSendRepresentability.slice_roundtrip]
    | bundle _ | accept _ | finish _ _ | hmac _ _ | hash _ | serverSend _ _ | serverRaw _ | beaconSend _ _ | beaconRaw _ _=>
      simp [RegistrationNativePlatformPublicAdapterInterface.adapter,
        RegistrationNativePlatformPublicAdapterInterface.nativeCommand,lower,bytes_bound];
        repeat' rw [RegistrationNativePlatformPublicAdapterSendRepresentability.slice_roundtrip]

theorem query_native (query :RegistrationNativeInterface.Spec.Domain)
    (allowed :RegistrationNativePlatformPublicAdapterLedgerScope.Allowed query) :
    simulateQ RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter (lower query)=
      (RegistrationNativeInterface.Spec.query query :OracleComp RegistrationNativeInterface.Spec _) :=by
  rcases query with coin|command
  · rfl
  · cases command with
    | create ed ml kid=>
      change ed.length≤Usize.max ∧ml.length≤Usize.max at allowed
      simp only [lower,dite_eq_left allowed.1,dite_eq_left allowed.2]
      rw [RegistrationNativePlatformPublicAdapterLowSpec.public_native]
      dsimp only [RegistrationNativePlatformPublicAdapterInterface.adapter,
        RegistrationNativePlatformPublicAdapterInterface.nativeCommand,Option.map]
      repeat' rw [RegistrationNativePlatformPublicAdapterSendRepresentability.slice_bytes]
    | accept raw | finish _ raw | serverRaw raw | beaconRaw _ raw=>
      change raw.length≤Usize.max at allowed
      simp only [lower,dite_eq_left allowed]
      rw [RegistrationNativePlatformPublicAdapterLowSpec.public_native]
      dsimp only [RegistrationNativePlatformPublicAdapterInterface.adapter,
        RegistrationNativePlatformPublicAdapterInterface.nativeCommand,Option.map]
      repeat' rw [RegistrationNativePlatformPublicAdapterSendRepresentability.slice_bytes]
    | build handle payload=>
      cases payload with
      | none=>rfl
      | some bytes=>
        have fits:=allowed bytes rfl
        simp only [lower,dite_eq_left fits]
        rw [RegistrationNativePlatformPublicAdapterLowSpec.public_native]
        dsimp only [RegistrationNativePlatformPublicAdapterInterface.adapter,
          RegistrationNativePlatformPublicAdapterInterface.nativeCommand,Option.map]
        repeat' rw [RegistrationNativePlatformPublicAdapterSendRepresentability.slice_bytes]
    | bundle _ | hmac _ _ | hash _=>rfl
    | serverSend kid bytes=>
      by_cases fits :bytes.length≤Usize.max
      · simp only [lower,dite_eq_left fits]
        rw [RegistrationNativePlatformPublicAdapterLowSpec.public_native]
        dsimp only [RegistrationNativePlatformPublicAdapterInterface.adapter,
          RegistrationNativePlatformPublicAdapterInterface.nativeCommand,Option.map]
        repeat' rw [RegistrationNativePlatformPublicAdapterSendRepresentability.slice_bytes]
      · simp only [lower,dite_eq_right fits,simulateQ_spec_query,RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter]
    | beaconSend owner bytes=>
      by_cases fits :bytes.length≤Usize.max
      · simp only [lower,dite_eq_left fits]
        rw [RegistrationNativePlatformPublicAdapterLowSpec.public_native]
        dsimp only [RegistrationNativePlatformPublicAdapterInterface.adapter,
          RegistrationNativePlatformPublicAdapterInterface.nativeCommand,Option.map]
        repeat' rw [RegistrationNativePlatformPublicAdapterSendRepresentability.slice_bytes]
      · simp only [lower,dite_eq_right fits,simulateQ_spec_query,RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter]

private theorem scoped_native {A :Type} (work :OracleComp RegistrationNativeInterface.Spec A)
    (allowed :AllQueriesSatisfy work RegistrationNativePlatformPublicAdapterLedgerScope.Allowed) :
    simulateQ RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter (simulateQ lower work)=work :=by
  rw [←QueryImpl.simulateQ_compose]
  induction work using OracleComp.inductionOn with
  | pure value=>rfl
  | query_bind query next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    rw [simulateQ_bind,simulateQ_spec_query]
    change (simulateQ RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter (lower query) >>=fun reply=>
      simulateQ (RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter ∘ₛlower) (next reply))=_
    rw [query_native query allowed.1]
    apply bind_congr
    intro reply
    exact ih reply (allowed.2 reply)

theorem program_native {Reader Response A :Type} (crypto :Pqxdh.Crypto) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
    (work :OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) A) :
    simulateQ RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter (program crypto codec serverKid bounds mode work)=
      RegistrationNativeLedger.wrap crypto codec serverKid bounds
        (RegistrationNativeInterface.asModeO mode (RegistrationNativePlatformPublicAdapterInterface.compile mode work)) :=
  scoped_native _ (RegistrationNativePlatformPublicAdapterLedgerScope.full crypto codec serverKid bounds mode work)

theorem program_typed {A :Type} (crypto :Pqxdh.Crypto) (wire :RegistrationNativeWire.Wire)
    (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
    (work :OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) A) :
    simulateQ (RegistrationNativeRawAdapter.adapter wire ∘ₛRegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter)
      (program crypto (RegistrationNativeWire.ledgerCodec wire) serverKid bounds mode work)=
      RegistrationNativeFullCompiler.compile crypto wire serverKid bounds mode
        (RegistrationNativePlatformPublicAdapterInterface.compile mode work) :=by
  rw [QueryImpl.simulateQ_compose,program_native]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile.original' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile.original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile.query_native' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile.query_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile.program_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile.program_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile.program_typed
