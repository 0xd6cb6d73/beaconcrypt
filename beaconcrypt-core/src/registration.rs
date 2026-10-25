// SPDX-License-Identifier: 0BSD

//! Owned registration authentication requests. Primitive responses are supplied
//! by an interpreter; every continuation retains the exact selected fields.

// Fixed-width owned phases avoid allocation; explicit matches avoid unsupported Try extraction.
#![allow(clippy::large_enum_variant, clippy::question_mark)]

use crate::agreement::ResponsePublic;
use crate::authentication::{
	AuthRole, INIT_TRANSCRIPT_LEN, InitFields, MLDSA_PUBLIC_KEY_LEN, MLDSA_SIGNATURE_LEN,
	RESPONSE_PREFIX_LEN, SIGNATURE_INPUT_LEN, SIGNING_CONTEXT, TRANSCRIPT_HASH_LEN,
	build_init_transcript, build_response_prefix, build_signature_input, encode_u64_le,
};
use crate::pqxdh::{
	ENCODED_MLKEM768_PUBLIC_KEY_SIZE, ENCODED_X25519_PUBLIC_KEY_SIZE, InitKex, SIGN_TYPE_ED25519,
	ServerBinding, VerifiedInitKex, validate_init_kex,
};
use crate::session::{RegistrationBinding, ServerAuthenticationPin};

/// The exact single input or ordered transcript parts selected by the current phase.
pub enum HashRequest<'a> {
	Single(&'a [u8]),
	Triple([&'a [u8]; 3]),
}

pub struct MldsaVerificationRequest<'a> {
	pub public_key: &'a [u8; MLDSA_PUBLIC_KEY_LEN],
	pub input: &'a [u8; SIGNATURE_INPUT_LEN],
	pub context: [u8; 32],
	pub signature: &'a [u8; MLDSA_SIGNATURE_LEN],
}

pub struct Ed25519VerificationRequest<'a> {
	pub public_key: &'a [u8; 32],
	pub signed: &'a [u8],
}

/// Fixed-width views of one complete decoded InitKex.
pub struct InitPacket<'a> {
	identity_key: &'a [u8; 33],
	pre_key: &'a [u8; 98],
	one_time_key: &'a [u8; 98],
	pq_key: &'a [u8; 1249],
	mldsa_public_key: &'a [u8; MLDSA_PUBLIC_KEY_LEN],
	signature: &'a [u8; MLDSA_SIGNATURE_LEN],
}

impl<'a> InitPacket<'a> {
	pub fn from_slices(
		identity_key: &'a [u8],
		pre_key: &'a [u8],
		one_time_key: &'a [u8],
		pq_key: &'a [u8],
		mldsa_public_key: &'a [u8],
		signature: &'a [u8],
	) -> Option<Self> {
		Some(Self {
			identity_key: match identity_key.try_into() {
				Ok(value) => value,
				Err(_) => return None,
			},
			pre_key: match pre_key.try_into() {
				Ok(value) => value,
				Err(_) => return None,
			},
			one_time_key: match one_time_key.try_into() {
				Ok(value) => value,
				Err(_) => return None,
			},
			pq_key: match pq_key.try_into() {
				Ok(value) => value,
				Err(_) => return None,
			},
			mldsa_public_key: match mldsa_public_key.try_into() {
				Ok(value) => value,
				Err(_) => return None,
			},
			signature: match signature.try_into() {
				Ok(value) => value,
				Err(_) => return None,
			},
		})
	}

	fn fields(&self) -> InitFields<'a> {
		InitFields {
			identity_key: self.identity_key,
			pre_key: self.pre_key,
			one_time_key: self.one_time_key,
			pq_key: self.pq_key,
			mldsa_public_key: self.mldsa_public_key,
		}
	}
}

pub struct PinFingerprint {
	binding: ServerBinding,
	public_key: [u8; MLDSA_PUBLIC_KEY_LEN],
}

pub fn begin_server_pin(
	binding: ServerBinding,
	public_key: [u8; MLDSA_PUBLIC_KEY_LEN],
) -> PinFingerprint {
	PinFingerprint {
		binding,
		public_key,
	}
}

impl PinFingerprint {
	pub fn request(&self) -> HashRequest<'_> {
		HashRequest::Single(&self.public_key)
	}

	pub fn resume(
		self,
		fingerprint: Option<[u8; TRANSCRIPT_HASH_LEN]>,
	) -> Option<ServerAuthenticationPin> {
		Some(ServerAuthenticationPin::new(
			self.binding,
			self.public_key,
			match fingerprint {
				Some(value) => value,
				None => return None,
			},
		))
	}
}

struct InitAuthenticationState<'a> {
	packet: InitPacket<'a>,
	server_pin: ServerAuthenticationPin,
	init_hash: [u8; TRANSCRIPT_HASH_LEN],
}

pub enum InitAuthentication<'a> {
	HashRequested(InitHash<'a>),
	MldsaVerificationRequested(InitMldsaVerification<'a>),
	Ed25519VerificationRequested(InitEd25519Verification<'a>),
	ServerFingerprintRequested(InitServerFingerprint<'a>),
	BeaconFingerprintRequested(InitBeaconFingerprint<'a>),
	Accepted(AuthenticatedInit),
	Rejected,
}

pub struct InitHash<'a> {
	packet: InitPacket<'a>,
	server_pin: ServerAuthenticationPin,
	input: [u8; INIT_TRANSCRIPT_LEN],
}

pub fn begin_init_authentication<'a>(
	server_pin: ServerAuthenticationPin,
	packet: InitPacket<'a>,
) -> InitAuthentication<'a> {
	let server = server_pin.binding();
	let input = build_init_transcript(
		packet.fields(),
		server.identity_key_id,
		&server.identity_public_key,
		server_pin.public_key(),
	);
	InitAuthentication::HashRequested(InitHash {
		packet,
		server_pin,
		input,
	})
}

impl<'a> InitHash<'a> {
	pub fn request(&self) -> HashRequest<'_> {
		HashRequest::Single(&self.input)
	}

	pub fn resume(self, hash: Option<[u8; TRANSCRIPT_HASH_LEN]>) -> InitAuthentication<'a> {
		let Some(init_hash) = hash else {
			return InitAuthentication::Rejected;
		};
		InitAuthentication::MldsaVerificationRequested(InitMldsaVerification {
			input: build_signature_input(AuthRole::Beacon, &init_hash),
			state: InitAuthenticationState {
				packet: self.packet,
				server_pin: self.server_pin,
				init_hash,
			},
		})
	}
}

pub struct InitMldsaVerification<'a> {
	state: InitAuthenticationState<'a>,
	input: [u8; SIGNATURE_INPUT_LEN],
}

impl<'a> InitMldsaVerification<'a> {
	pub fn request(&self) -> MldsaVerificationRequest<'_> {
		MldsaVerificationRequest {
			public_key: self.state.packet.mldsa_public_key,
			input: &self.input,
			context: SIGNING_CONTEXT,
			signature: self.state.packet.signature,
		}
	}

	pub fn resume(self, verified: bool) -> InitAuthentication<'a> {
		if !verified || self.state.packet.identity_key[0] != SIGN_TYPE_ED25519 {
			return InitAuthentication::Rejected;
		}
		let public_key = core::array::from_fn(|index| self.state.packet.identity_key[index + 1]);
		InitAuthentication::Ed25519VerificationRequested(InitEd25519Verification {
			state: self.state,
			public_key,
			stage: SignedKeyStage::PqKey,
			pre_key: [0; ENCODED_X25519_PUBLIC_KEY_SIZE],
			pq_key: [0; ENCODED_MLKEM768_PUBLIC_KEY_SIZE],
		})
	}
}

enum SignedKeyStage {
	PreKey,
	OneTimeKey,
	PqKey,
}

pub struct InitEd25519Verification<'a> {
	state: InitAuthenticationState<'a>,
	public_key: [u8; 32],
	stage: SignedKeyStage,
	pre_key: [u8; ENCODED_X25519_PUBLIC_KEY_SIZE],
	pq_key: [u8; ENCODED_MLKEM768_PUBLIC_KEY_SIZE],
}

impl<'a> InitEd25519Verification<'a> {
	pub fn request(&self) -> Ed25519VerificationRequest<'_> {
		let signed: &[u8] = match self.stage {
			SignedKeyStage::PreKey => self.state.packet.pre_key,
			SignedKeyStage::OneTimeKey => self.state.packet.one_time_key,
			SignedKeyStage::PqKey => self.state.packet.pq_key,
		};
		Ed25519VerificationRequest {
			public_key: &self.public_key,
			signed,
		}
	}

	pub fn resume(mut self, opened: Option<&[u8]>) -> InitAuthentication<'a> {
		let Some(opened) = opened else {
			return InitAuthentication::Rejected;
		};
		// Native verification returns the exact attached message, not a new field.
		if opened != &self.request().signed[64..] {
			return InitAuthentication::Rejected;
		}
		match self.stage {
			SignedKeyStage::PreKey => {
				let Ok(pre_key) = opened.try_into() else {
					return InitAuthentication::Rejected;
				};
				self.pre_key = pre_key;
				self.stage = SignedKeyStage::OneTimeKey;
				InitAuthentication::Ed25519VerificationRequested(self)
			}
			SignedKeyStage::OneTimeKey => {
				let Ok(one_time_key) = opened.try_into() else {
					return InitAuthentication::Rejected;
				};
				let message = InitKex::from_encoded(
					*self.state.packet.identity_key,
					self.pre_key,
					one_time_key,
					self.pq_key,
				);
				let Ok(registration) = validate_init_kex(message) else {
					return InitAuthentication::Rejected;
				};
				InitAuthentication::ServerFingerprintRequested(InitServerFingerprint {
					state: self.state,
					registration,
				})
			}
			SignedKeyStage::PqKey => {
				let Ok(pq_key) = opened.try_into() else {
					return InitAuthentication::Rejected;
				};
				self.pq_key = pq_key;
				self.stage = SignedKeyStage::PreKey;
				InitAuthentication::Ed25519VerificationRequested(self)
			}
		}
	}
}

pub struct InitServerFingerprint<'a> {
	state: InitAuthenticationState<'a>,
	registration: VerifiedInitKex,
}

impl<'a> InitServerFingerprint<'a> {
	pub fn request(&self) -> HashRequest<'_> {
		HashRequest::Single(self.state.server_pin.public_key())
	}

	pub fn resume(self, fingerprint: Option<[u8; TRANSCRIPT_HASH_LEN]>) -> InitAuthentication<'a> {
		let Some(fingerprint) = fingerprint else {
			return InitAuthentication::Rejected;
		};
		InitAuthentication::BeaconFingerprintRequested(InitBeaconFingerprint {
			server_pin: ServerAuthenticationPin::new(
				self.state.server_pin.binding(),
				*self.state.server_pin.public_key(),
				fingerprint,
			),
			state: self.state,
			registration: self.registration,
		})
	}
}

pub struct InitBeaconFingerprint<'a> {
	state: InitAuthenticationState<'a>,
	server_pin: ServerAuthenticationPin,
	registration: VerifiedInitKex,
}

impl<'a> InitBeaconFingerprint<'a> {
	pub fn request(&self) -> HashRequest<'_> {
		HashRequest::Single(self.state.packet.mldsa_public_key)
	}

	pub fn resume(self, fingerprint: Option<[u8; TRANSCRIPT_HASH_LEN]>) -> InitAuthentication<'a> {
		let Some(fingerprint) = fingerprint else {
			return InitAuthentication::Rejected;
		};
		let binding = RegistrationBinding::new(
			self.server_pin,
			self.state.init_hash,
			*self.registration.beacon_identity_public_key(),
			fingerprint,
		);
		InitAuthentication::Accepted(AuthenticatedInit {
			registration: self.registration,
			binding,
		})
	}
}

pub struct AuthenticatedInit {
	registration: VerifiedInitKex,
	binding: RegistrationBinding,
}

impl AuthenticatedInit {
	pub fn registration_id(&self) -> crate::pqxdh::RegistrationId {
		crate::pqxdh::registration_id(&self.registration)
	}

	pub(crate) fn into_parts(self) -> (VerifiedInitKex, RegistrationBinding) {
		(self.registration, self.binding)
	}
}

/// Fixed-width views of one complete decoded KexResponse.
pub struct ResponsePacket<'a> {
	public: ResponsePublic,
	application: &'a [u8],
	signature: &'a [u8; MLDSA_SIGNATURE_LEN],
}

impl<'a> ResponsePacket<'a> {
	pub fn from_slices(
		identity_key: &[u8],
		ephemeral_key: &[u8],
		kem_cipher_text: &[u8],
		key_id: u64,
		application: &'a [u8],
		signature: &'a [u8],
	) -> Option<Self> {
		Some(Self {
			public: ResponsePublic {
				identity_key: match identity_key.try_into() {
					Ok(value) => value,
					Err(_) => return None,
				},
				ephemeral_key: match ephemeral_key.try_into() {
					Ok(value) => value,
					Err(_) => return None,
				},
				kem_cipher_text: match kem_cipher_text.try_into() {
					Ok(value) => value,
					Err(_) => return None,
				},
				key_id,
			},
			application,
			signature: match signature.try_into() {
				Ok(value) => value,
				Err(_) => return None,
			},
		})
	}
}

/// The unique request capability produced only after successful Init serialization.
pub struct BeaconPending {
	control: crate::pqxdh::BeaconInitSent,
	binding: RegistrationBinding,
}

impl BeaconPending {
	pub const fn server_key_id(&self) -> u64 {
		self.control.server_key_id()
	}
	pub const fn aborted_state(&self) -> crate::pqxdh::BeaconAborted {
		crate::pqxdh::beacon_abort_init(self.control)
	}
	pub fn abort(self) -> crate::pqxdh::BeaconAborted {
		crate::pqxdh::beacon_abort_init(self.control)
	}
}

pub struct ResponseHash<'a> {
	pending: BeaconPending,
	packet: ResponsePacket<'a>,
	prefix: [u8; RESPONSE_PREFIX_LEN],
	assigned_id: [u8; 8],
}

pub fn begin_response_authentication<'a>(
	pending: BeaconPending,
	packet: Option<ResponsePacket<'a>>,
) -> Result<ResponseHash<'a>, crate::pqxdh::BeaconAborted> {
	let packet = match packet {
		Some(packet) => packet,
		None => return Err(pending.abort()),
	};
	let application_len = match u64::try_from(packet.application.len()) {
		Ok(length) => length,
		Err(_) => return Err(pending.abort()),
	};
	let prefix = build_response_prefix(
		pending.binding.init_hash(),
		&packet.public.identity_key,
		&packet.public.ephemeral_key,
		&packet.public.kem_cipher_text,
		application_len,
	);
	let assigned_id = encode_u64_le(packet.public.key_id);
	Ok(ResponseHash {
		pending,
		packet,
		prefix,
		assigned_id,
	})
}

impl<'a> ResponseHash<'a> {
	pub fn request(&self) -> HashRequest<'_> {
		HashRequest::Triple([&self.prefix, self.packet.application, &self.assigned_id])
	}

	pub fn resume(
		self,
		digest: Option<[u8; TRANSCRIPT_HASH_LEN]>,
	) -> Result<ResponseMldsaVerification<'a>, crate::pqxdh::BeaconAborted> {
		let digest = match digest {
			Some(digest) => digest,
			None => return Err(self.pending.abort()),
		};
		Ok(ResponseMldsaVerification {
			input: build_signature_input(AuthRole::Server, &digest),
			pending: self.pending,
			packet: self.packet,
		})
	}
}

pub struct ResponseMldsaVerification<'a> {
	pending: BeaconPending,
	packet: ResponsePacket<'a>,
	input: [u8; SIGNATURE_INPUT_LEN],
}

impl<'a> ResponseMldsaVerification<'a> {
	pub fn request(&self) -> MldsaVerificationRequest<'_> {
		MldsaVerificationRequest {
			public_key: self.pending.binding.server_pin().public_key(),
			input: &self.input,
			context: SIGNING_CONTEXT,
			signature: self.packet.signature,
		}
	}

	pub fn resume(
		self,
		verified: bool,
	) -> Result<AuthenticatedResponse<'a>, crate::pqxdh::BeaconAborted> {
		if !verified {
			return Err(self.pending.abort());
		}
		Ok(AuthenticatedResponse {
			pending: self.pending,
			packet: self.packet,
		})
	}
}

pub struct AuthenticatedResponse<'a> {
	pending: BeaconPending,
	packet: ResponsePacket<'a>,
}

impl<'a> AuthenticatedResponse<'a> {
	pub(crate) fn into_parts(
		self,
	) -> (
		crate::pqxdh::BeaconInitSent,
		RegistrationBinding,
		ResponsePublic,
		&'a [u8],
	) {
		(
			self.pending.control,
			self.pending.binding,
			self.packet.public,
			self.packet.application,
		)
	}
}

pub struct Ed25519SigningRequest<'a> {
	pub public_key: &'a [u8; 32],
	pub role: AuthRole,
	pub message: &'a [u8],
}

pub struct MldsaSigningRequest<'a> {
	pub public_key: &'a [u8; MLDSA_PUBLIC_KEY_LEN],
	pub role: AuthRole,
	pub input: &'a [u8; SIGNATURE_INPUT_LEN],
	pub context: [u8; 32],
}

struct BeaconInitState {
	original_control: crate::pqxdh::BeaconFresh,
	started: crate::pqxdh::BeaconStart,
	server_pin: ServerAuthenticationPin,
	beacon_identity: [u8; 32],
	beacon_mldsa: [u8; MLDSA_PUBLIC_KEY_LEN],
	pre_key: [u8; 98],
	one_time_key: [u8; 98],
	pq_key: [u8; 1249],
}

impl BeaconInitState {
	fn fields(&self) -> InitFields<'_> {
		InitFields {
			identity_key: self.started.message.identity_key(),
			pre_key: &self.pre_key,
			one_time_key: &self.one_time_key,
			pq_key: &self.pq_key,
			mldsa_public_key: &self.beacon_mldsa,
		}
	}
}

pub enum BeaconInitEffect {
	Rejected(crate::pqxdh::BeaconFresh),
	Ed25519SigningRequested(BeaconEd25519Signing),
	FingerprintRequested(BeaconFingerprint),
	HashRequested(BeaconInitHash),
	MldsaSigningRequested(BeaconMldsaSigning),
	Ready(BeaconInitReady),
}

pub fn begin_beacon_init(
	control: crate::pqxdh::BeaconFresh,
	inputs: crate::pqxdh::BeaconStartInputs,
	coins: crate::pqxdh::BeaconCoins,
	server_pin: ServerAuthenticationPin,
	beacon_mldsa: [u8; MLDSA_PUBLIC_KEY_LEN],
) -> BeaconInitEffect {
	let expected = control.expected_server_binding();
	let actual = server_pin.binding();
	if expected.identity_key_id != actual.identity_key_id
		|| expected.identity_public_key != actual.identity_public_key
	{
		return BeaconInitEffect::Rejected(control);
	}
	let beacon_identity = inputs.identity_public_key;
	let started = crate::pqxdh::beacon_start(control, inputs, coins);
	BeaconInitEffect::Ed25519SigningRequested(BeaconEd25519Signing {
		state: BeaconInitState {
			original_control: control,
			started,
			server_pin,
			beacon_identity,
			beacon_mldsa,
			pre_key: [0; 98],
			one_time_key: [0; 98],
			pq_key: [0; 1249],
		},
		stage: SignedKeyStage::PreKey,
	})
}

pub struct BeaconEd25519Signing {
	state: BeaconInitState,
	stage: SignedKeyStage,
}

impl BeaconEd25519Signing {
	pub fn request(&self) -> Ed25519SigningRequest<'_> {
		let message: &[u8] = match self.stage {
			SignedKeyStage::PreKey => self.state.started.message.prekey(),
			SignedKeyStage::OneTimeKey => self.state.started.message.one_time_key(),
			SignedKeyStage::PqKey => self.state.started.message.pq_key(),
		};
		Ed25519SigningRequest {
			public_key: &self.state.beacon_identity,
			role: AuthRole::Beacon,
			message,
		}
	}

	pub fn resume(mut self, signed: Option<&[u8]>) -> BeaconInitEffect {
		let Some(signed) = signed else {
			return BeaconInitEffect::Rejected(self.state.original_control);
		};
		if signed.get(64..) != Some(self.request().message) {
			return BeaconInitEffect::Rejected(self.state.original_control);
		}
		match self.stage {
			SignedKeyStage::PreKey => {
				let Ok(bytes) = signed.try_into() else {
					return BeaconInitEffect::Rejected(self.state.original_control);
				};
				self.state.pre_key = bytes;
				self.stage = SignedKeyStage::OneTimeKey;
				BeaconInitEffect::Ed25519SigningRequested(self)
			}
			SignedKeyStage::OneTimeKey => {
				let Ok(bytes) = signed.try_into() else {
					return BeaconInitEffect::Rejected(self.state.original_control);
				};
				self.state.one_time_key = bytes;
				self.stage = SignedKeyStage::PqKey;
				BeaconInitEffect::Ed25519SigningRequested(self)
			}
			SignedKeyStage::PqKey => {
				let Ok(bytes) = signed.try_into() else {
					return BeaconInitEffect::Rejected(self.state.original_control);
				};
				self.state.pq_key = bytes;
				BeaconInitEffect::FingerprintRequested(BeaconFingerprint { state: self.state })
			}
		}
	}
}

pub struct BeaconFingerprint {
	state: BeaconInitState,
}

impl BeaconFingerprint {
	pub fn request(&self) -> HashRequest<'_> {
		HashRequest::Single(&self.state.beacon_mldsa)
	}

	pub fn resume(self, fingerprint: Option<[u8; TRANSCRIPT_HASH_LEN]>) -> BeaconInitEffect {
		let Some(fingerprint) = fingerprint else {
			return BeaconInitEffect::Rejected(self.state.original_control);
		};
		let server = self.state.server_pin.binding();
		let input = build_init_transcript(
			self.state.fields(),
			server.identity_key_id,
			&server.identity_public_key,
			self.state.server_pin.public_key(),
		);
		BeaconInitEffect::HashRequested(BeaconInitHash {
			state: self.state,
			fingerprint,
			input,
		})
	}
}

pub struct BeaconInitHash {
	state: BeaconInitState,
	fingerprint: [u8; TRANSCRIPT_HASH_LEN],
	input: [u8; INIT_TRANSCRIPT_LEN],
}

impl BeaconInitHash {
	pub fn request(&self) -> HashRequest<'_> {
		HashRequest::Single(&self.input)
	}

	pub fn resume(self, hash: Option<[u8; TRANSCRIPT_HASH_LEN]>) -> BeaconInitEffect {
		let Some(init_hash) = hash else {
			return BeaconInitEffect::Rejected(self.state.original_control);
		};
		BeaconInitEffect::MldsaSigningRequested(BeaconMldsaSigning {
			state: self.state,
			fingerprint: self.fingerprint,
			init_hash,
			input: build_signature_input(AuthRole::Beacon, &init_hash),
		})
	}
}

pub struct BeaconMldsaSigning {
	state: BeaconInitState,
	fingerprint: [u8; TRANSCRIPT_HASH_LEN],
	init_hash: [u8; TRANSCRIPT_HASH_LEN],
	input: [u8; SIGNATURE_INPUT_LEN],
}

impl BeaconMldsaSigning {
	pub fn request(&self) -> MldsaSigningRequest<'_> {
		MldsaSigningRequest {
			role: AuthRole::Beacon,
			public_key: &self.state.beacon_mldsa,
			input: &self.input,
			context: SIGNING_CONTEXT,
		}
	}

	pub fn resume(self, signature: Option<&[u8]>) -> BeaconInitEffect {
		let Some(signature) = signature else {
			return BeaconInitEffect::Rejected(self.state.original_control);
		};
		let Ok(signature) = signature.try_into() else {
			return BeaconInitEffect::Rejected(self.state.original_control);
		};
		let binding = RegistrationBinding::new(
			self.state.server_pin,
			self.init_hash,
			self.state.beacon_identity,
			self.fingerprint,
		);
		BeaconInitEffect::Ready(BeaconInitReady {
			state: self.state,
			binding,
			signature,
		})
	}
}

pub struct SignedInitView<'a> {
	pub fields: InitFields<'a>,
	pub signature: &'a [u8; MLDSA_SIGNATURE_LEN],
}

pub struct BeaconInitReady {
	state: BeaconInitState,
	binding: RegistrationBinding,
	signature: [u8; MLDSA_SIGNATURE_LEN],
}

impl BeaconInitReady {
	pub fn message(&self) -> SignedInitView<'_> {
		SignedInitView {
			fields: self.state.fields(),
			signature: &self.signature,
		}
	}

	pub fn publish<Encoded>(
		self,
		encoded: Option<Encoded>,
	) -> Result<PublishedBeaconInit<Encoded>, crate::pqxdh::BeaconFresh> {
		let encoded = match encoded {
			Some(encoded) => encoded,
			None => return Err(self.state.original_control),
		};
		Ok(PublishedBeaconInit {
			pending: BeaconPending {
				control: self.state.started.state,
				binding: self.binding,
			},
			encoded,
		})
	}
}

pub struct PublishedBeaconInit<Encoded> {
	pending: BeaconPending,
	encoded: Encoded,
}

impl<Encoded> PublishedBeaconInit<Encoded> {
	pub fn into_parts(self) -> (BeaconPending, Encoded) {
		(self.pending, self.encoded)
	}
}

pub struct BeaconInitialKdf<'a> {
	agreement: crate::agreement::BeaconAgreement<'a>,
	pending: crate::pqxdh::InitialRatchetKdfPending,
}

pub fn begin_beacon_completion(
	agreement: crate::agreement::BeaconAgreement<'_>,
) -> BeaconInitialKdf<'_> {
	let pending = crate::pqxdh::start_beacon_candidate_ratchet_kdf(
		&agreement.candidate,
		agreement.root.as_bytes(),
	);
	BeaconInitialKdf { agreement, pending }
}

impl<'a> BeaconInitialKdf<'a> {
	pub const fn request(&self) -> &crate::ratchet::SymmetricRatchetKdfRequest {
		self.pending.request()
	}

	pub fn resume(
		self,
		response: Option<crate::pqxdh::InitialRatchetKdfResponse>,
	) -> Result<BeaconInitialOpen<'a>, crate::pqxdh::BeaconAborted> {
		let response = match response {
			Some(response) => response,
			None => {
				return Err(crate::pqxdh::beacon_abort_candidate(
					self.agreement.candidate,
				));
			}
		};
		let kernel = crate::pqxdh::resume_initial_ratchet_kdf(self.pending, response);
		Ok(BeaconInitialOpen {
			agreement: self.agreement,
			kernel: Some(kernel),
		})
	}
}

/// Temporary complete-record interpreter seam, replaced by composed record effects in item 3.
pub struct InitialOpenRequest<'a> {
	pub ciphertext: &'a [u8],
	pub associated_data: &'a [u8; crate::pqxdh::ASSOCIATED_DATA_SIZE],
	pub sequence: u64,
	pub sender_key_id: u64,
}

pub struct InitialOpened<'a> {
	pub plaintext: &'a [u8],
	pub sequence: u64,
	pub sender_key_id: u64,
}

pub struct BeaconInitialOpen<'a> {
	agreement: crate::agreement::BeaconAgreement<'a>,
	kernel: Option<crate::ratchet::ConcreteRatchetKernel>,
}

impl BeaconInitialOpen<'_> {
	pub fn request(&self) -> InitialOpenRequest<'_> {
		InitialOpenRequest {
			ciphertext: self.agreement.application_ciphertext,
			associated_data: self.agreement.binding.associated_data(),
			sequence: 1,
			sender_key_id: self.agreement.candidate.server_key_id(),
		}
	}

	pub fn take_kernel(&mut self) -> Option<crate::ratchet::ConcreteRatchetKernel> {
		self.kernel.take()
	}

	/// The interpreter must return the same kernel after the exact requested open.
	pub fn resume<'a>(
		self,
		kernel: crate::ratchet::ConcreteRatchetKernel,
		opened: Option<InitialOpened<'a>>,
	) -> Result<CompletedBeacon<'a>, crate::pqxdh::BeaconAborted> {
		let server_key_id = self.agreement.candidate.server_key_id();
		let rejected = crate::pqxdh::BeaconAborted::new(server_key_id);
		if self.kernel.is_some()
			|| kernel.send_sequence() != 0
			|| kernel.receive_sequence() != 1
			|| kernel.receive_cache_len() != 0
		{
			return Err(rejected);
		}
		let Some(opened) = opened else {
			return Err(rejected);
		};
		if opened.sequence != 1
			|| opened.plaintext.len() <= crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE
		{
			return Err(rejected);
		}
		let (prefix, application) = opened
			.plaintext
			.split_at(crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE);
		let Ok(prefix) = prefix.try_into() else {
			return Err(rejected);
		};
		let Ok(authenticated) = crate::pqxdh::authenticate_registration_key_id_binding(
			self.agreement.candidate,
			opened.sender_key_id,
			prefix,
		) else {
			return Err(rejected);
		};
		let binding = self
			.agreement
			.binding
			.finish(authenticated.assigned_key_id());
		Ok(CompletedBeacon {
			control: crate::pqxdh::beacon_commit(authenticated),
			binding,
			kernel,
			application,
		})
	}
}

pub struct CompletedBeacon<'a> {
	control: crate::pqxdh::BeaconEstablished,
	binding: crate::session::SessionBinding,
	kernel: crate::ratchet::ConcreteRatchetKernel,
	application: &'a [u8],
}

impl<'a> CompletedBeacon<'a> {
	pub fn into_parts(
		self,
	) -> (
		crate::pqxdh::BeaconEstablished,
		crate::session::SessionBinding,
		crate::ratchet::ConcreteRatchetKernel,
		&'a [u8],
	) {
		(self.control, self.binding, self.kernel, self.application)
	}
}

pub struct ServerInitialKdf<'a> {
	candidate: crate::pqxdh::ServerRegistrationCandidate,
	binding: RegistrationBinding,
	application: &'a [u8],
	pending: crate::pqxdh::InitialRatchetKdfPending,
}

pub fn begin_server_completion<'a>(
	control: crate::pqxdh::ServerState,
	current_pin: &ServerAuthenticationPin,
	availability: crate::pqxdh::KeyIdAvailability,
	agreement: crate::agreement::ServerAgreement,
	application: &'a [u8],
) -> Result<ServerInitialKdf<'a>, crate::pqxdh::ServerState> {
	let rejected = control;
	if application.is_empty() || !agreement.binding.matches_server(current_pin) {
		return Err(rejected);
	}
	let candidate = match crate::pqxdh::server_prepare_commit(
		control,
		agreement.pending,
		current_pin.binding(),
		availability,
	) {
		Ok(candidate) => candidate,
		Err(_) => return Err(rejected),
	};
	let pending =
		crate::pqxdh::start_server_candidate_ratchet_kdf(&candidate, agreement.root.as_bytes());
	Ok(ServerInitialKdf {
		candidate,
		binding: agreement.binding,
		application,
		pending,
	})
}

impl<'a> ServerInitialKdf<'a> {
	pub const fn request(&self) -> &crate::ratchet::SymmetricRatchetKdfRequest {
		self.pending.request()
	}

	pub fn resume(
		self,
		response: Option<crate::pqxdh::InitialRatchetKdfResponse>,
	) -> Result<ServerInitialSeal<'a>, crate::pqxdh::ServerState> {
		let rejected = crate::pqxdh::server_abort_candidate(&self.candidate);
		let response = match response {
			Some(response) => response,
			None => return Err(rejected),
		};
		let kernel = crate::pqxdh::resume_initial_ratchet_kdf(self.pending, response);
		let prefix = *self.candidate.key_id_binding().as_bytes();
		Ok(ServerInitialSeal {
			candidate: self.candidate,
			binding: self.binding,
			application: self.application,
			prefix,
			kernel: Some(kernel),
		})
	}
}

pub struct InitialSealRequest<'a> {
	pub plaintext: [&'a [u8]; 2],
	pub associated_data: &'a [u8; crate::pqxdh::ASSOCIATED_DATA_SIZE],
	pub sequence: u64,
	pub sender_key_id: u64,
	pub target_key_id: u64,
}

pub struct ServerInitialSeal<'a> {
	candidate: crate::pqxdh::ServerRegistrationCandidate,
	binding: RegistrationBinding,
	application: &'a [u8],
	prefix: [u8; 8],
	kernel: Option<crate::ratchet::ConcreteRatchetKernel>,
}

impl ServerInitialSeal<'_> {
	pub fn request(&self) -> InitialSealRequest<'_> {
		InitialSealRequest {
			plaintext: [&self.prefix, self.application],
			associated_data: self.binding.associated_data(),
			sequence: 1,
			sender_key_id: self.candidate.server_identity_key_id(),
			target_key_id: self.candidate.key_id(),
		}
	}

	pub fn take_kernel(&mut self) -> Option<crate::ratchet::ConcreteRatchetKernel> {
		self.kernel.take()
	}

	/// The interpreter must return the same kernel and ciphertext from the exact requested seal.
	pub fn resume<'a>(
		self,
		kernel: crate::ratchet::ConcreteRatchetKernel,
		sequence: u64,
		ciphertext: Option<&'a [u8]>,
	) -> Result<ServerResponseHash<'a>, crate::pqxdh::ServerState> {
		let rejected = crate::pqxdh::server_abort_candidate(&self.candidate);
		if self.kernel.is_some()
			|| sequence != 1
			|| kernel.send_sequence() != 1
			|| kernel.receive_sequence() != 0
			|| kernel.receive_cache_len() != 0
		{
			return Err(rejected);
		}
		let ciphertext = match ciphertext {
			Some(ciphertext) => ciphertext,
			None => return Err(rejected),
		};
		let bound_length = match 8usize.checked_add(self.application.len()) {
			Some(length) => length,
			None => return Err(rejected),
		};
		let length = match bound_length.checked_add(crate::record::MESSAGE_OVERHEAD) {
			Some(length) => length,
			None => return Err(rejected),
		};
		if ciphertext.len() != length {
			return Err(rejected);
		}
		let prefix = build_response_prefix(
			self.binding.init_hash(),
			self.candidate.server_identity_public_key(),
			self.candidate.ephemeral_public_key(),
			self.candidate.kem_ciphertext(),
			match u64::try_from(ciphertext.len()) {
				Ok(length) => length,
				Err(_) => return Err(rejected),
			},
		);
		let assigned_id = encode_u64_le(self.candidate.key_id());
		Ok(ServerResponseHash {
			candidate: self.candidate,
			binding: self.binding,
			kernel,
			ciphertext,
			prefix,
			assigned_id,
		})
	}
}

pub struct ServerResponseHash<'a> {
	candidate: crate::pqxdh::ServerRegistrationCandidate,
	binding: RegistrationBinding,
	kernel: crate::ratchet::ConcreteRatchetKernel,
	ciphertext: &'a [u8],
	prefix: [u8; RESPONSE_PREFIX_LEN],
	assigned_id: [u8; 8],
}

impl<'a> ServerResponseHash<'a> {
	pub fn request(&self) -> HashRequest<'_> {
		HashRequest::Triple([&self.prefix, self.ciphertext, &self.assigned_id])
	}

	pub fn resume(
		self,
		digest: Option<[u8; TRANSCRIPT_HASH_LEN]>,
	) -> Result<ServerResponseSigning<'a>, crate::pqxdh::ServerState> {
		let rejected = crate::pqxdh::server_abort_candidate(&self.candidate);
		Ok(ServerResponseSigning {
			candidate: self.candidate,
			binding: self.binding,
			kernel: self.kernel,
			ciphertext: self.ciphertext,
			input: build_signature_input(
				AuthRole::Server,
				&match digest {
					Some(digest) => digest,
					None => return Err(rejected),
				},
			),
		})
	}
}

pub struct ServerResponseSigning<'a> {
	candidate: crate::pqxdh::ServerRegistrationCandidate,
	binding: RegistrationBinding,
	kernel: crate::ratchet::ConcreteRatchetKernel,
	ciphertext: &'a [u8],
	input: [u8; SIGNATURE_INPUT_LEN],
}

impl<'a> ServerResponseSigning<'a> {
	pub fn request(&self) -> MldsaSigningRequest<'_> {
		MldsaSigningRequest {
			role: AuthRole::Server,
			public_key: self.binding.server_pin().public_key(),
			input: &self.input,
			context: SIGNING_CONTEXT,
		}
	}

	pub fn resume(
		self,
		signature: Option<&[u8]>,
	) -> Result<ServerResponseReady<'a>, crate::pqxdh::ServerState> {
		let rejected = crate::pqxdh::server_abort_candidate(&self.candidate);
		Ok(ServerResponseReady {
			candidate: self.candidate,
			binding: self.binding,
			kernel: self.kernel,
			ciphertext: self.ciphertext,
			signature: match signature {
				Some(signature) => match signature.try_into() {
					Ok(signature) => signature,
					Err(_) => return Err(rejected),
				},
				None => return Err(rejected),
			},
		})
	}
}

pub struct SignedResponseView<'a> {
	pub identity_key: &'a [u8; 32],
	pub ephemeral_key: &'a [u8; 32],
	pub kem_cipher_text: &'a [u8; 1088],
	pub key_id: u64,
	pub application_ciphertext: &'a [u8],
	pub signature: &'a [u8; MLDSA_SIGNATURE_LEN],
}

pub struct ServerResponseReady<'a> {
	candidate: crate::pqxdh::ServerRegistrationCandidate,
	binding: RegistrationBinding,
	kernel: crate::ratchet::ConcreteRatchetKernel,
	ciphertext: &'a [u8],
	signature: [u8; MLDSA_SIGNATURE_LEN],
}

impl ServerResponseReady<'_> {
	pub fn message(&self) -> SignedResponseView<'_> {
		SignedResponseView {
			identity_key: self.candidate.server_identity_public_key(),
			ephemeral_key: self.candidate.ephemeral_public_key(),
			kem_cipher_text: self.candidate.kem_ciphertext(),
			key_id: self.candidate.key_id(),
			application_ciphertext: self.ciphertext,
			signature: &self.signature,
		}
	}

	pub fn publish<Encoded>(
		self,
		encoded: Option<Encoded>,
	) -> Result<PublishedServerResponse<Encoded>, crate::pqxdh::ServerState> {
		let rejected = crate::pqxdh::server_abort_candidate(&self.candidate);
		let encoded = match encoded {
			Some(encoded) => encoded,
			None => return Err(rejected),
		};
		let binding = self.binding.finish(self.candidate.key_id());
		let (control, _) = crate::pqxdh::server_commit(self.candidate);
		Ok(PublishedServerResponse {
			control,
			binding,
			kernel: self.kernel,
			encoded,
		})
	}
}

pub struct PublishedServerResponse<Encoded> {
	control: crate::pqxdh::ServerState,
	binding: crate::session::SessionBinding,
	kernel: crate::ratchet::ConcreteRatchetKernel,
	encoded: Encoded,
}

impl<Encoded> PublishedServerResponse<Encoded> {
	pub fn into_parts(
		self,
	) -> (
		crate::pqxdh::ServerState,
		crate::session::SessionBinding,
		crate::ratchet::ConcreteRatchetKernel,
		Encoded,
	) {
		(self.control, self.binding, self.kernel, self.encoded)
	}
}
