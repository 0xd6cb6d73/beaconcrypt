# BeaconCrypt Modified PQXDH Registration Protocol

## 1. Scope

This specification covers the BeaconCrypt registration/key-establishment protocol through establishment of the initial symmetric ratchets. It includes:

- authenticated Beacon `InitKex` generation;
- server replay protection;
- the four X25519 contributions and ML-KEM contribution;
- root-secret derivation;
- directional symmetric-ratchet initialization;
- the server's first authenticated/committing ratchet record;
- authenticated assignment of the beacon's numeric key identifier;
- transactional server commit;
- terminal beacon success/failure semantics.

Subsequent ordinary symmetric-ratchet traffic is outside scope except where its first record forms part of registration.

The deterministic protocol control is implemented by `beaconcrypt-core`; concrete Ed25519, X25519, ML-KEM, HKDF, ChaCha20-Poly1305 and BLAKE2b operations are performed by the production adapter. 

---

# 2. Parties and long-term state

There are two protocol roles:

\[
S = \text{Server},\qquad B = \text{Beacon}.
\]

## 2.1 Server

The server has:

\[
(IK_S^{sk}, IK_S^{pk})
\]

an Ed25519 identity key pair, and a fixed numeric sender identifier

\[
sid_S \in \{0,\ldots,2^{64}-1\}.
\]

It additionally maintains:

\[
n_S
\]

the last allocated beacon key identifier,

\[
Peers_S : kid \mapsto (\text{beacon identity},\text{ratchet state}),
\]

and a persistent consumed-registration set

\[
Consumed_S \subseteq \{0,1\}^{512}.
\]

The identity identifier \(sid_S\) and allocation counter \(n_S\) are conceptually distinct: registrations advance \(n_S\), while records sent by the server continue to identify their sender using \(sid_S\). The implementation stores the consumed-registration set alongside server state. 

## 2.2 Beacon

At construction, the beacon is provisioned with the expected server binding

\[
SB_S=(IK_S^{pk},sid_S).
\]

The server public key is therefore pinned out-of-band.

The beacon generates:

\[
(IK_B^{sk},IK_B^{pk}) \leftarrow Ed25519.KeyGen(),
\]

\[
(PK_B^{sk},PK_B^{pk}) \leftarrow X25519.KeyGen(),
\]

\[
(KEM_B^{sk},KEM_B^{pk}) \leftarrow MLKEM768.KeyGen().
\]

The X25519 `prekey` and ML-KEM key pair exist only while registration is pending; they are not retained in an established beacon. The one-time X25519 key is generated when the registration bundle is constructed, unless explicitly pregenerated through the compatibility API. The runtime state distinguishes `Fresh`, `FreshWithCoins`, `InitSent`, `Established`, and `Aborted`. 

---

# 3. Primitive notation

Let

\[
X25519(sk,pk)
\]

denote X25519 scalar multiplication.

Let

\[
XSK(IK^{sk}),\qquad XPK(IK^{pk})
\]

denote libsodium's Ed25519-to-X25519 secret/public-key conversions.

Let

\[
Sign_{sk}(x)
\]

denote the libsodium Ed25519 attached-signature representation `signature || x`.

Let

\[
Encap(pk)\rightarrow(ct,ss)
\]

and

\[
Decap(sk,ct)\rightarrow ss
\]

denote ML-KEM-768.

Define:

\[
HKDF_{512}(x,info,L)
=
Expand_{SHA512}
(
Extract_{SHA512}(\varnothing,x),
info,
L
).
\]

BeaconCrypt uses the fixed domain strings

\[
INFO_{PQ}
=
\texttt{"BeaconcryptPqxdh\_CURVE25519\_SHA-512\_ML-KEM-768"}
\]

of length 46, and

\[
INFO_R
=
\texttt{"SymRatchet\_HKDF\_SHA-512\_CHACHA20\_POLY1305"}
\]

of length 41. 

---

# 4. Authenticated public-key encodings

The protocol assigns explicit algorithm and key-role domains.

Define:

\[
Tag_{sig}(pk)=
01_{16}\parallel pk.
\]

For X25519:

\[
Tag_X(role,pk)
=
04_{16}\parallel role\parallel pk,
\]

where

\[
role_{pre}=80_{16},
\qquad
role_{otk}=81_{16}.
\]

For ML-KEM-768:

\[
Tag_{PQ}(pk)
=
03_{16}\parallel pk.
\]

Thus:

\[
|Tag_{sig}|=33,
\]

\[
|Tag_X|=34,
\]

\[
|Tag_{PQ}|=1185.
\]

The algorithm/type tags occupy the low half of the byte domain while the X25519 role tags occupy the high half. Prekey and one-time X25519 values therefore cannot be substituted for one another while retaining a valid field-specific encoding. 

---

# 5. Beacon registration initiation

From the `Fresh` state, generate:

\[
(OT_B^{sk},OT_B^{pk})\leftarrow X25519.KeyGen().
\]

The beacon constructs the unsigned logical `InitKex`:

\[
I_B = Tag_{sig}(IK_B^{pk}),
\]

\[
P_B = Tag_X(role_{pre},PK_B^{pk}),
\]

\[
O_B = Tag_X(role_{otk},OT_B^{pk}),
\]

\[
Q_B = Tag_{PQ}(KEM_B^{pk}).
\]

The wire message is:

\[
M_1 =
\operatorname{InitKex}
\left(
I_B,
Sign_{IK_B^{sk}}(P_B),
Sign_{IK_B^{sk}}(O_B),
Sign_{IK_B^{sk}}(Q_B)
\right).
\]

These are exactly the four Cap'n Proto fields `identityKey`, `preKey`, `oneTimeKey`, and `pqKey`; the latter three use attached signatures. 

The transition is affine:

\[
B_{Fresh}
\xrightarrow{\;M_1\;}
B_{InitSent}.
\]

No second registration bundle can be emitted from `InitSent`. 

---

# 6. Server validation of `InitKex`

On receiving \(M_1\), the server:

1. parses \(I_B\) as an Ed25519-tagged 32-byte public key;
2. obtains \(IK_B^{pk}\);
3. verifies the attached signatures on \(P_B,O_B,Q_B\) under \(IK_B^{pk}\);
4. validates:
   \[
   P_B=04\parallel80\parallel PK_B^{pk},
   \]
   \[
   O_B=04\parallel81\parallel OT_B^{pk},
   \]
   \[
   Q_B=03\parallel KEM_B^{pk}.
   \]

Failure of any signature, type tag, role tag, length, or key parse rejects the registration. The core explicitly revalidates the type and role encodings after the adapter has verified the signatures.  

Define the semantic registration identifier:

\[
RID =
IK_B^{pk}\parallel OT_B^{pk}.
\]

Hence:

\[
|RID|=64\text{ bytes}.
\]

No hash is used for this identifier; replay classification uses exact byte equality. 

The server requires:

\[
RID\notin Consumed_S.
\]

Otherwise:

\[
\operatorname{Reject}(\textsf{RegistrationReplay}).
\]

---

# 7. Server PQXDH computation

For a fresh registration, the server generates:

\[
(E_S^{sk},E_S^{pk})\leftarrow X25519.KeyGen()
\]

and

\[
(CT_{KEM},SS)\leftarrow Encap(KEM_B^{pk}).
\]

Define converted identity keys:

\[
IK_{S,X}^{sk}=XSK(IK_S^{sk}),
\]

\[
IK_{B,X}^{pk}=XPK(IK_B^{pk}).
\]

The server computes:

\[
DH_1
=
X25519(IK_{S,X}^{sk},PK_B^{pk}),
\]

\[
DH_2
=
X25519(E_S^{sk},IK_{B,X}^{pk}),
\]

\[
DH_3
=
X25519(E_S^{sk},PK_B^{pk}),
\]

\[
DH_4
=
X25519(E_S^{sk},OT_B^{pk}).
\]

This is the exact ordering used by the production server adapter. 

The protocol rejects if any

\[
DH_i=0^{256}.
\]

---

# 8. PQXDH root transcript and root secret

Define:

\[
F=FF_{16}^{32}.
\]

The 192-byte PQXDH input is:

\[
IKM_{PQ}
=
F
\parallel DH_1
\parallel DH_2
\parallel DH_3
\parallel DH_4
\parallel SS.
\]

Every component following the padding is 32 bytes. The exact ordering and all-zero-DH rejection are owned by the verified core. 

The derived session root is

\[
DS
=
HKDF_{512}
(
IKM_{PQ},
INFO_{PQ},
32
).
\]

The production adapter uses HKDF-SHA-512 with no salt, expands to 32 bytes, and zeroizes the 192-byte root transcript after the call. 

After this succeeds, the server permanently records:

\[
Consumed_S
:=
Consumed_S\cup\{RID\}.
\]

This occurs **before construction of the response**. Consequently, if response construction later fails or its pending token is dropped, replaying the same `InitKex` remains forbidden.  

---

# 9. Associated data

Define:

\[
AD =
Tag_{sig}(IK_S^{pk})
\parallel
Tag_{sig}(IK_B^{pk})
\parallel
INFO_{PQ}
\parallel
INFO_R.
\]

Its size is exactly:

\[
33+33+46+41=153\text{ bytes}.
\]

The order is always **server identity first, beacon identity second**. 

---

# 10. Initial symmetric-ratchet derivation

Expand \(DS\) in the symmetric-ratchet domain:

\[
R_0
=
HKDF_{512}
(
DS,
INFO_R,
64
).
\]

Let:

\[
L=R_0[0..32),
\qquad
R=R_0[32..64).
\]

The directional chains are assigned:

### Server

\[
CK_{S\rightarrow B}^{0}=L,
\]

\[
CK_{B\rightarrow S}^{0}=R.
\]

### Beacon

\[
CK_{B\rightarrow S}^{0}=R,
\]

\[
CK_{S\rightarrow B}^{0}=L.
\]

Thus the roles are complementary by construction. The core owns the 64-byte request/response type and the left/right role ordering; the adapter only executes HKDF-SHA-512.  

Both initial ratchet sequence counters are zero. 

---

# 11. Server key-ID allocation

Let the current server allocation state be \(n_S\).

The next beacon identifier is:

\[
kid_B=n_S+1
\]

provided:

\[
n_S\neq 2^{64}-1
\]

and

\[
kid_B\notin dom(Peers_S).
\]

Counter exhaustion produces `KeyIdExhausted`; an occupied proposed identifier produces `KeyIdCollision`. No wrapping is permitted. 

At this stage the assignment is still provisional.

---

# 12. Authenticated key-ID confirmation

Define the fixed-width binding:

\[
Bind(kid_B)=LE64(kid_B).
\]

Let \(M_{app}\) be the optional initial server application message. If none is provided:

\[
M_{app}=FF_{16}.
\]

An explicitly supplied empty application message is rejected.

The plaintext of the first server ratchet record is:

\[
P_0
=
LE64(kid_B)
\parallel
M_{app}.
\]

Therefore the assigned identifier is not authenticated merely by the clear `keyId` field in `KexResponse`; it is independently carried inside the encrypted initial record. 

---

# 13. Initial server record

For an honest implementation run, the server consumes the first send-ratchet step.

Starting with

\[
CK=CK_{S\rightarrow B}^{0},
\]

compute:

\[
O
=
HKDF_{512}(CK,INFO_R,76).
\]

Partition:

\[
K_1=O[0..32),
\]

\[
CK_{S\rightarrow B}^{1}=O[32..64),
\]

\[
N_1=O[64..76).
\]

The first allocated send sequence is

\[
seq=1.
\]

Ratchet derivations are explicitly partitioned as `key || next_chain || nonce`, and send sequence allocation increments the initial zero counter before sealing.  

Compute detached ChaCha20-Poly1305:

\[
(CT,T)
=
ChaCha20Poly1305.Seal
(
K_1,N_1,AD,P_0
).
\]

BeaconCrypt then computes its CTX commitment:

\[
T^*
=
BLAKE2b_{512}
(
K_1
\parallel N_1
\parallel AD
\parallel T
\parallel LE64(seq)
\parallel LE64(sid_S)
).
\]

The transmitted record ciphertext is:

\[
CT^*=CT\parallel T\parallel T^*.
\]

The `CryptoFrame` contains:

\[
CF_0=
(
keyId=sid_S,\;
seq=1,\;
cipherText=CT^*
).
\]

The commitment binds the key, nonce, associated data, base AEAD tag, sequence and **sender** identifier; the plaintext is bound transitively by the AEAD opening/tag.  

---

# 14. `KexResponse`

The server sends:

\[
M_2=
\operatorname{KexResponse}
(
IK_S^{pk},
E_S^{pk},
CT_{KEM},
CF_0,
kid_B
).
\]

On the wire these are:

- `identityKey = IK_S^{pk}`;
- `ephemeralKey = E_S^{pk}`;
- `kemCipherText = CT_KEM`;
- `appCipherText = serialized CF_0`;
- `keyId = kid_B`.

Unlike the tagged `InitKex.identityKey`, the `KexResponse.identityKey` production field contains the raw 32-byte Ed25519 public key.  

Only after the initial record has been encrypted and the complete response successfully serialized does the server commit:

\[
n_S:=kid_B
\]

and

\[
Peers_S[kid_B]
:=
(IK_B^{pk},AD,\text{server ratchet}).
\]

Failure before this commit leaves the peer map and allocation counter unchanged, although \(RID\) remains consumed. 

---

# 15. Beacon processing of `KexResponse`

The beacon must be in state:

\[
B_{InitSent}.
\]

It parses:

\[
IK_{S,r}^{pk},
E_S^{pk},
CT_{KEM},
CF,
kid_B.
\]

It computes:

\[
SS'=Decap(KEM_B^{sk},CT_{KEM}).
\]

Let:

\[
IK_{S,X}^{pk}=XPK(IK_{S,r}^{pk}),
\]

\[
IK_{B,X}^{sk}=XSK(IK_B^{sk}).
\]

The beacon computes:

\[
DH'_1
=
X25519(PK_B^{sk},IK_{S,X}^{pk}),
\]

\[
DH'_2
=
X25519(IK_{B,X}^{sk},E_S^{pk}),
\]

\[
DH'_3
=
X25519(PK_B^{sk},E_S^{pk}),
\]

\[
DH'_4
=
X25519(OT_B^{sk},E_S^{pk}).
\]

These are the role-reversed computations corresponding exactly to the four server contributions. 

Before constructing a registration candidate the beacon requires:

\[
IK_{S,r}^{pk}=IK_S^{pk},
\]

where the right-hand value is the server identity retained from its original pinned `ServerBinding`. 

It then derives:

\[
IKM'_{PQ}
=
FF^{32}
\parallel DH'_1
\parallel DH'_2
\parallel DH'_3
\parallel DH'_4
\parallel SS',
\]

\[
DS'=HKDF_{512}(IKM'_{PQ},INFO_{PQ},32),
\]

and initializes its complementary ratchets from \(DS'\).

---

# 16. Beacon registration acceptance

The beacon attempts to open `appCipherText` using its freshly initialized server-to-beacon receive ratchet and:

\[
AD =
Tag_{sig}(IK_S^{pk})
\parallel Tag_{sig}(IK_B^{pk})
\parallel INFO_{PQ}
\parallel INFO_R.
\]

The ratchet record must satisfy all ordinary BeaconCrypt record checks, including:

1. successful ratchet sequence admission;
2. `CryptoFrame.keyId = sid_S`;
3. valid CTX commitment;
4. valid ChaCha20-Poly1305 authentication under the selected ratchet material.

The implementation's **honest server** emits sequence \(1\). The beacon acceptance code, however, is defined through the general receive-ratchet transition rather than an explicit `seq == 1` test. Therefore the formal acceptance relation should be stated as “a valid admissible initial receive-ratchet record,” not artificially restricted to sequence 1. 

Let successful decryption return:

\[
P=b\parallel M,
\]

where:

\[
|b|=8,\qquad |M|>0.
\]

The beacon then requires:

\[
b=LE64(kid_B),
\]

where \(kid_B\) is the clear `KexResponse.keyId`, and independently requires that the authenticated record sender be:

\[
sid_S.
\]

The core transition is:

\[
AuthenticateCandidate
(
candidate,
authenticatedSender,
b
)
\]

and succeeds iff:

\[
authenticatedSender=sid_S
\]

and

\[
b=LE64(candidate.assignedKeyId).
\]

Only the resulting `AuthenticatedBeaconRegistration` typestate can be passed to `beacon_commit`. 

Immediately before final commitment, production additionally rechecks that the retained server public key and numeric server identifier still equal the authenticated core binding. 

---

# 17. Successful establishment

If all preceding checks succeed:

\[
B_{InitSent}
\xrightarrow{M_2}
B_{Established}.
\]

The beacon stores:

\[
kid_B,
\]

\[
SB_S=(IK_S^{pk},sid_S),
\]

\[
AD,
\]

and the initialized/advanced symmetric ratchet.

The registration-specific:

\[
PK_B^{sk},
\quad
OT_B^{sk},
\quad
KEM_B^{sk}
\]

are no longer represented in the established runtime state.

The corresponding public/private registration keypairs therefore become logically unavailable after establishment. The implementation tests this explicitly. Physical memory erasure is a separate implementation assumption, not a protocol-core theorem.  

---

# 18. Failure semantics

Registration is deliberately one-shot.

For a beacon in `InitSent`, **any failure** while processing the response causes:

\[
B_{InitSent}\rightarrow B_{Aborted}.
\]

This includes, inter alia:

- malformed response;
- invalid ML-KEM ciphertext;
- failed identity-key conversion;
- invalid/all-zero DH;
- pinned server identity mismatch;
- HKDF failure;
- invalid initial ratchet record;
- CTX failure;
- AEAD authentication failure;
- wrong authenticated sender ID;
- malformed authenticated plaintext;
- assigned-key-ID binding mismatch.

`Aborted` cannot restart registration. Entering it also drops the registration prekey, one-time key and ML-KEM key material from the beacon state. 

On the server, by contrast:

- accepting a registration consumes \(RID\);
- building the response is provisional;
- peer/counter state is committed only after encryption and serialization;
- aborting response construction preserves the old peer/counter state;
- but \(RID\) remains consumed.

This intentionally gives:

\[
\text{consume replay token}
\prec
\text{response construction}
\prec
\text{peer commit}.
\]

---

# 19. Honest agreement relation

Under the primitive-correctness assumptions:

\[
Decap(KEM_B^{sk},CT_{KEM})=SS,
\]

and X25519 agreement,

\[
DH'_i=DH_i\qquad i=1,\ldots,4,
\]

the two parties obtain:

\[
IKM'_{PQ}=IKM_{PQ},
\]

therefore:

\[
DS'=DS.
\]

Consequently:

\[
AD_B=AD_S,
\]

and the initial ratchet chains satisfy:

\[
CK^{0}_{S.send}=CK^{0}_{B.recv},
\]

\[
CK^{0}_{S.recv}=CK^{0}_{B.send}.
\]

On successful beacon commitment:

\[
kid_B^{Beacon}=kid_B^{Server},
\]

and both sides agree on the ordered identity pair:

\[
(IK_S^{pk},IK_B^{pk}).
\]

These are essentially the post-validation correspondence properties already proved for the extracted PQXDH core under explicit primitive/agreement assumptions. 

---

# 20. State-transition summary

The beacon machine is:

\[
Fresh
\rightarrow
InitSent
\rightarrow
\begin{cases}
Established & \text{iff complete authenticated finish succeeds}\\
Aborted & \text{otherwise}.
\end{cases}
\]

There is no transition out of `Established` or `Aborted` back into registration.

The server machine for one registration is:

\[
(S,Consumed)
\xrightarrow[\;RID\notin Consumed\;]{M_1}
(S,Consumed\cup\{RID\},Pending)
\]

followed by:

\[
Pending
\xrightarrow[\text{response creation succeeds}]{}
(S',EstablishedPeer)
\]

or:

\[
Pending
\xrightarrow[\text{failure}]{}
S
\]

while retaining:

\[
RID\in Consumed.
\]

This captures the implementation's distinction between replay consumption and transactional peer publication. 

---

# 21. Principal modifications relative to vanilla PQXDH

The implemented BeaconCrypt construction can therefore be summarized as:

\[
\boxed{
\text{PQXDH}
+
\text{explicit principal roles}
+
\text{role-tagged signed X25519 keys}
+
\text{mandatory one-shot registration}
+
\text{persistent replay consumption}
+
\text{symmetric-ratchet bootstrap}
+
\text{authenticated numeric-ID assignment}
+
\text{committing initial record}
}
\]

More concretely, relative to generic Signal PQXDH:

1. **The roles are fixed:** the prekey-owning party is a Beacon and the initiator/responding party is the Server in the BeaconCrypt registration semantics.
2. **The server identity is pinned in the beacon.**
3. **Prekey and one-time X25519 keys have distinct authenticated role tags.**
4. **There is exactly one registration attempt per beacon state machine.**
5. **The ML-KEM key is registration-local and becomes unavailable after completion.**
6. **Replay is tracked by exact**
   \[
   RID=IK_B^{pk}\parallel OT_B^{pk}.
   \]
7. **The server allocates a checked numeric identity to the beacon.**
8. **That identity is authenticated inside the first encrypted ratchet record rather than trusted from an unauthenticated response field.**
9. **Registration is complete only after successful opening of that record.**
10. **The PQXDH output immediately initializes complementary symmetric ratchets.**
11. **The first record uses BeaconCrypt's CTX-style strong commitment as well as ChaCha20-Poly1305.**
12. **Server peer publication is transactional; replay consumption occurs earlier and survives response failure.**

This specification describes the protocol implemented by the current `lean` branch. It does not by itself assert computational security of the primitive implementations or active-quantum authentication; those remain separate security claims and assumptions.
