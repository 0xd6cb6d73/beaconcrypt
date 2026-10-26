# Joint consistency of the Server-authentication contracts

The joint witness is an explicitly insecure mathematical instance. It checks that the new X25519 class law, scalar-spread bound and nonzero-honest agreement can hold together with the same source wiring, full HKDF equations and abstract message interface. It is not an implementation of any production primitive and makes no hardness, pseudorandomness or authentication claim about its toy functions.

## Complete finite DH construction

`PqxdhServerAuthWitnessDh` represents each 32-byte word by a 256-element Boolean function. A finite equivalence is chosen to send the all-zero wire word to the all-false function. Toy agreement XORs the two representations and forces coordinate zero to true. It then maps the complete result back to a 32-byte word. The equivalence is a mathematical choice, not a claimed efficient encoding or production byte layout.

The operation is symmetric and always nonzero. If two peers have equal outputs under one scalar, they agree at every coordinate except the forced one. They therefore have equal outputs under every scalar. Given a fixed peer and output, restoring the erased first scalar bit to false or true lists all possible scalar preimages. The checked finite-set inclusion bounds the complete fiber by two. This implies the approved bound of 64 on the actual uniform 32-byte scalar space without enumerating that space or assuming a distributional estimate.

Raw byte strings of length 32 keep their exact word. Other lengths normalize to zero. This makes the class law total on the abstract interface while leaving the source-width scalar sampler unchanged. It is only a convention of the witness.

## One primitive and message instance

`PqxdhServerAuthJointWitness` combines that agreement operation with the existing insecure HMAC/HKDF construction, attached-signature format, correct constant KEM and identity-like AEAD. Its converted identity scalar and public key agree with the same normalized toy interface. The joint identity's optional static DH uses that exact converted scalar; the separate scalar interface uses the same raw function. Neither a security premise nor a protocol acceptance premise supplies the wiring.

The HKDF witness retains both source labels and all 32-, 64- and 76-byte prefix relationships. Its root and full-output laws are inherited from the previously checked two-block HMAC construction. This is reuse of a functional consistency construction; no internals of HKDF-SHA-512, X25519, Ed25519, ML-KEM, ChaCha20-Poly1305 or BLAKE2b are being verified.

The abstract message codec remains the existing injective countable encoding, with read-back and successful-writing laws. It says nothing about Cap’n Proto or serialization, which remain outside the approved proof scope. The authentication experiments still have their explicitly disclosed programmable 192-byte Extract and shared CTX/BLAKE2b random-oracle idealizations. Showing the functional premises are jointly satisfiable does not show the associated reduction advantages are small, for this toy or for production.

## Joint hypotheses and live controls

`joint_witness` supplies one setup and one codec satisfying all control laws, the class law, scalar spread, root and full KDF correctness, zero KEM correctness error, functional effect-free decapsulation, and the existing `ReadWritable` law. Its proofs use those concrete objects throughout; they do not assemble unrelated witnesses for different premises. `ReadWritable` only asks that a frame returned by the reader can be written, not that arbitrary received bytes are canonical.

On this same instance, `seed_control_wins` reaches the original no-partner winning event with probability one when the Server seed is disclosed. `relay_zero` shows that the honest relay never meets the authentication-winning event, while `relay_accepts` proves that an admitted relay actually reaches Beacon acceptance. Thus the functional consistency witness also exercises both success and failure of the intended event. These are instances of the previously checked control theorems, with their KEM error reduced to zero; they do not change the headline experiment or its reveal policy.

The separate pre-seal-chain disclosure control and the remaining selected adaptive CTX composition are not established by this witness. No snapshot, persistence or production primitive implementation is modeled here.
