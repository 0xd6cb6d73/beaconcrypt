# Source record dispatch and exact record witnesses

`PqxdhRecordFactsOriginDispatch` connects the source Server and Beacon dispatchers to the local accepted-record and returned-ciphertext witnesses. The statements execute the unchanged dispatcher under the actual CTX service interpreter, retain its complete private poststate, and use the actual optional reply to select successful cases.

`ownerRun_accepted_tag` preserves the local receive witness through the actual publication callback with any tag. This matters because a routed Server receive carries no publication tag; the receiving peer comes from the header route and peer lookup. The wrapper does not replace that tag with a peer handle.

`serverReceive_accepted` identifies the peer actually selected by the header route and requires the corresponding stored peer to exist. `beaconReceive_accepted` retains the requested owner index. Both distinguish caller-known keys from hidden keys. In the hidden case, the accepted raw bytes decode to a frame matching a seal in the actual post-execution dictionary, at the installed slot and the physical opposite sending direction, with the actual returned plaintext. Missing and inactive owners, a missing Server or peer, and failed routing cannot supply the successful optional reply.

`serverSend_published` and `beaconSend_published` retain the requested sending handle. A returned ciphertext from a hidden kernel has a decoded frame matching an entry in the actual sending-coordinate dictionary. The proof uses the existing `FrameReadBack` codec contract to connect successful serialization to decoding. The caller-known branch remains explicit.

All five statements assume replay or random mode on every hidden coordinate and source control safety. They establish local dispatcher facts under those premises; they do not assume that a selected key is hidden. They make no new primitive, parser, deployment, or freshness assumption. No query costs are erased or bounded here: the execution, counters, caches, logs, and complete private poststate remain literal. The global source safety and ledger persistence joins, and the unpublished-record probability bound, are separate obligations.
