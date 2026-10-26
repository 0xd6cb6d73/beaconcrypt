# Pure admission factoring for the strong-secrecy receiver

Status: separate scratch derivative for review. The original exact Kr3 receiver and every unsuccessful solver diagnostic remain unchanged. A verdict for this derivative can be transferred only after the complete local operational equivalence below is checked against its frozen inputs. It is not a change of receive capability, test gate, bound or returned observation.

For b2s let `a=1`, `b=2` and initial receive counter zero; for s2b let `a=2`, `b=3` and initial counter one. Retain the exact original parser, expected sender, fixed owner/root/AD/material fields, public call label and original raw frame. The derivative moves only the following pure state-dependent material selection into `Admission`:

| Original guard | Material and successful next state |
| --- | --- |
| `t<=r` and `t=a` and `cached` | `(m1,r,false)` |
| `t<=r` and not the preceding conjunction | No opening; unchanged state and None. |
| `t>r` and `t=a` | `(m1,a,cached)` |
| `t>r` and `t=b` and `r=a-1` | `(m2,b,true)` |
| `t>r` and `t=b` and `r!=a-1` | `(m2,b,cached)` |
| `t>r` and neither near target | No opening; unchanged state and None. |

The cases partition every natural `t,r` and both cache flags, including unreachable combinations. No invariant limiting r or cache is needed. The original process executes `open_frame` exactly in the four opening rows, with `fs_seq(a)` or `fs_seq(b)`. In those rows `t` equals that same literal, so the derivative's single `open_frame(material,ad,fs_seq(t),sender,original_frame)` is exactly the original primitive input. All other rows perform no open in either process.

The plan helper returns an explicit Some/None data term for every input. It cannot fail and terminate the process implicitly. Failure of the original frame parser, absence of a plan, and actual open failure each has an explicit None reply followed by the unchanged complete continuation. Open failure does not install the candidate next counter/cache. Successful open retains the exact recovered private plaintext, emits `FsReceived` then `FsReceivedFrame` with the original target/tuple/frame, returns the same public success marker, and invokes the exact full continuation with the successful next state. All other fixed arguments and the original call label remain unchanged.

Induct through the same three receive slots. At each input, the public guard chooses the same frame/owner, the partition chooses the same primitive call or no call, and the two private states and continuations are equal after either result. Thus both processes have the same complete symbolic reduction/observation trace modulo terminating pure local plan reductions. Ghost event order and multiplicity are also equal; the private plan constructors are never published. Their public constructor syntax adds no secret destructor and can be expressed using the already public tuple/option encoding. This is an exact symbolic program factoring, not a computational generator interchange or a rule declaring work free.

The positive experiment still contains the original full registration, all accepts/builds, AnyPin, exact identities/IDs, two send allocations, caller-selected alternatives/failed seals, chain disclosures and three receiver inputs. No terminal branch or replay failure is deleted. Send/accept/build `[precise]` annotations are inherited from the original strong probe; this derivative does not add receive precision. The same single hidden bit and private-application/no-echo scope remain. The exact process comparator and independently reviewed branch table must be maintained before any derivative result is counted as evidence for the original interface.
