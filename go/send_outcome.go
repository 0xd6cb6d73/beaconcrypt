// SPDX-License-Identifier: 0BSD

package beaconcrypt

// SendOutcome distinguishes unchanged rejection from successful output and key
// consumption without output. Persistent results describe confirmed commits.
type SendOutcome uint32

const (
	SendRejected SendOutcome = iota
	SendSent
	SendConsumedWithoutOutput
)

// SendResult is returned by the explicit send APIs. Data and metadata are valid
// only for SendSent. State contains secret observational JSON for update calls;
// JSON outcome calls put their complete JSON in Data and leave State empty.
// A non-nil error suppresses the entire result, including uncertain commits.
type SendResult struct {
	Outcome SendOutcome
	Data    []byte
	State   string
	KeyID   uint64
	Seq     uint64
}

// Changed reports whether this attempt consumed a send key, even without output.
func (result *SendResult) Changed() bool {
	return result != nil && (result.Outcome == SendSent || result.Outcome == SendConsumedWithoutOutput)
}

func makeSendResult(outcome SendOutcome, data, state []byte, keyID, seq uint64) (*SendResult, error) {
	switch outcome {
	case SendRejected, SendConsumedWithoutOutput:
		if len(data) != 0 || len(state) != 0 || keyID != 0 || seq != 0 {
			return nil, ErrCrypto
		}
	case SendSent:
		if len(data) == 0 || seq == 0 {
			return nil, ErrCrypto
		}
	default:
		return nil, ErrCrypto
	}
	return &SendResult{Outcome: outcome, Data: data, State: string(state), KeyID: keyID, Seq: seq}, nil
}
