import pytest

from beaconcrypt import (
    BeaconCryptBeacon,
    RowPersistenceError,
    RowRegistrationDecision,
    RowRegistrationError,
)
from test_row_persistence import create, register


def test_exact_application_result_recovers_unknown_commit_and_session_expires(tmp_path):
    server, database = create(tmp_path / "state.db")
    beacon, kid, _ = register(server)
    message = beacon.encrypt_message_to_server(b"inbound")
    sessions = []
    transitions = []

    def operation(session):
        sessions.append(session)
        saved = session.load(b"result")
        if saved is not None:
            return saved
        pending = session.decrypt_beacon_message(message)
        assert pending.changed
        assert (pending.message.key_id, pending.message.seq) == (kid, 1)
        transitions.append(pending.message.seq)
        response = b"exact application response: " + pending.message.data
        session.store(b"result", response)
        session.store(b"", b"")
        assert session.load(b"") == b""
        assert session.load(b"absent") is None
        return response

    database.fail_after_commit = True
    with pytest.raises(RowPersistenceError) as failure:
        server.transaction(operation)
    assert isinstance(failure.value.__cause__, OSError)
    with pytest.raises(RuntimeError, match="callback has ended"):
        sessions[0].load(b"result")
    database.fail_after_commit = False
    assert server.transaction(operation) == b"exact application response: inbound"
    assert transitions == [1]
    assert server.decrypt_beacon_message(message) is None
    assert server.transaction(lambda session: b"") == b""


def test_callback_and_caught_native_errors_roll_back_all_rows(tmp_path):
    server, database = create(tmp_path / "state.db")
    _, kid, _ = register(server)
    before = database.rows()
    failure = ValueError("application response encoding failed")

    def failed(session):
        session.store(b"pending", b"metadata")
        assert session.encrypt_to_beacon(b"pending", kid).changed
        raise failure

    with pytest.raises(RowPersistenceError) as raised:
        server.transaction(failed)
    assert raised.value.__cause__ is failure
    assert database.rows() == before

    def caught(session):
        assert session.encrypt_to_beacon(b"one", kid).changed
        with pytest.raises(RowPersistenceError) as twice:
            session.encrypt_to_beacon(b"two", kid)
        assert twice.value.code == "invalid_session"
        return b"ignored failure"

    with pytest.raises(RowPersistenceError) as raised:
        server.transaction(caught)
    assert raised.value.code == "invalid_session"
    assert database.rows() == before
    assert server.encrypt_to_beacon_with_metadata(b"retry", kid).seq == 2


def test_registration_phases_and_cached_application_response(tmp_path):
    server, database = create(tmp_path / "state.db")
    beacon = BeaconCryptBeacon(19, server.id_pk(), server.mldsa_public_key())
    registration = beacon.generate_registration()
    acceptance_sessions = []
    completed = []

    def accept(session):
        acceptance_sessions.append(session)
        cached = session.load(b"response")
        if cached is not None:
            return RowRegistrationDecision.return_result(cached)
        assert session.accept_registration(registration)
        session.store(b"request", b"accepted")
        return RowRegistrationDecision.continue_registration(b"initial")

    def complete(session, initial):
        with pytest.raises(RuntimeError, match="callback has ended"):
            acceptance_sessions[-1].load(b"request")
        assert session.load(b"request") == b"accepted"
        pending = session.complete_registration(initial)
        assert pending.changed and pending.message.seq == 1
        completed.append(pending.message.key_id)
        session.store(b"response", pending.message.data)
        return pending.message.data

    response = server.registration_transaction(accept, complete)
    assert beacon.process_initial_message(response) == b"initial"
    assert server.registration_transaction(accept, complete) == response
    assert len(completed) == 1
    database.fail_commit = True
    with pytest.raises(RowRegistrationError) as failed:
        server.registration_transaction(accept, complete)
    assert failed.value.phase == "acceptance"
    assert failed.value.code == "storage"
    assert isinstance(failed.value.__cause__, OSError)


def test_completion_failure_preserves_acceptance_and_application_marker(tmp_path):
    server, _ = create(tmp_path / "state.db")
    beacon = BeaconCryptBeacon(19, server.id_pk(), server.mldsa_public_key())
    registration = beacon.generate_registration()
    failure = ValueError("response encoding failed")

    def accept(session):
        assert session.accept_registration(registration)
        session.store(b"request", b"incomplete")
        return RowRegistrationDecision.continue_registration(b"")

    def complete(session, _):
        assert session.complete_registration(b"pending").changed
        raise failure

    with pytest.raises(RowRegistrationError) as raised:
        server.registration_transaction(accept, complete)
    assert raised.value.phase == "completion"
    assert raised.value.__cause__ is failure
    assert server.transaction(lambda session: session.load(b"request")) == b"incomplete"
    assert server.register_beacon(registration, b"replay") is None


def test_invalid_callback_result_rolls_back_and_invalidates_session(tmp_path):
    server, database = create(tmp_path / "state.db")
    before = database.rows()
    sessions = []

    def wrong_type(session):
        sessions.append(session)
        session.store(b"pending", b"value")
        return None

    with pytest.raises(RowPersistenceError) as raised:
        server.transaction(wrong_type)
    assert isinstance(raised.value.__cause__, TypeError)
    assert database.rows() == before
    with pytest.raises(RuntimeError, match="callback has ended"):
        sessions[0].store(b"late", b"value")


def test_explicit_empty_registration_payload_can_record_terminal_failure(tmp_path):
    server, _ = create(tmp_path / "state.db")
    beacon = BeaconCryptBeacon(19, server.id_pk(), server.mldsa_public_key())
    registration = beacon.generate_registration()

    def accept(session):
        assert session.accept_registration(registration)
        return RowRegistrationDecision.continue_registration(b"")

    def complete(session, context):
        assert context == b""
        pending = session.complete_registration(b"")
        assert pending.message is None and not pending.changed
        session.store(b"outcome", b"terminal failure")
        return b"terminal failure"

    assert server.registration_transaction(accept, complete) == b"terminal failure"
    assert (
        server.transaction(lambda session: session.load(b"outcome"))
        == b"terminal failure"
    )
    assert server.register_beacon(registration, b"retry") is None
