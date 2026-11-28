import threading

import pytest

from beaconcrypt import BeaconCryptRowServer, RowPersistenceError
from test_row_persistence import Database, create


def on_thread(function):
    """Run function on a new thread and return its result or raised exception."""
    outcome = {}

    def target():
        try:
            outcome["value"] = function()
        except BaseException as error:
            outcome["error"] = error

    thread = threading.Thread(target=target)
    thread.start()
    thread.join()
    return outcome


def committed_value(server):
    return server.transaction(lambda session: session.load(b"result") or b"absent")


def test_session_use_from_another_thread_raises_and_aborts_the_transaction(tmp_path):
    server, _ = create(tmp_path / "state.db")
    errors = []

    def operation(session):
        session.store(b"result", b"must not commit")
        outcome = on_thread(lambda: session.load(b"result"))
        errors.append(outcome.get("error"))
        # The owner thread keeps working, but the misuse still aborts the transaction.
        assert session.load(b"result") == b"must not commit"
        return b"ignored"

    with pytest.raises(RowPersistenceError) as failure:
        server.transaction(operation)
    assert isinstance(errors[0], RuntimeError)
    assert "thread" in str(errors[0])
    assert isinstance(failure.value.__cause__, RuntimeError)
    assert committed_value(server) == b"absent"
    server.close()


def test_retained_session_from_another_thread_reports_the_ended_callback(tmp_path):
    server, _ = create(tmp_path / "state.db")
    sessions = []
    assert (
        server.transaction(lambda session: sessions.append(session) or b"ok") == b"ok"
    )
    outcome = on_thread(lambda: sessions[0].load(b"result"))
    assert isinstance(outcome.get("error"), RuntimeError)
    assert "callback has ended" in str(outcome["error"])
    server.close()


class ReentrantDatabase(Database):
    session = None
    reentry = None

    def load(self, key):
        if self.session is not None:
            session, self.session = self.session, None
            try:
                session.load(b"nested")
            except BaseException as error:
                self.reentry = error
        return super().load(key)


def test_reentrant_session_use_from_a_store_callback_raises(tmp_path):
    database = ReentrantDatabase(tmp_path / "state.db")
    server = BeaconCryptRowServer.create(19, b"s" * 32, b"m" * 32, database, b"l" * 32)

    def operation(session):
        database.session = session
        session.load(b"result")
        return b"done"

    with pytest.raises(RowPersistenceError):
        server.transaction(operation)
    assert isinstance(database.reentry, RuntimeError)
    assert committed_value(server) == b"absent"
    server.close()
