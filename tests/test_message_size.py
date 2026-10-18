# SPDX-License-Identifier: 0BSD

from beaconcrypt import MAX_MESSAGE_SIZE


def test_max_message_size_is_the_complete_wire_limit():
    assert isinstance(MAX_MESSAGE_SIZE, int)
    assert MAX_MESSAGE_SIZE == 32 * 1024 * 1024
