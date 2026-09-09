"""Refresh only the already allocated Exp015 runtime proxy; never print tokens."""
from colab_cli.common import State
from colab_cli.state import SessionState

endpoint = 'm-s-kkb-ass1a0-1gts16oqjjhbw'
state = State()
matches = [a for a in state.client.list_assignments() if a.endpoint == endpoint]
if len(matches) != 1:
    raise RuntimeError('Expected exactly one existing Exp015 assignment; no runtime changed')
assignment = matches[0]
state.store.add(SessionState(
    name='exp015-independent-check', endpoint=assignment.endpoint,
    token=assignment.runtime_proxy_info.token, url=assignment.runtime_proxy_info.url,
    variant=assignment.variant.name, accelerator=assignment.accelerator.value,
    machine_shape=assignment.machine_shape.name))
print('Refreshed proxy for existing endpoint', assignment.endpoint)
print('No allocation, kernel restart, proof launch or backup destination change performed')
