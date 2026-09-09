"""Refresh the local proxy binding for the observed existing CPU assignment only."""
import datetime
import json
from pathlib import Path
from colab_cli.common import State
from colab_cli.state import SessionState

state = State()
name = 'exp016-development'
endpoint = 'm-s-kkb-usc1c0-3nv3p0bo2kg3y'
matches = [a for a in state.client.list_assignments() if a.endpoint == endpoint]
assert len(matches) == 1, 'Expected existing assignment absent; no changes made'
assert state.store.get(name) is None, 'Local binding exists; do not overwrite it'
assignment = matches[0]
state.store.add(SessionState(name=name, endpoint=endpoint,
    token=assignment.runtime_proxy_info.token, url=assignment.runtime_proxy_info.url))
receipt = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'session': name, 'endpoint': endpoint,
    'action': 'Restored local name/proxy binding for the observed existing assignment only. '
        'No allocation, VM restart, bootstrap, project file edit or proof rerun.',
    'runtime_contents_verified': False, 'credentials_in_receipt': False}
path = Path('/home/richman954/NDEA_Evolve_offruntime/exp016/evidence/CONTINUUM_PROXY_REBIND.json')
with path.open('x') as out:
    out.write(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
