#!/usr/bin/env python3
"""Test the compiled JSON boundary against contract fixtures and explicit cases."""
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/hono-lean-json'
CORPUS = json.loads((ROOT / 'examples/v1.json').read_text())


def run(value, *, raw=False):
    text = value if raw else json.dumps(value, ensure_ascii=False)
    completed = subprocess.run([str(EXE)], input=text, capture_output=True, text=True, check=True)
    assert not completed.stderr, completed.stderr
    return json.loads(completed.stdout)


def category(value):
    return value['error']['category']


def route(pattern, method='GET', handler='label'):
    return dict(method=method, pattern=pattern, handler=handler)


def lookup(path='/', method='GET'):
    return dict(op='lookup', request=dict(method=method, path=path))


def scenario(routes=(), steps=()):
    return dict(routes=list(routes), steps=list(steps))


lookups = registrations = 0
for case in CORPUS['scenarios']:
    output = run(case)
    assert len(output['results']) == len(case['steps']), case['id']
    count = len(case['routes'])
    for step, actual in zip(case['steps'], output['results']):
        if step['op'] == 'lookup':
            assert actual == {'matches': step['expected']}, (case['id'], step, actual)
            lookups += 1
        else:
            assert actual == {'registration': step['expectedRegistration']}, (case['id'], actual)
            count += 1
            registrations += 1
    assert output['nextRegistration'] == count, case['id']

for case in CORPUS['rejected']:
    if case['target'] == 'route':
        output = run(scenario([route('/valid'), case['input']], [lookup('/valid')]))
        assert category(output) == case['expectedError'], case['id']
        assert set(output) == {'error'}, 'Failed build exposed partial results or counter'
    else:
        output = run(scenario([], [dict(op='lookup', request=case['input'])]))
        assert category(output['results'][0]) == case['expectedError'], case['id']
        assert output['nextRegistration'] == 0

# Each invalid route is also attempted after a successful build. The next valid
# registration must still receive 1, with the old route preserved and no hole.
invalid_routes = [case['input'] for case in CORPUS['rejected'] if case['target'] == 'route']
for bad in invalid_routes:
    output = run(scenario([route('/old')], [dict(op='register', route=bad),
        dict(op='register', route=route('/new')), lookup('/old'), lookup('/new')]))
    assert category(output['results'][0]) == 'invalid_route'
    assert output['results'][1] == {'registration': 1}
    assert output['results'][2] == {'matches': [dict(registration=0, handler='label', params={})]}
    assert output['results'][3] == {'matches': [dict(registration=1, handler='label', params={})]}
    assert output['nextRegistration'] == 2

# Additional grammar boundaries: no hidden normalizing, wildcard ambiguity, or
# duplicate-name acceptance; ordinary opaque labels are deliberately unrestricted.
bad_patterns = ['', '//', '/a/', '/a//b', '/a/*/*', '/a/*/b', '/a/**', '/a*',
    '/:a/:a', '/:1id', '/:', '/a/:id?', '/a/:id{a}', '/a.b', '/a%20b',
    '/étudiant', '/ a', '/a\\b', '/a\nb', ' /a', 'https://example.test/a']
for pattern in bad_patterns:
    assert category(run(scenario([route(pattern)]))) == 'invalid_route', pattern
bad_paths = ['', '//', '/a/', '/a//b', '/a?b', '/a#b', '/a%2Fb', '/.', '/..',
    '/a.b', '/é', '/ a', '/a\\b', '/a\nb', ' /a', 'https://example.test/a', '/*', '/:id']
for path in bad_paths:
    output = run(scenario([], [lookup(path)]))
    assert category(output['results'][0]) == 'invalid_request', path

label = '任意\n"quoted"\\label'
output = run(scenario([route('/:__proto__/:constructor/*', method='CUSTOM', handler=label)],
    [lookup('/alpha/beta/x/y', method='CUSTOM'), lookup('/', method='CUSTOM')]))
assert output['results'] == [
    {'matches': [dict(registration=0, handler=label, params={'__proto__': 'alpha', 'constructor': 'beta'})]},
    {'matches': []}]
# Standard JSON escaping is transport decoding; it is not URL decoding.
escaped = r'{"routes":[{"method":"GET","pattern":"\u002fgrade_2\u002f:id","handler":""}],"steps":[{"op":"lookup","request":{"method":"GET","path":"\u002fgrade_2\u002fskill-7"}}]}'
assert run(escaped, raw=True)['results'] == [{'matches': [dict(registration=0, handler='', params={'id': 'skill-7'})]}]

for raw in ['', '{', '{"routes": [], "steps": []} trailing', '[', 'NaN']:
    assert category(run(raw, raw=True)) == 'invalid_input'
for envelope in [None, [], 1, 'text', True]:
    assert category(run(envelope)) == 'invalid_input'
for envelope in [dict(routes=[]), dict(routes=[], steps={}), dict(routes=[], steps=None)]:
    assert category(run(envelope)) == 'invalid_input'
for values in [None, {}, 'routes', 1]:
    assert category(run(dict(routes=values, steps=[]))) == 'invalid_route'
for bad in [None, {}, {'method': 'GET', 'pattern': '/'},
            {'method': 1, 'pattern': '/', 'handler': ''},
            {'method': 'GET', 'pattern': [], 'handler': ''},
            {'method': 'GET', 'pattern': '/', 'handler': False}]:
    assert category(run(scenario([bad]))) == 'invalid_route'
for bad in [None, {}, {'method': 'GET'}, {'method': 1, 'path': '/'}, {'method': 'GET', 'path': []}]:
    output = run(scenario([], [dict(op='lookup', request=bad)]))
    assert category(output['results'][0]) == 'invalid_request'
output = run(scenario([], [None, {}, dict(op='unknown'), dict(op='register'), dict(op='lookup'),
    dict(op='register', route=route('/')), lookup('/')]))
assert [category(x) for x in output['results'][:5]] == [
    'invalid_input', 'invalid_input', 'invalid_input', 'invalid_route', 'invalid_request']
assert output['results'][5] == {'registration': 0}
assert output['results'][6] == {'matches': [dict(registration=0, handler='label', params={})]}
assert output['nextRegistration'] == 1

print(f'CLI adapter tests passed: {len(CORPUS["scenarios"])} scenarios, {lookups} lookups, '
      f'{registrations} append events, {len(CORPUS["rejected"])} rejection fixtures, '
      f'{len(invalid_routes)} failed-register sequences, plus grammar/JSON/formatting checks.')
