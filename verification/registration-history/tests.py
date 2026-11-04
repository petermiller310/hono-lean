#!/usr/bin/env python3
"""Prefix storage and history/lookup conformance using the existing exact-source runners."""
import itertools
from pathlib import Path
import random
import runpy
import unittest

ROOT = Path(__file__).resolve().parents[2]
previous = runpy.run_path(str(ROOT/'verification/methods-loop-initial/tests.py'))
invoke, native, model = (previous[name] for name in ['invoke', 'native', 'model'])
units, registration, fixture, unique, encoded = (previous[name] for name in ['units', 'registration', 'fixture', 'unique', 'encoded'])
HONO = previous['HONO']


def oracle(case):
    result = previous['oracle'](case)
    start = case.get('startOrder', 0)
    result['scores'] = [start+index+1 for index in range(len(case['registrations']))]
    result['order'] = start+len(case['registrations'])
    result['registrationSteps'] = [dict(returned=index+1, count=index+1, order=start+index+1, score=start+index+1,
        method=row['method'], handler=encoded(row['handlerCode']) if 'handlerCode' in row else dict(kind='number', value=index),
        keys=unique(row['names']), oldRowsKept=True, oldRecordsKept=True, oldKeysKept=True,
        rowFresh=True, recordFresh=True, keysFresh=True, privateArrayKept=True)
        for index, row in enumerate(case['registrations'])]
    return result


class RegistrationHistoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = invoke(['python3', 'verification/methods-loop-initial/source.py', '--hono', str(HONO)])
        if result.returncode:
            raise AssertionError(result.stdout+result.stderr)

    def compare(self, cases):
        expected = [oracle(case) for case in cases]
        packet = dict(cases=cases, observePrefixes=True)
        self.assertEqual(native(packet)['results'], expected)
        self.assertEqual(model(packet), expected)

    def test_every_registration_prefix_and_equal_user_handlers(self):
        choices = [registration('GET', 'id', 'name'), registration('ALL', 'id', 'id', 'name'),
                   registration('POST'), registration('__proto__', 'constructor')]
        for choice in choices:
            choice['handlerCode'] = 'text'
        cases = [fixture(list(sequence)) for length in range(6) for sequence in itertools.product(choices, repeat=length)]
        for index, case in enumerate(cases):
            case['startOrder'] = [-7, 0, 23][index % 3]
        self.compare(cases)
        print(f'Registration-prefix audit: {len(cases)} exhaustive histories with equal supplied handler values', flush=True)

    def test_generated_frames_keys_scores_and_empty_history(self):
        rng = random.Random(1729)
        alphabet = [units(name) for name in ['', 'id', 'name', '__proto__', 'constructor', 'params', '0', 'é', '\ud800']]
        methods = [units(name) for name in ['GET', 'POST', 'ALL', '', 'constructor', 'toString', '__proto__', '\ud800']]
        queries = [units(name) for name in ['GET', 'POST', 'ALL', '', '\ud800']]
        cases = []
        for _ in range(256):
            cases.append(dict(registrations=[dict(method=rng.choice(methods), handlerCode=rng.choice(['text', 'text', 'f', 'n', 'u', 'one']),
                              names=[rng.choice(alphabet) for _ in range(rng.randrange(14))]) for _ in range(rng.randrange(20))],
                              queries=[rng.choice(queries) for _ in range(rng.randrange(1, 4))], startOrder=rng.randrange(-1000, 1000),
                              nodeEntries=[[key, rng.choice(['u', 'n', 'f', 'z', 'empty', 'text', 'one'])] for key in alphabet],
                              parameterEntries=[[key, rng.choice(['u', 'n', 'f', 'z', 'empty', 'text', 'one'])] for key in alphabet],
                              parameterMode=rng.choice(['object', 'null', 'undefined'])))
        cases += [fixture([registration('ALL', 'id')]*96),
                  fixture([registration('GET', *[str(i) for i in range(96)]), registration('ALL', 'id', 'name')]),
                  fixture([], ('constructor', 'toString', '__proto__')),
                  fixture([dict(registration('GET', 'id'), handlerCode='f'), dict(registration('GET', 'name'), handlerCode='f')], ())]
        self.compare(cases)
        print(f'Registration-frame audit: {len(cases)} seeded/long/empty histories, UTF16 and repeated queries', flush=True)

    def test_registration_source_faults_reach_prefix_observations(self):
        source = (ROOT/'verification/methods-push/source.ts.txt').read_text()
        case = fixture([dict(registration('GET', 'id', 'name'), handlerCode='text'),
                        dict(registration('ALL', 'name', 'id'), handlerCode='text')])
        for fault in [source.replace('score: ++order', 'score: order'), source.replace('[...possibleKeys]', '[]'),
                      source.replace('        handler,', '        handler: null,')]:
            self.assertNotEqual(fault, source)
            packet = dict(cases=[case], observePrefixes=True, registrationSource=fault)
            observed = native(packet)['results']
            self.assertEqual(model(packet), observed)
            self.assertNotEqual(observed, [oracle(case)])

    def test_native_history_boundaries_and_returned_pairs(self):
        observed = native(dict(historyScope=True))['historyScope']
        self.assertEqual(observed, dict(unsafeScores=[9007199254740992]*2, unsafeOrder=9007199254740992,
            sameUserHandlerDistinctRecords=True,
            iteratorEffects=dict(oldScore=1, changedScore=-1, secondScore=2, count=2),
            actualNode=dict(counts=[2, 2], sameHandler=True, distinctFirstParams=True, freshNextParams=True,
                            priorIds=['one', 'one'], nextIds=['two', 'two'])))


if __name__ == '__main__':
    unittest.main(argv=['registration-history-tests'])
