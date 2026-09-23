"""Fail-closed host evaluator for the generated native bodies used in this audit.

This is not a proved Clight interpreter. It uses an isolated 80-word object
image, binary32 operations, explicit RNG-word inputs, and no whole-game state.
Every tested result is independently checked against extracted pinned C.
"""
from dataclasses import dataclass
import importlib.util
from pathlib import Path
import re
import struct

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('rng_analysis', HERE.parent / 'ttc-cog-rng-sequence/analyze.py')
rng = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rng)


def bits(x):
    return struct.unpack('>I', struct.pack('>f', x))[0]


def single(x):
    return struct.unpack('>f', struct.pack('>f', x))[0]


def as_float(x):
    return struct.unpack('>f', struct.pack('>I', x))[0]


def integer(x):
    assert isinstance(x, int) and -(1 << 31) <= x < (1 << 31)
    return x


@dataclass(frozen=True)
class Pointer:
    space: str
    index: int = 0
    field: str = ''


class Returned(Exception):
    pass


class Break(Exception):
    pass


def coq_list(node):
    if node == 'nil':
        return []
    assert node[-1] == 'nil' and all(x == '::' for x in node[1::2])
    return node[:-1:2]


class Engine:
    def __init__(self, version):
        self.functions = {}
        self.texts = {}
        for unit, name in [('obj_behaviors_2', 'bhv_ttc_cog_update'),
                           ('obj_behaviors_2', 'bhv_ttc_spinner_update'),
                           ('obj_behaviors_2', 'approach_f32_ptr'),
                           ('obj_behaviors_2', 'random_mod_offset'),
                           ('behavior_script', 'random_sign')]:
            text = rng.generated_function(version, unit, name)
            self.texts[name] = text
            params = text.split('fn_params :=', 1)[1].split(';', 1)[0]
            names = re.findall(r"\((_[A-Za-z0-9']+),", params)
            self.functions['_' + name] = (names, rng.parse_body(text))
        text = (PROJECT / f'generated/{version}_obj_behaviors_2.v').read_text()
        table = text.split('Definition v_sTTCSpinnerSpeeds :=', 1)[1].split('\n|}.', 1)[0]
        self.speeds = [int(x) for x in re.findall(r'Init_int16 \(Int.repr (\d+)\)', table)]
        assert self.speeds == [200, 600, 200, 0]
        self.table_text = table

    def reset(self, words):
        self.memory = [0] * 80
        self.words = list(words)
        self.draws = []
        self.accesses = set()

    def load(self, p):
        assert isinstance(p, Pointer)
        if p.space == 'object':
            assert p.index == 0
            return p
        if p.space == '_sTTCSpinnerSpeeds':
            return self.speeds[p.index]
        assert p.space == 'raw' and 0 <= p.index < 80
        self.accesses.add(('read', p.index, p.field))
        value = self.memory[p.index]
        if p.field == '_asF32':
            return as_float(value)
        assert p.field in ('_asS32', '_asU32')
        return value if p.field == '_asU32' or value < 2**31 else value - 2**32

    def store(self, p, value):
        assert p.space == 'raw' and 0 <= p.index < 80
        self.accesses.add(('write', p.index, p.field))
        if p.field == '_asF32':
            self.memory[p.index] = bits(value)
        else:
            assert p.field in ('_asS32', '_asU32')
            self.memory[p.index] = int(value) & 0xffffffff

    def call(self, name, values):
        if name == '_random_u16':
            assert not values and len(self.draws) < len(self.words)
            word = self.words[len(self.draws)]
            assert 0 <= word <= 65535
            self.draws.append(word)
            return word
        names, body = self.functions[name]
        assert len(names) == len(values)
        temps = dict(zip(names, values))

        def expr(node):
            kind, *a = node
            if kind == 'Econst_int':
                assert a[0][0] == 'Int.repr'
                return integer(int(a[0][1]))
            if kind == 'Econst_single':
                assert a[0][0] == 'Float32.of_bits' and a[0][1][0] == 'Int.repr'
                return as_float(int(a[0][1][1]))
            if kind == 'Etempvar':
                return temps[a[0]]
            if kind == 'Evar':
                if a[0] == '_gCurrentObject':
                    return Pointer('object')
                if a[0] == '_gTTCSpeedSetting':
                    return 2
                assert a[0] == '_sTTCSpinnerSpeeds'
                return Pointer(a[0])
            if kind == 'Ederef':
                return self.load(expr(a[0]))
            if kind == 'Efield':
                p = expr(a[0])
                if a[1] == '_rawData':
                    assert p == Pointer('object')
                    return Pointer('raw')
                assert p == Pointer('raw') and a[1] in ('_asS32', '_asU32', '_asF32')
                return Pointer('raw', 0, a[1])
            if kind == 'Ecast':
                value = expr(a[0])
                if a[1] == 'tfloat':
                    return single(value)
                if a[1] == 'tint':
                    return integer(int(value))
                if a[1] == 'tshort':
                    value = int(value) & 65535
                    return value if value < 32768 else value - 65536
                raise ValueError(a[1])
            if kind == 'Eunop':
                value = expr(a[1])
                assert a[0] in ('Oneg', 'Onotbool')
                return -value if a[0] == 'Oneg' else int(not value)
            assert kind == 'Ebinop', kind
            op, left, right, typ = a
            x, y = expr(left), expr(right)
            if isinstance(x, Pointer):
                assert op == 'Oadd' and isinstance(y, int)
                return Pointer(x.space, x.index + y, x.field)
            if op in ('Oeq', 'Ogt', 'Oge', 'Olt', 'Ole'):
                return int({'Oeq': x == y, 'Ogt': x > y, 'Oge': x >= y,
                            'Olt': x < y, 'Ole': x <= y}[op])
            if op == 'Oadd': value = x + y
            elif op == 'Osub': value = x - y
            elif op == 'Omul': value = x * y
            elif op == 'Omod':
                assert x >= 0 and y > 0
                value = x % y
            else: raise ValueError(op)
            return single(value) if typ == 'tfloat' else integer(value)

        def stmt(node):
            if node == 'Sskip': return
            if node == 'Sbreak': raise Break()
            kind, *a = node
            if kind == 'Ssequence':
                stmt(a[0]); stmt(a[1])
            elif kind == 'Sset': temps[a[0]] = expr(a[1])
            elif kind == 'Sassign':
                assert a[0][0] == 'Ederef'
                self.store(expr(a[0][1]), expr(a[1]))
            elif kind == 'Sifthenelse': stmt(a[1] if expr(a[0]) else a[2])
            elif kind == 'Scall':
                assert a[1][0] == 'Evar'
                result = self.call(a[1][1], [expr(x) for x in coq_list(a[2])])
                if a[0] != 'None':
                    assert a[0][0] == 'Some'
                    temps[a[0][1]] = result
            elif kind == 'Sreturn':
                assert a[0][0] == 'Some'
                raise Returned(expr(a[0][1]))
            elif kind == 'Sswitch':
                label, cases, active = expr(a[0]), a[1], False
                try:
                    while cases != 'LSnil':
                        assert cases[0] == 'LScons' and cases[1][0] == 'Some'
                        active |= label == int(cases[1][1])
                        if active: stmt(cases[2])
                        cases = cases[3]
                except Break: pass
            else: raise ValueError(kind)
        try:
            stmt(body)
        except Returned as r:
            return r.args[0]
        return None

    def run(self, case):
        kind, a, b, direction, w0, w1 = case
        self.reset([w0, w1])
        if kind == 0:
            for i, value in [(28, a), (29, b), (27, direction)]:
                self.store(Pointer('raw', i, '_asF32'), value)
            self.call('_bhv_ttc_cog_update', [])
            get = lambda i: self.load(Pointer('raw', i, '_asS32'))
            return [len(self.draws), self.memory[28], self.memory[29], get(19), get(36)]
        assert kind == 1
        for i, value in [(51, a), (28, b), (27, direction)]:
            self.store(Pointer('raw', i, '_asS32'), value)
        self.call('_bhv_ttc_spinner_update', [])
        # Explicit boundary contract: stable action, one generic timer increment,
        # no other object update/reset/write between native calls. Not execution
        # of the entire cur_obj_update body.
        timer = self.load(Pointer('raw', 51, '_asS32'))
        assert timer < 0x3fffffff
        self.store(Pointer('raw', 51, '_asS32'), timer + 1)
        return [len(self.draws)] + [self.load(Pointer('raw', i, '_asS32')) for i in (51, 28, 27, 18, 35)]
