"""Bounded target-derived contact/movement proposals, not reachability coverage.

Only typed, finite Mario fields are supplied at the earliest context. Stock
updates decide whether a proposed horizontal inverse or delayed interaction
actually works. The restored scene/support/RNG remain conditional.
"""
import math

from search import Backend, Move, Input, IDLE, WALKING, FREEFALL, DIALOG, bits, number, f32


class ContactBackend(Backend):
    def observe(self):
        result = super().observe()
        result['faceYaw'] = self.game.read('gMarioState.faceAngle[1]')
        return result

    def patch(self, patch):
        extra = {'vx': 'vel[0]', 'vz': 'vel[2]', 'forwardVel': 'forwardVel',
                 'faceYaw': 'faceAngle[1]'}
        super().patch({k: v for k, v in patch.items() if k not in extra})
        for key, path in extra.items():
            if key in patch:
                value = patch[key] if key == 'faceYaw' else number(patch[key])
                self.game.write('gMarioState.' + path, value)
        actual = self.observe()
        if any(actual[k] != v for k, v in patch.items()):
            raise RuntimeError('Contact predecessor patch failed readback')


def contact_templates(target, legacy):
    """Interleave legacy, displaced collision and horizontal inverse recipes.

    Collision offsets are hypotheses about an earlier record, not teleportation
    inputs. Horizontal displacement uses target minus a finite proposed speed;
    exact walls/air acceleration/rounding are tested by the game, not assumed.
    The terminal automatic-message state is the real stock action, supplied
    diagnostically; no reward/dialog history is granted by this generator.
    """
    legacy = tuple(legacy)
    families = [list(legacy), [], [], []]
    offsets = [(0., dy, 0.) for dy in (-128., -64., 64., 128., 384.)]
    offsets += [(dx, 0., dz) for radius in (48., 96., 192., 384.)
                for dx, dz in ((radius, 0.), (-radius, 0.), (0., radius), (0., -radius))]
    for base in legacy:
        for dx, dy, dz in offsets:
            patch = dict(base.patch)
            patch['collision'] = [bits(f32(number(v) + delta))
                                  for v, delta in zip(target['collision'], (dx, dy, dz))]
            families[1].append(Move('contact-%s-offset-%g-%g-%g' % (base.name, dx, dy, dz),
                                    patch, Input(), 'earlier collision outside/near contact hypothesis'))
    for action, tag in ((WALKING, 'walk'), (FREEFALL, 'air')):
        for speed in (8., 16., 32., 48., 64.):
            for yaw in (0, 8192, 16384, 24576, -32768, -24576, -16384, -8192):
                vx = f32(speed * math.sin(yaw * math.pi / 32768.))
                vz = f32(speed * math.cos(yaw * math.pi / 32768.))
                old = list(target['movement'])
                old[0] = bits(f32(number(old[0]) - vx))
                old[2] = bits(f32(number(old[2]) - vz))
                for raw_mode in ('aligned', 'target-low', 'above-contact'):
                    raw = list(old) if raw_mode == 'aligned' else list(target['collision'])
                    if raw_mode == 'above-contact':
                        raw[1] = bits(f32(number(raw[1]) + 128.))
                    for display_mode in ('inherited', 'aligned'):
                        patch = dict(movement=list(old), collision=raw,
                                     display=list(target['display']) if display_mode == 'inherited' else list(old),
                                     action=action, actionState=0, actionArg=0, actionTimer=0,
                                     depth=bits(0.), vy=bits(0.), vx=bits(vx), vz=bits(vz),
                                     forwardVel=bits(speed), faceYaw=yaw)
                        families[2].append(Move('horizontal-%s-%g-%d-%s-%s' %
                                               (tag, speed, yaw, raw_mode, display_mode),
                                               patch, Input(), 'target-minus-speed horizontal proposal'))
    for state in (23, 24):
        for timer in (0, 1, 4, 8, 16, 24):
            for raw_mode in ('target', 'aligned', 'above-contact'):
                raw = list(target['collision']) if raw_mode != 'aligned' else list(target['movement'])
                if raw_mode == 'above-contact': raw[1] = bits(f32(number(raw[1]) + 128.))
                patch = dict(movement=list(target['movement']), collision=raw,
                             display=list(target['display']), action=DIALOG,
                             actionState=state, actionArg=0, actionTimer=timer,
                             depth=target.get('depth', bits(0.)), vy=bits(0.))
                families[3].append(Move('interaction-dialog-%d-%d-%s' % (state, timer, raw_mode),
                                       patch, Input(), 'stock intangible message-state predecessor hypothesis'))
    seen = set()
    for i in range(max(map(len, families))):
        for family in families:
            if i >= len(family): continue
            move = family[i]
            identity = tuple((k, tuple(v) if isinstance(v, list) else v)
                             for k, v in sorted(move.patch.items()))
            if identity not in seen:
                seen.add(identity)
                yield move
