"""Cooperative phase limits; safety finalization is allowed to overrun a limit."""
import time


class LimitReached(Exception):
    def __init__(self, phase):
        self.phase = phase
        super().__init__(phase+' budget exhausted')


class WorkLimits:
    def __init__(self, setup=None, verification=None, search=None, overall=None, clock=None):
        self.clock = clock or time.perf_counter
        self.started = self.clock()
        self.phase_started = self.started
        self.phase = 'preparation'
        self.bounds = dict(preparation=setup,verification=verification,search=search)
        self.overall = overall
        self.phases = dict(preparation=0.,verification=0.,search=0.,checkpoint=0.,finalization=0.)
        if any(x is not None and x<0 for x in list(self.bounds.values())+[overall]):
            raise ValueError('Limits must be nonnegative or unset')

    def enter(self, phase):
        now=self.clock()
        self.phases[self.phase] += now-self.phase_started
        self.phase_started=now; self.phase=phase

    def check(self):
        now=self.clock()
        if self.overall is not None and now-self.started>=self.overall:
            raise LimitReached(self.phase)
        bound=self.bounds.get(self.phase)
        if bound is not None and self.phases[self.phase]+now-self.phase_started>=bound:
            raise LimitReached(self.phase)

    def finish(self):
        now=self.clock()
        result=dict(self.phases)
        result[self.phase]+=now-self.phase_started
        return dict(phaseSeconds=result,totalSeconds=now-self.started,
                    limits=dict(setup=self.bounds['preparation'],verification=self.bounds['verification'],
                                search=self.bounds['search'],overall=self.overall),
                    limitSemantics='Cooperative checks between updates and bounded IO operations; '
                        'an in-flight native update/IO cannot be preempted. Completed records are '
                        'checkpointed and safety finalization may exceed these limits.')
