"""Assemble LogLean/MinorCore.lean = header + LogSeries body + gen/core_tail.lean."""
import os, re
here = os.path.dirname(os.path.abspath(__file__))
ls = open(os.path.join(here, '..', 'LogLean', 'LogSeries.lean')).read()
body = ls[ls.index('noncomputable def logTaylor'):ls.rindex('end LogLean')]
hdr = open(os.path.join(here, 'core_head.lean')).read()
tail = open(os.path.join(here, 'core_tail.lean')).read()
open(os.path.join(here, '..', 'LogLean', 'MinorCore.lean'), 'w').write(hdr + body + tail)
