from common_v1 import *
fixed()
write(RUN/'readiness-pair-repair-failure-v2.md','''repair-ready-pairs-v2.py actually exited1 because Python rejects the misspelled utf8-sig codec. It had saved readiness-pair-failure-v1.md before failing; no v2 checker existed and its subsequent launch failed. V3 uses the exact utf-8-sig codec. All versions remain retained, no source/statement/body mutations.''')
code=(RUN/'audit-ready-pairs-v1.py').read_text(encoding='utf-8-sig').replace("(ns+'meanPredict_limitNoRegret_iff_mean_converges',ns+'meanPredict_noRegret')","(ns+'meanPredict_limitNoRegret_iff_mean_converges',ns+'meanPredict_limitNoRegret_of_mean_converges')").replace('required-readiness-value-pairs-v1.json','required-readiness-value-pairs-v2.json')
write(RUN/'audit-ready-pairs-v2.py',code)
fixed()
