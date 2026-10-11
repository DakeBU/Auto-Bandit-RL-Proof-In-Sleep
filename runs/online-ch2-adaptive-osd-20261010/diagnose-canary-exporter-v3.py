from common import *
s=(RUN/'ExportAlgorithmCanaryValuesV2.lean').read_text(encoding='utf8').replace('else throw "conjunction spine ended early"','else throw s!"conjunction spine ended early index={index} head={p.getAppFn} expr={p}"').replace('throw <| IO.userError err','throw <| IO.userError s!"{name}/{index}: {err}"')
write(RUN/'ExportAlgorithmCanaryValuesDiagnosticV3.lean',s)
code,out=capture('algorithm-canary-value-diagnostic-v3','lake','env','lean','--run',RUN/'ExportAlgorithmCanaryValuesDiagnosticV3.lean',RUN/'algorithm-canary-values-diagnostic-v3.json',required=False)
print(out[:10000],flush=True)
