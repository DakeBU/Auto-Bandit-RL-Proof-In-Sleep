from common import *
s=(RUN/'ExportAlgorithmCanaryValuesV2.lean').read_text(encoding='utf8')
s=s.replace('partial def peel (e : Expr) : Expr :=\n  match e with','partial def peel (e : Expr) : Expr :=\n  let reduced := e.headBeta\n  if reduced != e then peel reduced else\n  match e with')
s=s.replace('e.getAppArgs.size == 2 then peel e.getAppArgs[1]! else e','e.getAppArgs.size >= 2 then\n      peel (mkAppN e.getAppArgs[1]! (e.getAppArgs.extract 2 e.getAppArgs.size)) else e')
write(RUN/'ExportAlgorithmCanaryValuesV4.lean',s)
write(RUN/'algorithm-canary-exporter-repair-v4.json',dict(classification='Diagnostic v3 shows overapplied id wrapping lambda; preserve and beta-reduce remaining application arguments after removing id',evidence=rows([RUN/'algorithm-canary-value-diagnostic-v3.json']),production_unchanged=sha(ROOT/'Tests/OnlineAdaptiveOSDCanary.lean')))
code,out=capture('algorithm-canary-value-export-v4','lake','env','lean','--run',RUN/'ExportAlgorithmCanaryValuesV4.lean',RUN/'algorithm-canary-values-native-v4.json',required=False)
print(out,flush=True)
sys.exit(code)
