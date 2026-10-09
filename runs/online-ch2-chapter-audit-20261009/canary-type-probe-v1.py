from lower_common_v1 import *
reviewed();headers(3)
c=load(CONTRACT/'nonsmooth-canary-contracts-v1.json')
text='''import BanditRLProof.OnlineNonsmoothExamples
import Tests.OnlineGradientDescentSourceCanary
open scoped InnerProductSpace
open Tests.OnlineGradientDescentSource
'''
for t in c['targets']:
 short=t['declaration'].rsplit('.',1)[-1]
 binders,prop=t['exact_header'][len('theorem '+short):].split(' :\n',1)
 text+='\n#check ('+('∀'+binders+',\n' if binders.strip() else '')+prop+')\n'
write(RUN/'nonsmooth-canary-type-probe-v1.lean',text)
capture('nonsmooth-canary-type-probe-v1','lake','env','lean',RUN/'nonsmooth-canary-type-probe-v1.lean',required=False)
reviewed();print('Only five complete proposed canary proposition types probed; no canary theorem BODY authored.')
