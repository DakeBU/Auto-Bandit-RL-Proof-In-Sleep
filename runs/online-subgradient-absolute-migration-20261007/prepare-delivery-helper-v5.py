from common import *
s=(RUN/'prepare-delivery-v4.py').read_text(encoding='utf-8-sig')
s=s.replace("'scoped-diff-v4-01']:passed(label)", "'scoped-diff-v4-01','committed-raw-audit-v3-01']:passed(label)")
s=s.replace("No mathematical weakening or hidden proof failure.", "The initial delivery raw audit ran before its new gate logs were committed, then git show HEAD:longpath hit a Windows path limit. Both failures remain; exact tree/blob-object reads avoid path disambiguation without renaming snapshots or changing global config. The all-current-run raw audit subsequently passed. No mathematical weakening or hidden proof failure.")
write(RUN/'prepare-delivery-v5.py',s);generated('actual-delivery-helper-before-use-v5.json',[RUN/'prepare-delivery-v5.py'])
