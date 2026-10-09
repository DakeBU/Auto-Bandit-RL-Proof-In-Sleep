import json,sys
def body_normalized(s):
    s=s.replace('\r\n','\n')
    return s[:-1] if s.endswith('\n') else s
cases=[('body\r\n','body'),('body\n','body'),('body','body'),('body \n','body '),('body\n\n','body\n'),('a\r\nb\r\n','a\nb')]
for raw,expected in cases:assert body_normalized(raw)==expected
assert body_normalized('body \n')!=body_normalized('body\n')
assert body_normalized('body\n\n')!=body_normalized('body\n')
print(json.dumps(dict(actual_executable=sys.executable,actual_version=sys.version,case_count=len(cases),trailing_space_preserved=True,second_trailing_newline_preserved=True,all_passed=True)))
