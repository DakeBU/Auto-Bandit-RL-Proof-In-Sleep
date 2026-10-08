from common_v1 import *
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip() == BASE
fixed()
write(RUN/'bootstrap-environment-repair-v2.json',dict(
    prior_helper='bootstrap-draft-v1.py',actual_prior_exit=1,
    actual_error="ModuleNotFoundError: No module named 'pypdfium2'",
    evidence_origin='actual exec_command output, not independently captured raw stderr file',
    repair='Resume only remaining suffix using bundled Python with pypdfium2; existing baseline files immutable',
    runtime=sys.executable,proof_or_target_changed=False))
source = (RUN/'bootstrap-draft-v1.py').read_text(encoding='utf8')
exec(compile(source[source.index('from pypdf import PdfReader'):],str(RUN/'bootstrap-draft-v1.py')+'#resume','exec'))
