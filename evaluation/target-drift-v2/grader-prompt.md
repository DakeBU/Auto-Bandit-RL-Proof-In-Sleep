# Target-drift blind grading instruction

Work only from the physically separate grader-only export supplied to you.
Before grading, preserve the `grader_export_sha256`, `grading_pack_sha256`, and
`grader_prompt_sha256` already present in its response template. Do not add,
remove, or rename packets.

Evaluate each packet only against its frozen source contract, proposed
requirement, submitted Lean artifacts, and neutral checker evidence. Do not
infer or reward a workflow condition. Apply every binary label in the frozen
rubric independently, cite the exact source field and artifact line that
controls a failure or reversal, and then guess the hidden workflow condition
only for the prospectively specified blinding audit.

Return one schema-conforming record per `grade_id` in a copy of
`response-template.json`. Do not consult the internal grading pack, operator
mapping, completion ledger, run directories, model metadata, other prompts, or
condition-specific process artifacts. If any such file appears in the
grader-only export, stop and report the distribution failure without grading.
