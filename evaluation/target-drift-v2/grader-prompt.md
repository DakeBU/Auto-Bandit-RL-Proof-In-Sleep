# Target-drift blind grading instruction

Evaluate each packet only against its frozen source contract, proposed
requirement, submitted Lean artifacts, and neutral checker evidence. Do not
infer or reward a workflow condition. Apply every binary label in the frozen
rubric independently, cite the exact source field and artifact line that
controls a failure or reversal, and then guess the hidden workflow condition
only for the preregistered blinding audit.

Return one schema-conforming record per `grade_id`. Do not consult the operator
mapping, run directories, model metadata, prompts, or condition-specific
process artifacts.
