# Reverse derivative proof repairs

reverse-gradient01 failed to infer the fixed vector in the constant filter limit and inferred the wrong set argument for interior_subset. reverse-gradient02 fixed the constant but still used a proposition with the wrong syntactic membership target. Neither failed run establishes a theorem; Lean error recovery displayed sorryAx and is rejected.

reverse-gradient03 explicitly fixes the constant at g and states membership in effectiveDomain before coercing its value. The exact frozen reverse header is unchanged. The process exited 0 with no errors and only propext, Classical.choice and Quot.sound for the actual reverse producer.

full-theorem01 was not a mathematical compilation attempt: the temporary Python assembler used a Path.write_text newline option unsupported by the installed Python3.8, so the candidate file did not exist. The assembler was corrected to an explicit UTF8 LF stream. full-theorem02 compiles the actual full iff and gradient companion with the same three standard axioms; public integration and combined acceptance are separate.
