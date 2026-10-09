# Candidate staging, harness retry and local site plan review

Verdict: accepted-with-explicit-delta, conditional on the explicit caller checks below. No mathematical change or new proof acceptance. This is prospective execution-scope approval, not evidence that the future commands passed.

Actor /root/source_reviewer is a reused distinct staged automated reviewer, requested Astra/medium without runtime attestation, external/human review or absolute blindness. Prior integration and artifact reviews remain unchanged.

## Actual failure and correction of the earlier operational statement

The original full harness command exits1. Its raw stdout shows successful Tests build9290, exporter invocation, then AnonymousSupplementTests.setUpClass raises ValueError: untracked Lean source under allowlisted tree: BanditRLProof/OnlineFTLSelector.lean. The unittest result is446 tests, one error, seven skips. Separate root/Tests evidence records9115/9290 jobs. This is not a Lean theorem failure and is not a complete harness pass.

My earlier v2 integration review statement that staging is unnecessary for root/Tests/harness was too broad. The recursive placeholder scan can see untracked Lean, but this additional anonymous-supplement test requires the new allowlisted source in the Git index. Preserve that earlier report and this explicit correction; stage the exact new files before the real full retry, without changing their proof bytes.

## Four concrete helpers

stage-candidate-v1 checks the integrated guard, exact base HEAD and initially empty index, verifies the favorable artifact review and all its inputs, then hashes every matched binary artifact before staging. Independently enumerating those matches found47 files, all already present in the approved immutable artifact input set, with no new unmatched artifact. The approved attributes themselves are fixed inputs. Active helper-v2/production/Test files are not -diff. The stage list is limited to six approved old paths, two new Lean modules and OWN RUN/contract/task/contribution paths. It checks the baseline intersection equals exactly the six paths, all staged paths are within the stage list, active text whitespace, and the indexed two new Lean blobs exactly equal working RAW bytes. Capture receipts written after the initial add are intentionally gathered by the later final stage.

run-full-harness-v2 rechecks exact frozen inputs and both indexed Lean blobs, runs the actual tools/bandit.py check, retains its real stdout/exit, and requires successful build/unittest/exporter/check markers. Failure stops execution. It does not convert the previous failure into success or skip the failing suite.

commit-and-build-site-v1 requires the actual harness-v2 success record, zero shadow mismatches and staging checks. Final-stage and following commit/contributor/site-build command receipts are initially written under ignored tmp, preventing a post-stage RUN receipt from making the commit dirty. It requires no unstaged/untracked content, runs the actual staged text check and commits without force. It then requires two real committed diff-aware contributor successes, rejects N/A and demands the new production module in the output. Only after a clean checkout and those checks does it build the isolated site with --lean-verified. That flag is justified only by the successful unchanged full-harness binding. The site must not already exist. After building, command receipts are copied into RUN as new evidence; the site therefore binds the clean candidate commit, not a later evidence HEAD. Site check and registry checks remain real commands with failure propagation. A later failure may leave the authorized candidate commit in place; this is not publication or gate acceptance.

verify-registry-v1 checks gzip and decompressed baseline SHA, same registry identity, complete equality of each11041 old node object, exactly13 new canonical IDs and total11054, no Test/generated-Test nodes, source-qualified identities and actual module HTML files. Both site manifests must bind the clean recorded candidate HEAD and lean_verified with source_dirty=false. Fourteen source cards are required. This is stronger than count-only comparison; it still does not replace later DOM/math/pixel review.

## Binding and execution conditions

I ran integration_guard_v2.fixed() read-only successfully, checked all31 review RAW inputs before/after, stage-plan hash, four helper hashes and Python syntax. No stage, harness, commit or site helper was executed by this reviewer.

These four helpers inherit the accepted integration guard but do not themselves load this newly created candidate-plan review. Therefore the authorized caller must first validate this favorable receipt/report/index SHA and rehash every current row and all four helper hashes before executing the staged sequence. Before each later helper, recheck the frozen input set and required new predecessor receipts. Immediately after the final restage and before commit, independently recheck cached BASE paths: baseline intersection must be exactly the six approved old paths and every new path must lie in the exact reviewed stage list. Newly created OWN artifacts must be evidence/helper outputs within this task, not hidden code or changes to frozen inputs. Any new -diff-matched artifact beyond the47 inspected files requires separate exact binding/scope review. These are explicit execution conditions, not claims that the scripts enforce this review internally.

The allowed sequence is exact staging, genuine harness retry, exact restaging/conditional candidate commit, two nonempty contributor checks, clean isolated site/build/check/registry and OWN evidence recording. No push/PR, native acceptance, merge/deploy/global credential change, source-container or Chapter2/Goal closure is authorized here. Browser/original-pixel/FINAL/native/post-native/delivery gates remain separate. All eight forward containers remain required/open and GoalACTIVE.

## Input bindings

- E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineFTLSelector.lean — before/after cd1cae5683edaa40fde18466f1efbca8ad34b295d8dfc3b173a35e0d459405df
- E:/ABRL/worktrees/research-online-book/BanditRLProof.lean — before/after 78689ab212418e79f477c6e321265e5456eabafa27ab437ebe9b6988ed9e679a
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-book-v1/coverage.json — before/after eccc530ba62bac75db4da470e996811f9b23063aeca8dda34c53b315399ea4ba
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/.gitattributes — before/after 705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/exact-integration-plan-v1.json — before/after 8ac6db7ef1a93c15dea1b774a03b826e73323b685842a03afe736f59cad48e80
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/.gitattributes — before/after 4c998b82a6e1e718a46260844e32b551d87a4a4f9660d4638d60e32595c42ee3
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/candidate-git-site-plan-v1.json — before/after ac9777e660dcd3db8f46fa3b88719b50dcf0567d941d802e2f87266281694753
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/candidate-shadow-inspected-v1.json — before/after 4b6c5e8e6c537aaa933d796cbf4e643f79404692336caeb996e26e6e3b00a680
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/candidate-stage-plan-v1.json — before/after e40d14064a0b0d12858271b6e99c6606d47168d9d43cc81041e1e30ba871d0b4
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/combined-full-harness-v1.json — before/after f5a432cfa3670e7b6d64cc4e918881686241ff6302ceddaaa40a1269fd7e5599
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/combined-root-Tests-inspected-v1.json — before/after 18d9cd09b92433c779bff470762a9058df91057c47c630caac6a969b709ef631
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/commit-and-build-site-v1.py — before/after c08430ae777d859528829fd9092a7ec1012710d023bdb0c042de97ce4bbeb8e7
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/evidence-attributes-review-inputs-v1.json — before/after 7fd3f3af240a21b61c6d72873c56eac5be8d1196fd2237684d16b304b18dae71
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/evidence-attributes-review-v1.json — before/after 2e19af06faf63c3f1f4361dea2c380892d43f15d53a2e5932982fae09922a0c5
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/evidence-attributes-review-v1.md — before/after 3f548603e2f48297ef61f076b24d3c94d8b7e9a6f1d238ae0867a65ea0a36883
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-BODY-review-v1.json — before/after 47f8ec8b77a419c8bd39fc10fccee22a63bff8359d827e8d24c47999ff36d684
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/full-harness-failure-inspected-v1.json — before/after efc061974c4fd622172224c1ac76a10c36769c7ff6d0e6f93fc9c85d04bb42e6
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/integration-plan-review-v2.json — before/after 55f01d05cc78690c5ff2f84ec35240d32092ee7ea7ed462ee98e9dd9d16416d3
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/integration_guard_v2.py — before/after ee3ce0dae1057aa626a534e2fe8e7a9132adb4bb39662bca47d5c42979580f46
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/prospective-contribution-v2.json — before/after 7de38d7e04c6d3cfa7e03ae3f1be1149dad9018057bff185442c901dbe8d1035
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/reader-proposal-v1.json — before/after 5557da7e95d05e46b86f4aff5bee884853d3a190adf5e36bec1e41cd01c4105a
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/registry-baseline-binding-v1.json — before/after e10ccb8b1067cc30b8ec6d4ec51378da76e93364ef540ca7697d1148b7a06eb0
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/registry-baseline-v1.json.gz — before/after 870a7e63e9051e6a6fe6d2256dac3a65eef01323f180c52ebec08d05d829f577
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/run-full-harness-v2.py — before/after 94772b5d712277a86581dafc6b6e1f86ab510d288cbc5820342b0e6d4d1b6945
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/stage-candidate-v1.py — before/after 8f727fd7372bd7fbe22b33288cbc2cb8389804670305908a1a5d4386f02151a4
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/verify-registry-v1.py — before/after 136d5e7a5ced78bb7b9c58d4ea9860d4818c2082948c785d36b7b7761b201122
- E:/ABRL/worktrees/research-online-book/Tests/OnlineFTLSelectorCanary.lean — before/after a6e3b16b29c6a5eddcb343cb555457eb52bed35c9c5089a1948e90f30cb1df85
- E:/ABRL/worktrees/research-online-book/Tests.lean — before/after 1b89d5d4c175ca28dd40d493ae549abe506f3009225856afd051b14a96e14de8
- E:/ABRL/worktrees/research-online-book/website/content/chapters.json — before/after 9b2198a4b319cca2c3942ee093dc360a2619c57f97ad395f7afe7a8c4daa5c01
- E:/ABRL/worktrees/research-online-book/website/content/highlights.json — before/after 531da75fad121ae8dd949a19c1d5439964cfcca6905c1dd48561280ae9895cf5
- E:/ABRL/worktrees/research-online-book/website/content/readings.json — before/after 646b494554cfada17566b27ee2bdd455a2ea52d3a382597f42048c0b519c0a78
