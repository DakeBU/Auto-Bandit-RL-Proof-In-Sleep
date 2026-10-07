# Correction of prior escaping review finding

**Verdict: accepted. The counter-evidence is correct; the previous serialization blocker was false.** This is a review-metadata correction only. Original source-contract-review-v2.md and its receipt remain byte-fixed, including the erroneous finding.

Actor `/root/source_reviewer`, requested GPT-6 Astra / medium, runtime unverified. Prior staged source-review history disclosed; not blind, human, external or runtime independence attestation.

I independently decoded live readings.json and its immutable before-snapshot with json.loads, recursively inspected every math field of online-linearization, and counted actual U+005C runs. All13 fields have maximum run length0 or1, never2. The source-card field has ordinal92 at index5 followed by114 ('r') at6. The displayed JSON/Python repr escaping was mistaken for duplicate characters in my previous report. That was my review error, not malformed reader data.

I also independently checked all18 selected highlight math fields in both live and immutable before-highlight snapshot; none has two consecutive actual backslashes. Both live files match their corresponding before-snapshot raw SHA. Independently checked all13 v4 verification decoded-value UTF8 hashes and complete ordinal arrays. The bound verification is consistent with the actual decoded content.

Read actual normalize_math_source and executed only its extracted AST function with re available. For the source-card decoded string it returns the exact same correctly escaped TeX wrapped by one display-delimiter pair. It does not need to collapse backslashes. This tests Python normalization, not MathJax rendering. No pixel success or final formula correctness is inferred.

The failed prepare-reader-scope-v3.py selects fields containing TWO literal backslashes and asserts a nonempty list before its first write. Our independent scan finds zero such fields, explaining its guard failure and lack of a valid escaping addendum. The source-reviewer-confirmation text in this unused proposal reflects the prior erroneous message, not valid evidence. No reader edit or source/header/body change is warranted by that proposal.

## Exact supersession

Withdraw ONLY the v2 report's Additional future format obligation and receipt required_reader_corrections item R9-format/reader_format_finding claiming doubled decoded backslashes. That finding is superseded by this correction. Original R1–R8 meanings, mathematical CONTRACT accepted-with-explicit-delta verdict and all existing frozen targets remain unchanged. The actual future full formula/pixel gate remains mandatory; this correction does not certify it or waive any original obligation.

Required mathematical repairs: none. Required metadata repairs after this explicit correction: none. Required reader escaping changes: none. Current BODY/combined/reader/FINAL/native/PR/chapter/Goal acceptance is not provided.

## Raw reviewed files

| Path | SHA256 |
|---|---|
| `runs/online-linearization-public-20261007/source-contract-review-v2.md` | `758dc068aaba492b281b8e1a6622db2fa9d25849b8b1e9ed17acd1b3b11566cc` |
| `runs/online-linearization-public-20261007/source-contract-receipt-v2.json` | `0bf3d15d6bf16c7e36f7d3ede34e97bc6c7bd4bcc96f8a58646c1b19419d881c` |
| `runs/online-linearization-public-20261007/reader-escaping-verification-v4.json` | `46f383b96f41e8e893064bb07bcd43aba124f05a0017125d393dfaecd5af0e70` |
| `runs/online-linearization-public-20261007/inspect-reader-escaping-v4.py` | `edfa5f37ec0c6ae7da00198dcf9269ba69a81c41a1460188051aeb7bdab046aa` |
| `runs/online-linearization-public-20261007/prepare-reader-scope-v3.py` | `9c769f4a9a903cb809fd3dac5e2bdd9dc2b921692de89456fe31df747bea9e6c` |
| `website/content/readings.json` | `b0519ca7e882e1fa36d2f5345a23ecc95b6d3126aef2cf66f67a8764dfd97098` |
| `runs/online-linearization-public-20261007/snapshots/before-website--content--readings.json.txt` | `b0519ca7e882e1fa36d2f5345a23ecc95b6d3126aef2cf66f67a8764dfd97098` |
| `website/content/highlights.json` | `b904acf7bd4ed1bf7c8060d5ab61177cdf9514ff20a33954eb0b9ba05aadab37` |
| `runs/online-linearization-public-20261007/snapshots/before-website--content--highlights.json.txt` | `b904acf7bd4ed1bf7c8060d5ab61177cdf9514ff20a33954eb0b9ba05aadab37` |
| `website/scripts/build_site.py` | `f6cface76e1393fef186ab63ae521c14af11878a0b892b8acfbef390ae380a4f` |
