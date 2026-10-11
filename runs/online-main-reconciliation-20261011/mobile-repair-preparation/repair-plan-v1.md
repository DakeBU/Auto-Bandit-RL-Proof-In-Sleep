# Source-card mobile grid repair candidate

Only website/static/site.css is proposed for change: add grid-template-columns: minmax(0, 1fr) to .source-theorem-route-list and min-width: 0 to .source-theorem-disclosure. Full original/candidate bytes and a two-declaration diff are retained here. No tracked or generated-site edit occurred.

The actual template makes details the grid item and article its block child. Recorded mobile geometry shows the 358px route list assigning an implicit 629.375px track; the auto-minimum disclosure expands with it. The 627.375px card is then clipped by outer site-content. I personally viewed the failed screenshot and inspected the template/current CSS. The candidate constrains that grid track and removes the item's content minimum. It leaves the source text, math, disclosure semantics and existing internal formula horizontal scrolling intact.

This is a proposed layout repair, not a verified fix. Descendant headings/links, nested grids and full formula scroll reach must be checked in the actual next render with unchanged clipping predicates. Do not change QA thresholds, remove content, hide the overflow defect or edit old site outputs. Parent should independently review before applying, rebuild at the accepted clean candidate and rerun existing 390/1440 checks with fresh output/profile.

Requested GPT-6 Astra/medium; runtime not attested. Exact input and output hashes, observed HEAD and clean status are in repair-plan-v1.json.
