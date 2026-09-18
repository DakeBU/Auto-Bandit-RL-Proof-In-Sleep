(() => {
  const revealHashTarget = () => {
    if (!window.location.hash) return;

    let target;
    try {
      target = document.getElementById(decodeURIComponent(window.location.hash.slice(1)));
    } catch (_error) {
      return;
    }
    if (!(target instanceof HTMLElement)) return;

    target.hidden = false;
    const detailsToOpen = [];
    if (target instanceof HTMLDetailsElement) detailsToOpen.push(target);
    let ancestor = target.closest("details");
    while (ancestor) {
      detailsToOpen.push(ancestor);
      ancestor = ancestor.parentElement?.closest("details") || null;
    }
    [...new Set(detailsToOpen)].forEach((details) => {
      details.hidden = false;
      details.open = true;
    });

    // Two frames let the browser lay out newly opened details before it positions
    // the named proof obligation. This keeps copied #leaf-* URLs useful on both
    // the desktop sidebar layout and the collapsed mobile layout.
    window.requestAnimationFrame(() => {
      window.requestAnimationFrame(() => target.scrollIntoView({ block: "start" }));
    });
  };
  window.addEventListener("hashchange", revealHashTarget);

  const root = document.querySelector("[data-wiki]");
  if (!root) {
    revealHashTarget();
    return;
  }

  const controls = {
    query: root.querySelector("[data-wiki-query]"),
    family: root.querySelector("[data-wiki-family]"),
    literature: root.querySelector("[data-wiki-literature]"),
    lean: root.querySelector("[data-wiki-lean]"),
    frontier: root.querySelector("[data-wiki-frontier]"),
  };
  const cards = [...root.querySelectorAll("[data-wiki-case]")];
  const count = root.querySelector("[data-wiki-count]");
  const expand = root.querySelector("[data-wiki-expand]");
  const collapse = root.querySelector("[data-wiki-collapse]");
  const empty = document.createElement("p");
  empty.className = "empty wiki-empty";
  empty.textContent = "No cases match all active filters.";
  empty.hidden = true;
  root.querySelector(".wiki-case-list")?.append(empty);

  const params = new URLSearchParams(window.location.search);
  if (controls.query) controls.query.value = params.get("q") || "";
  if (controls.family) controls.family.value = params.get("family") || "";
  if (controls.literature) controls.literature.value = params.get("literature") || "";
  if (controls.lean) controls.lean.value = params.get("lean") || "";
  if (controls.frontier) controls.frontier.checked = params.get("frontier") === "1";

  const updateUrl = () => {
    const next = new URLSearchParams();
    const query = controls.query?.value.trim();
    if (query) next.set("q", query);
    if (controls.family?.value) next.set("family", controls.family.value);
    if (controls.literature?.value) next.set("literature", controls.literature.value);
    if (controls.lean?.value) next.set("lean", controls.lean.value);
    if (controls.frontier?.checked) next.set("frontier", "1");
    const queryString = next.toString();
    const target = window.location.pathname + (queryString ? "?" + queryString : "") + window.location.hash;
    window.history.replaceState(null, "", target);
  };

  const filter = () => {
    const terms = (controls.query?.value || "").trim().toLowerCase().split(/\s+/).filter(Boolean);
    const family = controls.family?.value || "";
    const literature = controls.literature?.value || "";
    const lean = controls.lean?.value || "";
    const frontierOnly = Boolean(controls.frontier?.checked);
    let visible = 0;
    cards.forEach((card) => {
      const show =
        terms.every((term) => (card.dataset.search || "").includes(term)) &&
        (!family || card.dataset.family === family) &&
        (!literature || card.dataset.literature === literature) &&
        (!lean || card.dataset.lean === lean) &&
        (!frontierOnly || card.dataset.frontier === "true");
      card.hidden = !show;
      if (show) visible += 1;
    });
    if (count) count.textContent = visible.toLocaleString() + " matching " + (visible === 1 ? "case" : "cases");
    empty.hidden = visible !== 0;
    updateUrl();
  };

  Object.values(controls).forEach((control) => {
    control?.addEventListener("input", filter);
    control?.addEventListener("change", filter);
  });
  expand?.addEventListener("click", () => {
    cards.forEach((card) => {
      if (!card.hidden) card.open = true;
    });
  });
  collapse?.addEventListener("click", () => {
    cards.forEach((card) => {
      card.open = false;
    });
  });

  filter();
  revealHashTarget();
})();
