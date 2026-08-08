(() => {
  const app = document.querySelector("[data-ide-app]");
  if (!app) return;

  const select = document.querySelector("[data-ide-declaration]");
  const latex = document.querySelector("[data-ide-latex]");
  const lean = document.querySelector("[data-ide-lean]");
  const preview = document.querySelector("[data-ide-math-preview]");
  const plain = document.querySelector("[data-ide-plain]");
  const diagnostics = document.querySelector("[data-ide-diagnostics]");
  const duration = document.querySelector("[data-ide-duration]");
  const mode = document.querySelector("[data-ide-mode]");
  const modeTitle = document.querySelector("[data-ide-mode-title]");
  const modeDetail = document.querySelector("[data-ide-mode-detail]");
  const translationStatus = document.querySelector("[data-translation-status]");
  const declarationLink = document.querySelector("[data-ide-declaration-link]");
  const sourceLink = document.querySelector("[data-ide-source-link]");
  const tree = document.querySelector("[data-ide-tree]");
  const treeSummary = document.querySelector("[data-ide-tree-summary]");
  const autoCompile = document.querySelector("[data-ide-auto]");
  const compileButton = document.querySelector("[data-ide-compile]");
  const loadButton = document.querySelector("[data-ide-load]");
  const scaffoldButton = document.querySelector("[data-ide-scaffold]");
  let items = [];
  let current = null;
  let localLean = false;
  let compileTimer = null;

  const setMode = (available, detail) => {
    localLean = available;
    mode?.classList.toggle("local", available);
    mode?.classList.toggle("static", !available);
    if (modeTitle) modeTitle.textContent = available ? "Local Lean compiler connected" : "Static teaching mode";
    if (modeDetail) modeDetail.textContent = detail;
    if (compileButton) compileButton.disabled = !available;
    if (autoCompile) {
      autoCompile.disabled = !available;
      if (!available) autoCompile.checked = false;
    }
  };

  const typeset = async () => {
    if (!preview) return;
    try {
      if (window.MathJax?.startup?.promise) await window.MathJax.startup.promise;
      if (window.MathJax?.typesetClear) window.MathJax.typesetClear([preview]);
      if (window.MathJax?.typesetPromise) await window.MathJax.typesetPromise([preview]);
    } catch (error) {
      console.error("MathJax preview failed", error);
    }
  };

  const renderMath = () => {
    if (!preview || !latex) return;
    preview.textContent = latex.value.trim() || "Enter a LaTeX statement to render it here.";
    typeset();
  };

  const leaf = (label, href, className = "") => {
    const node = document.createElement(href ? "a" : "div");
    node.className = `ide-tree-node ${className}`.trim();
    node.textContent = label;
    if (href) node.href = href;
    return node;
  };

  const renderTree = (item) => {
    if (!tree) return;
    tree.replaceChildren();
    const root = document.createElement("div");
    root.className = "ide-tree-root";
    root.append(leaf(item.name, item.url, "root"));
    const branch = document.createElement("div");
    branch.className = "ide-tree-children";
    branch.append(leaf(`module: ${item.module}`, item.source_url, "module"));
    item.dependencies.forEach((dependency) => branch.append(leaf(dependency.name, dependency.url, "dependency")));
    if (!item.dependencies.length) branch.append(leaf("No curated theorem dependency recorded", "", "empty-node"));
    root.append(branch);
    tree.append(root);
    if (treeSummary) treeSummary.textContent = `${item.dependencies.length} theorem dependencies + source module`;
  };

  const loadMapping = (item) => {
    current = item;
    if (latex) latex.value = item.latex;
    if (lean) lean.value = item.compile_source;
    if (plain) plain.textContent = item.plain;
    if (translationStatus) {
      translationStatus.textContent = "Reviewed mapping";
      translationStatus.className = "status compiled";
    }
    if (declarationLink) declarationLink.href = item.url;
    if (sourceLink) sourceLink.href = item.source_url;
    renderMath();
    renderTree(item);
    if (diagnostics) diagnostics.textContent = "Reviewed mapping loaded. Compile locally to ask the pinned Lean toolchain to elaborate the declaration.";
    scheduleCompile();
  };

  const safeDraftScaffold = () => {
    const source = (latex?.value || "").replace(/\r?\n/g, " ").replace(/--/g, "—").slice(0, 1200);
    if (lean) {
      lean.value = [
        "import BanditRLProof",
        "",
        "-- DRAFT ONLY: the LaTeX below has not been translated into a Lean proposition.",
        `-- ${source}`,
        "-- Replace `True` with a reviewed formal statement before treating this as a mapping.",
        "example : True := by",
        "  trivial",
        "",
      ].join("\n");
    }
    if (translationStatus) {
      translationStatus.textContent = "Draft; manual translation required";
      translationStatus.className = "status partial";
    }
    if (diagnostics) diagnostics.textContent = "A compiling placeholder scaffold was created, but no mathematical equivalence is claimed. Replace `True` with the reviewed proposition.";
    scheduleCompile();
  };

  const compile = async () => {
    if (!localLean || !lean || !diagnostics) return;
    compileButton.disabled = true;
    diagnostics.textContent = "Lean is elaborating the temporary snippet…";
    duration.textContent = "";
    try {
      const response = await fetch("../api/compile", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ code: lean.value }),
      });
      const result = await response.json();
      diagnostics.textContent = result.output || (result.ok ? "Lean accepted the snippet." : "Lean rejected the snippet without diagnostics.");
      diagnostics.classList.toggle("success", Boolean(result.ok));
      diagnostics.classList.toggle("failure", !result.ok);
      duration.textContent = Number.isFinite(result.duration_ms) ? `${result.duration_ms} ms` : "";
    } catch (error) {
      diagnostics.textContent = `The local Lean service became unavailable: ${error.message}`;
      diagnostics.classList.add("failure");
      setMode(false, "Start website/scripts/ide_server.py to restore verified compilation.");
    } finally {
      compileButton.disabled = !localLean;
    }
  };

  const scheduleCompile = () => {
    window.clearTimeout(compileTimer);
    if (!localLean || !autoCompile?.checked) return;
    compileTimer = window.setTimeout(compile, 850);
  };

  const checkHealth = async () => {
    try {
      const response = await fetch("../api/health", { headers: { Accept: "application/json" } });
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      const health = await response.json();
      setMode(true, `${health.lean_version || "Lean"}; temporary snippets only; source files are untouched. Auto-compile is opt-in for large imports.`);
    } catch (_error) {
      setMode(false, "Rendering, verified mappings, and dependency navigation remain available; code execution is disabled.");
      if (diagnostics) diagnostics.textContent = "Static mode: run `python3 website/scripts/ide_server.py` from the repository root for real Lean diagnostics.";
    }
  };

  fetch(app.dataset.ideData)
    .then((response) => response.json())
    .then((data) => {
      items = data.items || [];
      select.innerHTML = items
        .map((item, index) => `<option value="${index}">${item.chapter} — ${item.name}</option>`)
        .join("");
      const preferred = items.findIndex((item) => item.name.includes("integrable_and_integral_le_threshold"));
      select.value = String(preferred >= 0 ? preferred : 0);
      if (items.length) loadMapping(items[Number(select.value)]);
    })
    .catch((error) => {
      if (diagnostics) diagnostics.textContent = `Could not load the reviewed mapping index: ${error.message}`;
    });

  select?.addEventListener("change", () => loadMapping(items[Number(select.value)]));
  loadButton?.addEventListener("click", () => current && loadMapping(current));
  scaffoldButton?.addEventListener("click", safeDraftScaffold);
  compileButton?.addEventListener("click", compile);
  latex?.addEventListener("input", () => {
    renderMath();
    if (translationStatus) {
      translationStatus.textContent = "Edited; review required";
      translationStatus.className = "status partial";
    }
  });
  lean?.addEventListener("input", scheduleCompile);
  autoCompile?.addEventListener("change", scheduleCompile);
  checkHealth();
})();
