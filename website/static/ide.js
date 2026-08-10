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
  const exportButton = document.querySelector("[data-ide-export]");
  const exportNote = document.querySelector("[data-ide-export-note]");
  let items = [];
  let current = null;
  let localLean = false;
  let compileTimer = null;
  let lastCompiledSource = "";
  let lastCompileOk = false;

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
    lastCompiledSource = "";
    lastCompileOk = false;
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
    lastCompiledSource = "";
    lastCompileOk = false;
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
      lastCompiledSource = lean.value;
      lastCompileOk = Boolean(result.ok);
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

  const packetId = () => {
    const base = current?.name || "community-lemma";
    return base
      .replace(/^BanditRLProof\./, "")
      .replace(/[^A-Za-z0-9]+/g, "-")
      .replace(/^-|-$/g, "")
      .toLowerCase()
      .slice(0, 96) || "community-lemma";
  };

  const exportPacket = () => {
    const code = lean?.value || "";
    const imports = code
      .split(/\r?\n/)
      .map((line) => line.match(/^\s*import\s+([A-Za-z0-9_.]+)/)?.[1])
      .filter(Boolean);
    const compilerAcceptedCurrentText = lastCompileOk && lastCompiledSource === code;
    const packet = {
      schema_version: "1.0",
      id: packetId(),
      title: current?.plain || "Community lemma proposal",
      domain: current?.chapter || "Unclassified",
      status: compilerAcceptedCurrentText ? "lean-checked" : "proposed",
      mathematics: {
        plain: plain?.textContent || "",
        latex: latex?.value || "",
      },
      lean: {
        imports,
        code,
        proposed_name: current?.name || "",
        dependencies: (current?.dependencies || []).map((dependency) => dependency.name),
      },
      provenance: {
        source: "",
        locator: "",
        notes: "",
      },
      contributor: {
        name: "",
        credit: "",
        contact: "",
      },
      verification: {
        compiler: compilerAcceptedCurrentText ? "local ABRL Lean toolchain" : "not run or source changed",
        accepted: compilerAcceptedCurrentText,
        diagnostics: compilerAcceptedCurrentText ? (diagnostics?.textContent || "Lean accepted the snippet.") : "",
      },
      license: {
        spdx: "MIT",
        agreed: false,
      },
      created_at: new Date().toISOString(),
      draft_missing_fields: ["provenance.source", "contributor.name", "contributor.credit", "license.agreed"],
    };
    const blob = new Blob([`${JSON.stringify(packet, null, 2)}\n`], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const link = document.createElement("a");
    link.href = url;
    link.download = `${packet.id}.json`;
    document.body.append(link);
    link.click();
    link.remove();
    URL.revokeObjectURL(url);
    if (exportNote) {
      exportNote.classList.add("exported");
      exportNote.firstElementChild.textContent = "Lemma packet exported.";
    }
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
  exportButton?.addEventListener("click", exportPacket);
  compileButton?.addEventListener("click", compile);
  latex?.addEventListener("input", () => {
    renderMath();
    if (translationStatus) {
      translationStatus.textContent = "Edited; review required";
      translationStatus.className = "status partial";
    }
  });
  lean?.addEventListener("input", () => {
    lastCompileOk = false;
    scheduleCompile();
  });
  autoCompile?.addEventListener("change", scheduleCompile);
  checkHealth();
})();
