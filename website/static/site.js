(() => {
  const doc = document.documentElement;
  const themeButtons = [...document.querySelectorAll("[data-theme-choice]")];
  const savedTheme = localStorage.getItem("abrl-theme");
  const validThemes = new Set(["blueprint", "modern", "bold"]);
  const initialTheme = validThemes.has(savedTheme) ? savedTheme : "blueprint";

  const applyTheme = (theme) => {
    doc.dataset.theme = theme;
    localStorage.setItem("abrl-theme", theme);
    themeButtons.forEach((button) => {
      button.setAttribute("aria-pressed", String(button.dataset.themeChoice === theme));
    });
  };

  applyTheme(initialTheme);
  themeButtons.forEach((button) => {
    button.addEventListener("click", () => applyTheme(button.dataset.themeChoice));
  });

  const sidebar = document.querySelector("[data-site-sidebar]");
  const sidebarToggles = [...document.querySelectorAll("[data-sidebar-toggle]")];
  const sidebarScrim = document.querySelector("[data-sidebar-scrim]");
  const setSidebarOpen = (open) => {
    document.body.classList.toggle("sidebar-open", open);
    sidebarToggles.forEach((button) => button.setAttribute("aria-expanded", String(open)));
    if (open) sidebar?.querySelector("a, button, input")?.focus();
  };

  sidebarToggles.forEach((button) => {
    button.addEventListener("click", () => setSidebarOpen(!document.body.classList.contains("sidebar-open")));
  });
  sidebarScrim?.addEventListener("click", () => setSidebarOpen(false));
  sidebar?.querySelectorAll("a").forEach((link) => {
    link.addEventListener("click", () => {
      if (window.matchMedia("(max-width: 960px)").matches) setSidebarOpen(false);
    });
  });
  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape") setSidebarOpen(false);
  });

  const openDeclarationTarget = () => {
    if (!window.location.hash) return;
    const target = document.getElementById(decodeURIComponent(window.location.hash.slice(1)));
    if (target instanceof HTMLDetailsElement) {
      target.open = true;
    }
  };

  openDeclarationTarget();
  window.addEventListener("hashchange", openDeclarationTarget);

  const tocLinks = [...document.querySelectorAll("[data-toc-link]")];
  const tocTargets = tocLinks
    .map((link) => ({ link, target: document.getElementById(decodeURIComponent(link.hash.slice(1))) }))
    .filter((item) => item.target);
  if (tocTargets.length && "IntersectionObserver" in window) {
    const tocObserver = new IntersectionObserver(
      (entries) => {
        const visible = entries
          .filter((entry) => entry.isIntersecting)
          .sort((left, right) => left.boundingClientRect.top - right.boundingClientRect.top)[0];
        if (!visible) return;
        tocLinks.forEach((link) => link.removeAttribute("aria-current"));
        tocTargets.find((item) => item.target === visible.target)?.link.setAttribute("aria-current", "location");
      },
      { rootMargin: "-15% 0px -70% 0px", threshold: 0 },
    );
    tocTargets.forEach((item) => tocObserver.observe(item.target));
  }

  const root = document.body.dataset.siteRoot || ".";
  const globalSearch = document.querySelector("[data-global-search]");
  const globalResults = document.querySelector("[data-global-results]");
  let searchIndex = null;

  const hideGlobalResults = () => {
    if (globalResults) {
      globalResults.hidden = true;
      globalResults.innerHTML = "";
    }
  };

  const renderGlobalResults = async () => {
    if (!globalSearch || !globalResults) return;
    const query = globalSearch.value.trim().toLowerCase();
    if (query.length < 2) {
      hideGlobalResults();
      return;
    }
    if (!searchIndex) {
      const response = await fetch(`${root}/search-index.json`);
      searchIndex = await response.json();
    }
    const terms = query.split(/\s+/).filter(Boolean);
    const matches = searchIndex
      .filter((item) => {
        const haystack = `${item.name} ${item.kind} ${item.module} ${item.chapter}`.toLowerCase();
        return terms.every((term) => haystack.includes(term));
      })
      .slice(0, 18);

    globalResults.innerHTML = matches.length
      ? matches
          .map(
            (item) =>
              `<li><a href="${root}/${item.url}"><code>${escapeHtml(item.name)}</code>` +
              `<span class="search-kind">${escapeHtml(item.kind)} · ${escapeHtml(item.module)}</span></a></li>`,
          )
          .join("")
      : `<li class="empty">No matching declaration.</li>`;
    globalResults.hidden = false;
  };

  const escapeHtml = (value) =>
    value.replace(/[&<>"']/g, (char) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[char]);

  globalSearch?.addEventListener("input", () => {
    renderGlobalResults().catch(() => hideGlobalResults());
  });
  globalSearch?.addEventListener("keydown", (event) => {
    if (event.key === "Escape") hideGlobalResults();
  });
  document.addEventListener("click", (event) => {
    if (!event.target.closest(".search-shell")) hideGlobalResults();
  });

  const catalog = document.querySelector("[data-catalog]");
  if (catalog) {
    const queryInput = document.querySelector("[data-catalog-query]");
    const kindSelect = document.querySelector("[data-catalog-kind]");
    const statusSelect = document.querySelector("[data-catalog-status]");
    const chapterSelect = document.querySelector("[data-catalog-chapter]");
    const rows = [...catalog.querySelectorAll("[data-catalog-row]")];
    const count = document.querySelector("[data-catalog-count]");

    const filterRows = () => {
      const query = (queryInput?.value || "").trim().toLowerCase();
      const terms = query.split(/\s+/).filter(Boolean);
      const kind = kindSelect?.value || "";
      const status = statusSelect?.value || "";
      const chapter = chapterSelect?.value || "";
      let visible = 0;
      rows.forEach((row) => {
        const haystack = row.dataset.search || "";
        const show =
          terms.every((term) => haystack.includes(term)) &&
          (!kind || row.dataset.kind === kind) &&
          (!status || row.dataset.status === status) &&
          (!chapter || row.dataset.chapter === chapter);
        row.hidden = !show;
        if (show) visible += 1;
      });
      if (count) count.textContent = `${visible.toLocaleString()} matching declarations`;
    };

    [queryInput, kindSelect, statusSelect, chapterSelect].forEach((control) => {
      control?.addEventListener("input", filterRows);
      control?.addEventListener("change", filterRows);
    });
    filterRows();
  }

  const mermaidBlocks = [...document.querySelectorAll(".mermaid")];
  if (mermaidBlocks.length) {
    import("https://cdn.jsdelivr.net/npm/mermaid@11/dist/mermaid.esm.min.mjs")
      .then(({ default: mermaid }) => {
        const styles = getComputedStyle(document.documentElement);
        mermaid.initialize({
          startOnLoad: false,
          securityLevel: "strict",
          theme: "base",
          flowchart: { htmlLabels: true, curve: "basis" },
          themeVariables: {
            background: styles.getPropertyValue("--surface").trim(),
            primaryColor: styles.getPropertyValue("--accent-soft").trim(),
            primaryTextColor: styles.getPropertyValue("--ink").trim(),
            primaryBorderColor: styles.getPropertyValue("--accent").trim(),
            lineColor: styles.getPropertyValue("--muted").trim(),
            secondaryColor: styles.getPropertyValue("--surface-2").trim(),
            tertiaryColor: styles.getPropertyValue("--bg").trim(),
            fontFamily: styles.getPropertyValue("--sans").trim(),
          },
        });
        return mermaid.run({ nodes: mermaidBlocks });
      })
      .catch((error) => {
        mermaidBlocks.forEach((block) => {
          block.insertAdjacentHTML(
            "beforebegin",
            `<p class="callout warning">Diagram rendering could not start. The editable Mermaid source remains visible below.</p>`,
          );
          block.style.whiteSpace = "pre-wrap";
        });
        console.error(error);
      });
  }
})();
