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
  const siteContent = document.querySelector(".site-content");
  const sidebarMedia = window.matchMedia("(max-width: 960px)");
  let sidebarTrigger = null;
  const sidebarFocusable = () =>
    [...(sidebar?.querySelectorAll('a[href], button:not([disabled]), summary, input:not([disabled]), select:not([disabled]), [tabindex]:not([tabindex="-1"])') || [])]
      .filter((element) => !element.hidden && element.getClientRects().length);
  const syncSidebarAccessibility = (open) => {
    const sidebarUnavailable = sidebarMedia.matches && !open;
    if (sidebar) {
      if ("inert" in sidebar) sidebar.inert = sidebarUnavailable;
      if (sidebarUnavailable) sidebar.setAttribute("aria-hidden", "true");
      else sidebar.removeAttribute("aria-hidden");
    }
    if (siteContent && "inert" in siteContent) siteContent.inert = sidebarMedia.matches && open;
  };
  const setSidebarOpen = (open, trigger = null) => {
    const wasOpen = document.body.classList.contains("sidebar-open");
    if (open && trigger) sidebarTrigger = trigger;
    document.body.classList.toggle("sidebar-open", open);
    sidebarToggles.forEach((button) => button.setAttribute("aria-expanded", String(open)));
    sidebarScrim?.setAttribute("aria-hidden", String(!open));
    syncSidebarAccessibility(open);
    if (open) {
      sidebar?.querySelector(".sidebar-close")?.focus();
    } else if (wasOpen) {
      sidebarTrigger?.focus();
      sidebarTrigger = null;
    }
  };

  sidebarToggles.forEach((button) => {
    button.addEventListener("click", () =>
      setSidebarOpen(!document.body.classList.contains("sidebar-open"), button),
    );
  });
  sidebarScrim?.addEventListener("click", () => setSidebarOpen(false));
  sidebar?.querySelectorAll("a").forEach((link) => {
    link.addEventListener("click", () => {
      if (window.matchMedia("(max-width: 960px)").matches) setSidebarOpen(false);
    });
  });
  document.addEventListener("keydown", (event) => {
    if (event.defaultPrevented) return;
    if (event.key === "Escape" && document.body.classList.contains("sidebar-open")) {
      event.preventDefault();
      setSidebarOpen(false);
      return;
    }
    if (
      event.key === "Tab" &&
      document.body.classList.contains("sidebar-open") &&
      window.matchMedia("(max-width: 960px)").matches
    ) {
      const focusable = sidebarFocusable();
      if (!focusable.length) return;
      const first = focusable[0];
      const last = focusable[focusable.length - 1];
      if (event.shiftKey && document.activeElement === first) {
        event.preventDefault();
        last.focus();
      } else if (!event.shiftKey && document.activeElement === last) {
        event.preventDefault();
        first.focus();
      }
    }
  });
  window.addEventListener("resize", () => {
    if (!sidebarMedia.matches && document.body.classList.contains("sidebar-open")) {
      setSidebarOpen(false);
    } else {
      syncSidebarAccessibility(document.body.classList.contains("sidebar-open"));
    }
  });
  syncSidebarAccessibility(false);

  const navGroups = [...document.querySelectorAll("[data-nav-group]")];
  const navStateKey = "abrl-nav-groups-v2";
  let navGroupState = {};
  try {
    navGroupState = JSON.parse(localStorage.getItem(navStateKey) || "{}") || {};
  } catch (_error) {
    navGroupState = {};
  }
  let syncingNavGroups = false;
  const syncNavGroups = () => {
    syncingNavGroups = true;
    navGroups.forEach((group) => {
      const key = group.dataset.navGroup;
      const saved = typeof navGroupState[key] === "boolean" ? navGroupState[key] : null;
      const active = group.dataset.navGroupActive === "true";
      const defaultOpen = sidebarMedia.matches && key === "start";
      group.open = active || (saved ?? defaultOpen);
    });
    syncingNavGroups = false;
  };
  navGroups.forEach((group) => {
    group.addEventListener("toggle", () => {
      if (syncingNavGroups) return;
      navGroupState[group.dataset.navGroup] = group.open;
      try {
        localStorage.setItem(navStateKey, JSON.stringify(navGroupState));
      } catch (_error) {
        // The native details interaction remains usable when storage is unavailable.
      }
    });
  });
  syncNavGroups();
  sidebarMedia.addEventListener?.("change", syncNavGroups);

  const focusedFragments = new Set();
  const openDeclarationTarget = () => {
    if (!window.location.hash) return;
    const expectedHash = window.location.hash;
    const target = document.getElementById(decodeURIComponent(expectedHash.slice(1)));
    if (!target) return;
    let disclosure = target instanceof HTMLDetailsElement
      ? target
      : target.parentElement?.closest("details");
    while (disclosure) {
      disclosure.open = true;
      disclosure = disclosure.parentElement?.closest("details");
    }
    const focusTarget = target instanceof HTMLDetailsElement
      ? target.querySelector(":scope > summary")
      : target.matches("h1, h2, h3, h4, h5, h6, summary, a, button, input, select, textarea")
        ? target
        : target.querySelector("h1, h2, h3, h4, h5, h6, summary") || target;
    const focusFragmentTarget = () => {
      if (!(focusTarget instanceof HTMLElement)) return;
      if (target.contains(document.activeElement)) return;
      if (
        focusedFragments.has(expectedHash)
        && document.activeElement !== document.body
        && document.activeElement !== document.documentElement
      ) return;
      if (!focusTarget.matches("summary, a, button, input, select, textarea, [tabindex]")) {
        focusTarget.tabIndex = -1;
      }
      focusTarget.focus({ preventScroll: true });
      focusedFragments.add(expectedHash);
    };
    const bringTargetIntoView = () => {
      if (window.location.hash !== expectedHash) return;
      focusFragmentTarget();
      const rect = target.getBoundingClientRect();
      const headerClearance = 96;
      const alreadyVisible = rect.top >= headerClearance && rect.top <= window.innerHeight * 0.55;
      if (!alreadyVisible) target.scrollIntoView({ block: "start" });
    };
    window.requestAnimationFrame(() => window.requestAnimationFrame(bringTargetIntoView));
    [180, 700, 1800, 3600].forEach((delay) => window.setTimeout(bringTargetIntoView, delay));
    document.fonts?.ready.then(bringTargetIntoView);
    window.MathJax?.startup?.promise?.then(bringTargetIntoView);
  };

  openDeclarationTarget();
  window.addEventListener("load", openDeclarationTarget);
  window.addEventListener("hashchange", openDeclarationTarget);

  const tocLinks = [...document.querySelectorAll("[data-toc-link]")];
  const pageToc = document.querySelector("[data-page-toc]");
  const tocToggle = document.querySelector("[data-toc-toggle]");
  const tocCurrent = document.querySelector("[data-toc-current]");
  const setTocOpen = (open) => {
    pageToc?.classList.toggle("toc-open", open);
    tocToggle?.setAttribute("aria-expanded", String(open));
  };
  tocToggle?.addEventListener("click", () => setTocOpen(!pageToc?.classList.contains("toc-open")));
  tocLinks.forEach((link) => {
    link.addEventListener("click", () => {
      if (window.matchMedia("(max-width: 760px)").matches) setTocOpen(false);
    });
  });
  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape" && pageToc?.classList.contains("toc-open")) {
      event.preventDefault();
      setTocOpen(false);
      tocToggle?.focus();
    }
  });
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
        const currentLink = tocTargets.find((item) => item.target === visible.target)?.link;
        currentLink?.setAttribute("aria-current", "location");
        if (tocCurrent && currentLink) tocCurrent.textContent = currentLink.textContent;
      },
      { rootMargin: "-15% 0px -70% 0px", threshold: 0 },
    );
    tocTargets.forEach((item) => tocObserver.observe(item.target));
  }

  const root = document.body.dataset.siteRoot || ".";
  const globalSearch = document.querySelector("[data-global-search]");
  const globalResults = document.querySelector("[data-global-results]");
  let searchIndex = null;

  document.addEventListener("keydown", (event) => {
    const target = event.target;
    const isTyping = target instanceof HTMLElement && (
      target.isContentEditable || target.matches("input, textarea, select")
    );
    if (
      event.key !== "/" || event.altKey || event.ctrlKey || event.metaKey ||
      event.shiftKey || isTyping
    ) return;
    event.preventDefault();
    if (sidebarMedia.matches) {
      setSidebarOpen(true, document.querySelector(".sidebar-toggle"));
    }
    window.requestAnimationFrame(() => globalSearch?.focus());
  });

  const hideGlobalResults = () => {
    if (globalResults) {
      globalResults.hidden = true;
      globalResults.innerHTML = "";
    }
    globalSearch?.setAttribute("aria-expanded", "false");
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
              `<li role="none"><a role="option" href="${root}/${item.url}"><code>${escapeHtml(item.name)}</code>` +
              `<span class="search-kind">${escapeHtml(item.kind)} · ${escapeHtml(item.module)}</span></a></li>`,
          )
          .join("")
      : `<li class="empty">No matching declaration.</li>`;
    globalResults.hidden = false;
    globalSearch.setAttribute("aria-expanded", "true");
  };

  const escapeHtml = (value) =>
    value.replace(/[&<>"']/g, (char) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[char]);

  globalSearch?.addEventListener("input", () => {
    renderGlobalResults().catch(() => hideGlobalResults());
  });
  globalSearch?.addEventListener("keydown", (event) => {
    if (event.key === "Escape") hideGlobalResults();
    if (event.key === "ArrowDown" && globalResults && !globalResults.hidden) {
      event.preventDefault();
      globalResults.querySelector("a")?.focus();
    }
  });
  globalResults?.addEventListener("keydown", (event) => {
    const links = [...globalResults.querySelectorAll("a")];
    const index = links.indexOf(document.activeElement);
    if (event.key === "ArrowDown" && index >= 0) {
      event.preventDefault();
      links[Math.min(index + 1, links.length - 1)]?.focus();
    } else if (event.key === "ArrowUp" && index >= 0) {
      event.preventDefault();
      if (index === 0) globalSearch?.focus();
      else links[index - 1]?.focus();
    } else if (event.key === "Escape") {
      event.preventDefault();
      hideGlobalResults();
      globalSearch?.focus();
    }
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
    const catalogBody = catalog.querySelector("[data-catalog-body]");
    const count = document.querySelector("[data-catalog-count]");
    const moreButton = document.querySelector("[data-catalog-more]");
    let catalogItems = null;
    let catalogLoadPromise = null;
    let catalogPageSize = 100;
    let catalogVisibleLimit = catalogPageSize;

    const catalogRow = (item) =>
      `<tr data-catalog-row>` +
      `<td><a href="${escapeHtml(item.url)}"><code>${escapeHtml(item.name)}</code></a></td>` +
      `<td>${escapeHtml(item.kind_label)}</td>` +
      `<td>${escapeHtml(item.chapter_title)}</td>` +
      `<td><a href="${escapeHtml(item.module_url)}"><code>${escapeHtml(item.module)}</code></a></td>` +
      `<td><span class="status ${escapeHtml(item.status)}">${escapeHtml(item.status_label)}</span></td>` +
      `<td><a href="${escapeHtml(item.source_url)}">${escapeHtml(item.source_label)}</a></td>` +
      `</tr>`;

    const renderCatalog = () => {
      if (!catalogItems || !catalogBody) return;
      const query = (queryInput?.value || "").trim().toLowerCase();
      const terms = query.split(/\s+/).filter(Boolean);
      const kind = kindSelect?.value || "";
      const status = statusSelect?.value || "";
      const chapter = chapterSelect?.value || "";
      const matches = catalogItems.filter(
        (item) =>
          terms.every((term) => item.search.includes(term)) &&
          (!kind || item.kind === kind) &&
          (!status || item.status === status) &&
          (!chapter || item.chapter === chapter),
      );
      const visibleItems = matches.slice(0, catalogVisibleLimit);
      catalogBody.innerHTML = visibleItems.length
        ? visibleItems.map(catalogRow).join("")
        : '<tr><td colspan="6" class="empty">No matching declaration.</td></tr>';
      if (count) {
        count.textContent = matches.length
          ? `Showing ${visibleItems.length.toLocaleString()} of ${matches.length.toLocaleString()} matching declarations`
          : "No matching declarations";
      }
      if (moreButton) {
        const remaining = Math.max(0, matches.length - visibleItems.length);
        moreButton.hidden = remaining === 0;
        moreButton.textContent = remaining
          ? `Show ${Math.min(catalogPageSize, remaining).toLocaleString()} more declarations`
          : "All matching declarations shown";
      }
    };

    const loadCatalog = () => {
      if (catalogItems) return Promise.resolve();
      if (catalogLoadPromise) return catalogLoadPromise;
      catalog.setAttribute("aria-busy", "true");
      catalogLoadPromise = fetch(`${root}/catalog-data.json`)
        .then((response) => {
          if (!response.ok) throw new Error(`Catalog request failed with ${response.status}`);
          return response.json();
        })
        .then((payload) => {
          const kindLabels = payload.kind_labels || {};
          const statusLabels = payload.status_labels || {};
          const sourceBase = payload.source_base || "";
          catalogItems = Array.isArray(payload.items)
            ? payload.items.map((row) => {
                const [name, kind, module, moduleSlug, chapter, chapterTitle, status, file, line, anchor] = row;
                return {
                  name,
                  kind,
                  kind_label: kindLabels[kind] || kind,
                  module,
                  module_url: `../modules/${moduleSlug}/index.html`,
                  chapter,
                  chapter_title: chapterTitle,
                  status,
                  status_label: statusLabels[status] || status,
                  url: `../modules/${moduleSlug}/index.html#${anchor}`,
                  source_url: `${sourceBase}${file}#L${line}`,
                  source_label: `${file}:${line}`,
                  search: `${name} ${kind} ${module} ${file} ${chapterTitle}`.toLowerCase(),
                };
              })
            : [];
          catalogPageSize = Number.isInteger(payload.page_size) ? payload.page_size : 100;
        })
        .finally(() => catalog.setAttribute("aria-busy", "false"));
      return catalogLoadPromise;
    };

    const resetAndRenderCatalog = () => {
      catalogVisibleLimit = catalogPageSize;
      loadCatalog().then(renderCatalog).catch(() => {
        if (count) count.textContent = "Full catalog could not load; showing the initial declarations.";
        if (moreButton) moreButton.hidden = true;
      });
    };

    [queryInput, kindSelect, statusSelect, chapterSelect].forEach((control) => {
      control?.addEventListener("input", resetAndRenderCatalog);
      control?.addEventListener("change", resetAndRenderCatalog);
    });
    moreButton?.addEventListener("click", () => {
      catalogVisibleLimit += catalogPageSize;
      loadCatalog().then(renderCatalog).catch(() => {
        if (count) count.textContent = "Full catalog could not load; showing the initial declarations.";
        moreButton.hidden = true;
      });
    });
    if (moreButton) moreButton.hidden = false;
  }

  const installTableFilter = ({ listSelector, rowSelector, querySelector, countSelector, statusSelector, chapterSelector, noun }) => {
    const list = document.querySelector(listSelector);
    if (!list) return;
    const rows = [...list.querySelectorAll(rowSelector)];
    const queryInput = document.querySelector(querySelector);
    const statusInput = statusSelector ? document.querySelector(statusSelector) : null;
    const chapterInput = chapterSelector ? document.querySelector(chapterSelector) : null;
    const count = document.querySelector(countSelector);
    const filter = () => {
      const terms = (queryInput?.value || "").trim().toLowerCase().split(/\s+/).filter(Boolean);
      const status = statusInput?.value || "";
      const chapter = chapterInput?.value || "";
      let visible = 0;
      rows.forEach((row) => {
        const show = terms.every((term) => (row.dataset.search || "").includes(term)) &&
          (!status || row.dataset.status === status) &&
          (!chapter || row.dataset.chapter === chapter);
        row.hidden = !show;
        if (show) visible += 1;
      });
      if (count) count.textContent = `${visible.toLocaleString()} matching ${noun}`;
    };
    [queryInput, statusInput, chapterInput].forEach((control) => {
      control?.addEventListener("input", filter);
      control?.addEventListener("change", filter);
    });
    filter();
  };

  const milestoneList = document.querySelector("[data-milestone-list]");
  if (milestoneList) {
    const milestoneBody = milestoneList.querySelector("[data-milestone-body]");
    const milestoneQuery = document.querySelector("[data-milestone-query]");
    const milestoneStatus = document.querySelector("[data-milestone-status]");
    const milestoneChapter = document.querySelector("[data-milestone-chapter]");
    const milestoneCount = document.querySelector("[data-milestone-count]");
    const milestoneMore = document.querySelector("[data-milestone-more]");
    const milestonePageSize = Number(milestoneList.dataset.milestonePageSize || 20);
    const milestoneTotal = Number(milestoneList.dataset.milestoneTotal || 0);
    let milestoneVisibleLimit = milestonePageSize;
    let milestoneItems = null;
    let milestoneLoadPromise = null;

    const loadMilestones = () => {
      if (milestoneItems) return Promise.resolve(milestoneItems);
      if (!milestoneLoadPromise) {
        const dataUrl = new URL("milestone-data.json", window.location.href);
        milestoneLoadPromise = fetch(dataUrl)
          .then((response) => {
            if (!response.ok) throw new Error(`Milestone ledger request failed: ${response.status}`);
            return response.json();
          })
          .then((payload) => {
            milestoneItems = Array.isArray(payload.items) ? payload.items : [];
            return milestoneItems;
          });
      }
      return milestoneLoadPromise;
    };

    const renderMilestones = () => {
      if (!milestoneItems || !milestoneBody) return;
      const terms = (milestoneQuery?.value || "").trim().toLowerCase().split(/\s+/).filter(Boolean);
      const status = milestoneStatus?.value || "";
      const chapter = milestoneChapter?.value || "";
      const filtered = milestoneItems.filter((item) =>
        terms.every((term) => (item.search || "").includes(term))
        && (!status || item.status === status)
        && (!chapter || item.chapter === chapter)
      );
      const visible = filtered.slice(0, milestoneVisibleLimit);
      milestoneBody.innerHTML = visible.map((item) => item.html).join("");
      if (milestoneCount) {
        milestoneCount.textContent = filtered.length > visible.length
          ? `Showing ${visible.length.toLocaleString()} of ${filtered.length.toLocaleString()} matching milestones.`
          : `${filtered.length.toLocaleString()} matching milestones.`;
      }
      if (milestoneMore) {
        const remaining = Math.max(0, filtered.length - visible.length);
        milestoneMore.hidden = remaining === 0;
        milestoneMore.textContent = `Show ${Math.min(milestonePageSize, remaining).toLocaleString()} more milestones`;
      }
    };

    const resetAndRenderMilestones = () => {
      milestoneVisibleLimit = milestonePageSize;
      loadMilestones().then(renderMilestones).catch(() => {
        if (milestoneCount) milestoneCount.textContent = "Full milestone ledger could not load; showing the initial milestones.";
        if (milestoneMore) milestoneMore.hidden = true;
      });
    };
    [milestoneQuery, milestoneStatus, milestoneChapter].forEach((control) => {
      control?.addEventListener("input", resetAndRenderMilestones);
      control?.addEventListener("change", resetAndRenderMilestones);
    });
    milestoneMore?.addEventListener("click", () => {
      milestoneVisibleLimit += milestonePageSize;
      loadMilestones().then(renderMilestones).catch(() => {
        if (milestoneMore) milestoneMore.hidden = true;
      });
    });
    if (milestoneMore && milestoneTotal > milestonePageSize) milestoneMore.hidden = false;

    const revealMilestoneFragment = () => {
      const fragmentId = window.location.hash ? decodeURIComponent(window.location.hash.slice(1)) : "";
      if (!fragmentId || document.getElementById(fragmentId)) return;
      loadMilestones().then((items) => {
        if (!items.some((item) => item.id === fragmentId)) return;
        milestoneVisibleLimit = items.length;
        renderMilestones();
        openDeclarationTarget();
      }).catch(() => {});
    };
    revealMilestoneFragment();
    window.addEventListener("hashchange", revealMilestoneFragment);
  }
  installTableFilter({
    listSelector: "[data-module-list]",
    rowSelector: "[data-module-row]",
    querySelector: "[data-module-query]",
    countSelector: "[data-module-count]",
    noun: "modules",
  });

  const revealRenderedMath = (markFallback = false) => {
    document.querySelectorAll("[data-math-statement]").forEach((statement) => {
      const rendered = Boolean(statement.querySelector("mjx-container"));
      statement.classList.toggle("math-rendered", rendered);
      statement.classList.toggle("math-fallback-active", markFallback && !rendered);
      const tex = statement.querySelector(".math-tex");
      if (tex) tex.setAttribute("aria-hidden", String(!rendered));
      const fallback = statement.querySelector(".math-fallback");
      if (fallback) fallback.setAttribute("aria-hidden", String(rendered));
    });
  };
  window.addEventListener("load", revealRenderedMath);
  [300, 1200].forEach((delay) => window.setTimeout(revealRenderedMath, delay));
  window.setTimeout(() => revealRenderedMath(true), 3200);

  const labelOverflowRegions = () => {
    document.querySelectorAll(".diagram, .table-wrap, .lean-code, .math-statement").forEach((region) => {
      const mathTarget = region.matches(".math-statement")
        ? region.querySelector("mjx-container")
        : null;
      const regionOverflows = region.scrollWidth > region.clientWidth + 2;
      const mathTargetOverflows = Boolean(
        mathTarget && mathTarget.scrollWidth > mathTarget.clientWidth + 2,
      );
      const isScrollable = regionOverflows || mathTargetOverflows;
      region.classList.toggle("is-scrollable", isScrollable);
      if (!isScrollable) return;
      if (!region.hasAttribute("tabindex")) region.tabIndex = 0;
      if (!region.hasAttribute("role")) region.setAttribute("role", "region");
      if (!region.hasAttribute("aria-label")) {
        region.setAttribute("aria-label", "Horizontally scrollable content");
      }
    });
  };
  window.addEventListener("load", labelOverflowRegions);
  window.addEventListener("resize", labelOverflowRegions);
  [300, 1200, 3200].forEach((delay) => window.setTimeout(labelOverflowRegions, delay));
  window.MathJax?.startup?.promise?.then(labelOverflowRegions);

  const enhanceLeanCodeBlocks = () => {
    document.querySelectorAll("pre.lean-code").forEach((block, index) => {
      if (block.dataset.codeEnhanced === "true") return;
      block.dataset.codeEnhanced = "true";
      const toolbar = document.createElement("div");
      toolbar.className = "code-toolbar";
      toolbar.setAttribute("role", "group");
      toolbar.setAttribute("aria-label", "Lean statement display options");
      toolbar.innerHTML =
        '<button type="button" class="code-tool" data-code-wrap aria-pressed="false">Wrap lines</button>' +
        '<button type="button" class="code-tool" data-code-copy>Copy statement</button>' +
        `<span class="code-tool-status" data-code-status aria-live="polite" id="code-status-${index}"></span>`;
      block.before(toolbar);

      const wrapButton = toolbar.querySelector("[data-code-wrap]");
      const copyButton = toolbar.querySelector("[data-code-copy]");
      const status = toolbar.querySelector("[data-code-status]");
      const syncWrapButton = () => {
        const wrapped = getComputedStyle(block).whiteSpace !== "pre";
        wrapButton?.setAttribute("aria-pressed", String(wrapped));
        if (wrapButton) wrapButton.textContent = wrapped ? "Use horizontal scroll" : "Wrap lines";
      };
      syncWrapButton();

      wrapButton?.addEventListener("click", () => {
        const wrapped = getComputedStyle(block).whiteSpace !== "pre";
        block.classList.toggle("wrap-lines", !wrapped);
        block.classList.toggle("scroll-lines", wrapped);
        syncWrapButton();
        labelOverflowRegions();
      });
      copyButton?.addEventListener("click", async () => {
        try {
          await navigator.clipboard.writeText(block.innerText);
          if (status) status.textContent = "Copied";
        } catch (_error) {
          if (status) status.textContent = "Copy unavailable; select the statement instead.";
        }
        window.setTimeout(() => {
          if (status) status.textContent = "";
        }, 2400);
      });
    });
  };
  enhanceLeanCodeBlocks();
  window.addEventListener("resize", () => {
    document.querySelectorAll("pre.lean-code:not(.wrap-lines):not(.scroll-lines)").forEach((block) => {
      const button = block.previousElementSibling?.querySelector?.("[data-code-wrap]");
      if (!button) return;
      const wrapped = getComputedStyle(block).whiteSpace !== "pre";
      button.setAttribute("aria-pressed", String(wrapped));
      button.textContent = wrapped ? "Use horizontal scroll" : "Wrap lines";
    });
  });

  const mermaidBlocks = [...document.querySelectorAll(".mermaid")];
  if (mermaidBlocks.length) {
    const fitFlowchartViewBoxes = () => {
      document.querySelectorAll('svg[aria-roledescription^="flowchart"]').forEach((svg) => {
        const viewBoxParts = (svg.getAttribute("viewBox") || "")
          .trim()
          .split(/\s+/)
          .map(Number);
        const svgRect = svg.getBoundingClientRect();
        if (
          viewBoxParts.length !== 4 ||
          viewBoxParts.some((value) => !Number.isFinite(value)) ||
          svgRect.width <= 0 ||
          svgRect.height <= 0
        ) return;

        const [viewX, viewY, viewWidth, viewHeight] = viewBoxParts;
        const scale = Math.min(svgRect.width / viewWidth, svgRect.height / viewHeight);
        if (!Number.isFinite(scale) || scale <= 0) return;
        const offsetX = svgRect.left + (svgRect.width - viewWidth * scale) / 2;
        const offsetY = svgRect.top + (svgRect.height - viewHeight * scale) / 2;
        const marks = [...svg.querySelectorAll(".node, path.flowchart-link")]
          .map((mark) => mark.getBoundingClientRect())
          .filter((rect) => rect.width > 0.5 || rect.height > 0.5);
        if (!marks.length) return;

        const toUserX = (value) => viewX + (value - offsetX) / scale;
        const toUserY = (value) => viewY + (value - offsetY) / scale;
        const minX = Math.min(...marks.map((rect) => toUserX(rect.left)));
        const maxX = Math.max(...marks.map((rect) => toUserX(rect.right)));
        const minY = Math.min(...marks.map((rect) => toUserY(rect.top)));
        const maxY = Math.max(...marks.map((rect) => toUserY(rect.bottom)));
        const contentWidth = maxX - minX;
        const contentHeight = maxY - minY;
        if (contentWidth <= 0 || contentHeight <= 0) return;

        const padding = Math.max(20, Math.min(contentWidth, contentHeight) * 0.05);
        svg.setAttribute(
          "viewBox",
          `${minX - padding} ${minY - padding} ${contentWidth + 2 * padding} ${contentHeight + 2 * padding}`,
        );
        svg.style.maxWidth = "none";
      });
    };

    import("https://cdn.jsdelivr.net/npm/mermaid@11.4.1/dist/mermaid.esm.min.mjs")
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
      .then(() => {
        window.requestAnimationFrame(() => {
          fitFlowchartViewBoxes();
          labelOverflowRegions();
        });
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
