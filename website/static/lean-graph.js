(() => {
  "use strict";

  const app = document.querySelector("[data-lean-graph]");
  if (!app) return;

  const svg = app.querySelector("[data-graph-svg]");
  const canvas = app.querySelector("[data-graph-canvas]");
  const detail = app.querySelector("[data-graph-detail]");
  const count = app.querySelector("[data-graph-count]");
  const empty = app.querySelector("[data-graph-empty]");
  const search = app.querySelector("[data-graph-search]");
  const suggestions = app.querySelector("[data-graph-suggestions]");
  const branchSizeSelect = app.querySelector("[data-graph-branch-size]");
  const viewButtons = [...app.querySelectorAll("[data-graph-view]")];
  const fitButton = app.querySelector("[data-graph-fit]");
  const resetButton = app.querySelector("[data-graph-reset]");

  const statusLabels = {
    compiled: "Compiled",
    prototype: "Prototype",
    partial: "Partial",
    planned: "Planned",
    proposed: "Proposed",
    blocked: "Blocked",
    stated: "Stated",
    source: "Source indexed",
  };
  const statusPriority = {
    compiled: 0,
    partial: 1,
    prototype: 2,
    source: 3,
    stated: 4,
    planned: 5,
    proposed: 6,
    blocked: 7,
  };
  const svgNS = "http://www.w3.org/2000/svg";
  const nodeWidth = 236;
  const nodeHeight = 68;
  const columnGap = 310;
  const rowGap = 92;
  const padding = 54;

  let data = null;
  let nodes = new Map();
  let children = new Map();
  let incoming = new Map();
  let outgoing = new Map();
  let visible = new Set();
  let baseVisible = new Set();
  let expandedCounts = new Map();
  let selectedId = null;
  let currentView = "overview";
  let branchSize = Number(branchSizeSelect?.value || 12);
  let viewport = null;
  let graphBounds = { x: 0, y: 0, width: 1, height: 1 };
  let transform = { x: 0, y: 0, scale: 1 };
  let dragging = null;

  const create = (tag, className = "", text = "") => {
    const element = document.createElement(tag);
    if (className) element.className = className;
    if (text) element.textContent = text;
    return element;
  };

  const createSvg = (tag, attributes = {}) => {
    const element = document.createElementNS(svgNS, tag);
    Object.entries(attributes).forEach(([name, value]) => element.setAttribute(name, String(value)));
    return element;
  };

  const truncate = (value, length) => {
    const text = String(value || "");
    return text.length <= length ? text : `${text.slice(0, length - 1)}…`;
  };

  const relationClass = (relation) =>
    String(relation || "relation").toLowerCase().replace(/[^a-z0-9]+/g, "-");

  const nodeDepth = (node) => {
    let depth = 0;
    let cursor = node;
    const seen = new Set();
    while (cursor?.parent && nodes.has(cursor.parent) && !seen.has(cursor.parent)) {
      seen.add(cursor.parent);
      depth += 1;
      cursor = nodes.get(cursor.parent);
    }
    return depth;
  };

  const sortNodes = (leftId, rightId) => {
    const left = nodes.get(leftId);
    const right = nodes.get(rightId);
    const orderDelta = Number(left?.order || 0) - Number(right?.order || 0);
    if (orderDelta) return orderDelta;
    const statusDelta = (statusPriority[left?.status] ?? 99) - (statusPriority[right?.status] ?? 99);
    if (statusDelta) return statusDelta;
    return String(left?.label || "").localeCompare(String(right?.label || ""));
  };

  const addAncestors = (nodeId, target = visible) => {
    let cursor = nodes.get(nodeId);
    const seen = new Set();
    while (cursor && !seen.has(cursor.id)) {
      seen.add(cursor.id);
      target.add(cursor.id);
      cursor = cursor.parent ? nodes.get(cursor.parent) : null;
    }
  };

  const addChildren = (nodeId, more = false) => {
    const allChildren = children.get(nodeId) || [];
    if (!allChildren.length) return;
    const start = more ? expandedCounts.get(nodeId) || 0 : 0;
    const end = Math.min(allChildren.length, start + branchSize);
    allChildren.slice(0, end).forEach((childId) => {
      addAncestors(childId);
      visible.add(childId);
    });
    expandedCounts.set(nodeId, end);
  };

  const collapseBranch = (nodeId) => {
    const removeDescendants = (parentId) => {
      (children.get(parentId) || []).forEach((childId) => {
        removeDescendants(childId);
        if (!baseVisible.has(childId)) visible.delete(childId);
        expandedCounts.delete(childId);
      });
    };
    removeDescendants(nodeId);
    expandedCounts.delete(nodeId);
    if (!visible.has(selectedId)) selectedId = nodeId;
  };

  const setViewButtonState = (view) => {
    viewButtons.forEach((button) => {
      button.setAttribute("aria-pressed", String(button.dataset.graphView === view));
    });
  };

  const setView = (view) => {
    currentView = data.views[view] ? view : "overview";
    visible = new Set(data.views[currentView]);
    baseVisible = new Set(visible);
    expandedCounts = new Map();
    selectedId =
      currentView === "book" || currentView === "modules"
        ? "group:book-map"
        : currentView === "spine"
          ? "group:textbook-spine"
          : currentView === "milestones"
            ? "group:milestones"
            : data.root;
    if (currentView === "milestones") addChildren("group:milestones");
    setViewButtonState(currentView);
    render({ fit: true, focusId: null });
  };

  const selectNode = (nodeId, expand = true) => {
    if (!nodes.has(nodeId)) return;
    selectedId = nodeId;
    addAncestors(nodeId);
    if (expand && (children.get(nodeId) || []).length && !expandedCounts.has(nodeId)) {
      addChildren(nodeId);
    }
    render({ fit: false, focusId: nodeId });
  };

  const revealSearchResult = (nodeId) => {
    if (!nodes.has(nodeId)) return;
    currentView = "search";
    setViewButtonState("");
    visible = new Set();
    expandedCounts = new Map();
    addAncestors(nodeId);
    const related = [
      ...(incoming.get(nodeId) || []).filter((edge) => edge.relation !== "contains"),
      ...(outgoing.get(nodeId) || []).filter((edge) => edge.relation !== "contains"),
    ].slice(0, branchSize);
    related.forEach((edge) => {
      addAncestors(edge.source);
      addAncestors(edge.target);
    });
    baseVisible = new Set(visible);
    selectedId = nodeId;
    hideSuggestions();
    render({ fit: true, focusId: nodeId });
  };

  const edgeIsVisible = (edge) => visible.has(edge.source) && visible.has(edge.target);

  const computeLayout = () => {
    const columns = new Map();
    [...visible].forEach((nodeId) => {
      const node = nodes.get(nodeId);
      if (!node) return;
      const depth = nodeDepth(node);
      if (!columns.has(depth)) columns.set(depth, []);
      columns.get(depth).push(nodeId);
    });
    columns.forEach((ids) => ids.sort(sortNodes));
    const maxRows = Math.max(1, ...[...columns.values()].map((ids) => ids.length));
    const positions = new Map();
    let maxDepth = 0;
    columns.forEach((ids, depth) => {
      maxDepth = Math.max(maxDepth, depth);
      const columnHeight = Math.max(nodeHeight, (ids.length - 1) * rowGap + nodeHeight);
      const maximumHeight = Math.max(nodeHeight, (maxRows - 1) * rowGap + nodeHeight);
      const offsetY = padding + (maximumHeight - columnHeight) / 2;
      ids.forEach((nodeId, index) => {
        positions.set(nodeId, {
          x: padding + depth * columnGap,
          y: offsetY + index * rowGap,
        });
      });
    });
    graphBounds = {
      x: 0,
      y: 0,
      width: padding * 2 + maxDepth * columnGap + nodeWidth,
      height: padding * 2 + Math.max(nodeHeight, (maxRows - 1) * rowGap + nodeHeight),
    };
    return positions;
  };

  const appendText = (parent, value, x, y, className, maxLength) => {
    const text = createSvg("text", { x, y, class: className });
    text.textContent = truncate(value, maxLength);
    parent.append(text);
  };

  const updateTransform = () => {
    if (!viewport) return;
    viewport.setAttribute(
      "transform",
      `translate(${transform.x.toFixed(2)} ${transform.y.toFixed(2)}) scale(${transform.scale.toFixed(4)})`,
    );
  };

  const fitGraph = () => {
    if (!canvas || !viewport) return;
    const width = Math.max(320, canvas.clientWidth);
    const height = Math.max(420, canvas.clientHeight - 26);
    const scale = Math.min(
      1.15,
      Math.max(0.18, (width - 42) / graphBounds.width),
      Math.max(0.18, (height - 42) / graphBounds.height),
    );
    transform = {
      scale,
      x: (width - graphBounds.width * scale) / 2,
      y: (height - graphBounds.height * scale) / 2,
    };
    updateTransform();
  };

  const makeNeighborButton = (edge, direction) => {
    const nodeId = direction === "incoming" ? edge.source : edge.target;
    const node = nodes.get(nodeId);
    const button = create("button", "lean-graph-neighbor");
    button.type = "button";
    button.dataset.graphNeighbor = nodeId;
    const relation = create("span", "lean-graph-neighbor-relation", edge.relation);
    const label = create("strong", "", node?.label || nodeId);
    const kind = create("small", "", node?.kind || "node");
    button.append(relation, label, kind);
    return button;
  };

  const renderNeighborSection = (heading, edgeList, direction) => {
    const section = create("section", "lean-graph-neighbors");
    const title = create("h3", "", `${heading} · ${edgeList.length}`);
    section.append(title);
    if (!edgeList.length) {
      section.append(create("p", "empty", "No recorded neighbor in this generated graph."));
      return section;
    }
    const list = create("div", "lean-graph-neighbor-list");
    edgeList.slice(0, 18).forEach((edge) => list.append(makeNeighborButton(edge, direction)));
    section.append(list);
    if (edgeList.length > 18) {
      section.append(create("p", "lean-graph-overflow", `${edgeList.length - 18} additional neighbors are available through search or branch expansion.`));
    }
    return section;
  };

  const renderDetail = () => {
    const node = nodes.get(selectedId);
    if (!node) return;
    detail.replaceChildren();

    const header = create("header", "lean-graph-detail-header");
    const headingWrap = create("div");
    headingWrap.append(create("span", "lean-graph-kind", node.kind), create("h2", "", node.label));
    const status = create("span", `status ${node.status}`, statusLabels[node.status] || node.status);
    header.append(headingWrap, status);
    detail.append(header);
    if (node.subtitle) detail.append(create("p", "lean-graph-subtitle", node.subtitle));
    if (node.description) detail.append(create("p", "lean-graph-description", node.description));

    if (node.meta?.length) {
      const meta = create("dl", "lean-graph-meta");
      node.meta.forEach(([term, value]) => {
        const row = create("div");
        row.append(create("dt", "", term), create("dd", "", value));
        meta.append(row);
      });
      detail.append(meta);
    }

    if (node.statement) {
      const statement = create("details", "lean-graph-statement");
      statement.append(create("summary", "", "Exact indexed Lean statement"));
      const pre = create("pre", "lean-code");
      pre.tabIndex = 0;
      pre.append(create("code", "", node.statement));
      statement.append(pre);
      detail.append(statement);
    }

    if (node.missing?.length) {
      const gaps = create("details", "lean-graph-gaps");
      gaps.append(create("summary", "", `Open boundary · ${node.missing.length}`));
      const list = create("ul");
      node.missing.slice(0, 8).forEach((item) => list.append(create("li", "", item)));
      gaps.append(list);
      detail.append(gaps);
    }

    const actions = create("div", "lean-graph-detail-actions");
    if (node.url) {
      const link = create("a", "button primary", "Open reader / Lean card ↗");
      link.href = node.url;
      actions.append(link);
    }
    const childList = children.get(node.id) || [];
    const shown = expandedCounts.get(node.id) || 0;
    if (childList.length && shown < childList.length) {
      const more = create(
        "button",
        "button",
        shown ? `Show ${Math.min(branchSize, childList.length - shown)} more` : `Open first ${Math.min(branchSize, childList.length)} children`,
      );
      more.type = "button";
      more.dataset.graphMore = node.id;
      actions.append(more);
    }
    if (shown) {
      const collapse = create("button", "button", "Collapse branch");
      collapse.type = "button";
      collapse.dataset.graphCollapse = node.id;
      actions.append(collapse);
    }
    detail.append(actions);

    const incomingEdges = (incoming.get(node.id) || []).slice().sort((a, b) => a.relation.localeCompare(b.relation));
    const outgoingEdges = (outgoing.get(node.id) || []).slice().sort((a, b) => a.relation.localeCompare(b.relation));
    detail.append(
      renderNeighborSection("Prerequisites / parents", incomingEdges, "incoming"),
      renderNeighborSection("Consumers / children", outgoingEdges, "outgoing"),
    );
  };

  const render = ({ fit = false, focusId = null } = {}) => {
    const positions = computeLayout();
    const defs = createSvg("defs");
    const marker = createSvg("marker", {
      id: "lean-graph-arrow",
      viewBox: "0 0 10 10",
      refX: 8,
      refY: 5,
      markerWidth: 5,
      markerHeight: 5,
      orient: "auto-start-reverse",
    });
    marker.append(createSvg("path", { d: "M 0 0 L 10 5 L 0 10 z", class: "lean-graph-arrow" }));
    defs.append(marker);
    viewport = createSvg("g", { class: "lean-graph-viewport" });
    const edgeLayer = createSvg("g", { class: "lean-graph-edges" });
    const nodeLayer = createSvg("g", { class: "lean-graph-nodes" });

    const visibleEdges = data.edges.filter(edgeIsVisible);
    visibleEdges.forEach((edge) => {
      const source = positions.get(edge.source);
      const target = positions.get(edge.target);
      if (!source || !target) return;
      const x1 = source.x + nodeWidth;
      const y1 = source.y + nodeHeight / 2;
      const x2 = target.x;
      const y2 = target.y + nodeHeight / 2;
      const middle = x1 + (x2 - x1) * 0.5;
      const path = createSvg("path", {
        d: `M ${x1} ${y1} C ${middle} ${y1}, ${middle} ${y2}, ${x2} ${y2}`,
        class: `lean-graph-edge relation-${relationClass(edge.relation)}${edge.source === selectedId || edge.target === selectedId ? " is-related" : ""}`,
        "marker-end": "url(#lean-graph-arrow)",
      });
      edgeLayer.append(path);
      if ((edge.source === selectedId || edge.target === selectedId) && edge.relation !== "contains") {
        const label = createSvg("text", {
          x: middle,
          y: (y1 + y2) / 2 - 5,
          class: "lean-graph-edge-label",
          "text-anchor": "middle",
        });
        label.textContent = edge.relation;
        edgeLayer.append(label);
      }
    });

    [...visible].sort(sortNodes).forEach((nodeId) => {
      const node = nodes.get(nodeId);
      const position = positions.get(nodeId);
      if (!node || !position) return;
      const group = createSvg("g", {
        class: `lean-graph-node status-${relationClass(node.status)} kind-${relationClass(node.kind)}${nodeId === selectedId ? " is-selected" : ""}`,
        transform: `translate(${position.x} ${position.y})`,
        tabindex: "0",
        role: "button",
        "data-node-id": nodeId,
        "aria-label": `${node.kind}: ${node.label}. ${statusLabels[node.status] || node.status}`,
      });
      group.append(createSvg("rect", { width: nodeWidth, height: nodeHeight, rx: 11, ry: 11 }));
      appendText(group, node.kind, 14, 17, "lean-graph-node-kind", 30);
      appendText(group, node.label, 14, 40, "lean-graph-node-label", 31);
      appendText(group, statusLabels[node.status] || node.status, 14, 58, "lean-graph-node-status", 24);
      const childTotal = (children.get(nodeId) || []).length;
      if (childTotal) appendText(group, `${childTotal} children`, nodeWidth - 12, 58, "lean-graph-node-count", 18);
      const activate = (event) => {
        event.stopPropagation();
        selectNode(nodeId, true);
      };
      group.addEventListener("click", activate);
      group.addEventListener("keydown", (event) => {
        if (event.key === "Enter" || event.key === " ") {
          event.preventDefault();
          activate(event);
        }
      });
      nodeLayer.append(group);
    });

    viewport.append(edgeLayer, nodeLayer);
    svg.replaceChildren(defs, viewport);
    svg.setAttribute("viewBox", `0 0 ${Math.max(320, canvas.clientWidth)} ${Math.max(420, canvas.clientHeight - 26)}`);
    empty.hidden = visible.size > 0;
    count.textContent = `${visible.size.toLocaleString()} visible nodes · ${visibleEdges.length.toLocaleString()} visible edges`;
    renderDetail();
    updateTransform();

    requestAnimationFrame(() => {
      if (fit) fitGraph();
      if (focusId) {
        const target = [...svg.querySelectorAll("[data-node-id]")].find(
          (element) => element.dataset.nodeId === focusId,
        );
        target?.focus({ preventScroll: true });
      }
    });
  };

  const hideSuggestions = () => {
    suggestions.hidden = true;
    suggestions.replaceChildren();
    search.setAttribute("aria-expanded", "false");
  };

  const searchScore = (node, query) => {
    const label = node.label.toLowerCase();
    const subtitle = node.subtitle.toLowerCase();
    if (label === query || subtitle === query) return 0;
    if (label.startsWith(query) || subtitle.startsWith(query)) return 1;
    if (label.includes(query) || subtitle.includes(query)) return 2;
    if (node.search.includes(query)) return 3;
    return 99;
  };

  const updateSuggestions = () => {
    const query = search.value.trim().toLowerCase();
    if (query.length < 2) {
      hideSuggestions();
      return;
    }
    const matches = [...nodes.values()]
      .map((node) => ({ node, score: searchScore(node, query) }))
      .filter((item) => item.score < 99)
      .sort((left, right) => left.score - right.score || sortNodes(left.node.id, right.node.id))
      .slice(0, 10);
    suggestions.replaceChildren();
    matches.forEach(({ node }) => {
      const item = create("li");
      item.setAttribute("role", "option");
      const button = create("button");
      button.type = "button";
      button.dataset.graphSuggestion = node.id;
      button.append(
        create("strong", "", node.label),
        create("span", "", `${node.kind} · ${statusLabels[node.status] || node.status}`),
        create("small", "", node.subtitle),
      );
      item.append(button);
      suggestions.append(item);
    });
    if (!matches.length) {
      const item = create("li", "lean-graph-no-result", "No matching graph node.");
      item.setAttribute("role", "option");
      suggestions.append(item);
    }
    suggestions.hidden = false;
    search.setAttribute("aria-expanded", "true");
  };

  const initialize = (payload) => {
    data = payload;
    nodes = new Map(data.nodes.map((node) => [node.id, node]));
    children = new Map();
    incoming = new Map();
    outgoing = new Map();
    data.nodes.forEach((node) => {
      children.set(node.id, []);
      incoming.set(node.id, []);
      outgoing.set(node.id, []);
    });
    data.nodes.forEach((node) => {
      if (node.parent && children.has(node.parent)) children.get(node.parent).push(node.id);
    });
    children.forEach((ids) => ids.sort(sortNodes));
    data.edges.forEach((edge) => {
      if (incoming.has(edge.target)) incoming.get(edge.target).push(edge);
      if (outgoing.has(edge.source)) outgoing.get(edge.source).push(edge);
    });
    setView("overview");
  };

  viewButtons.forEach((button) => {
    button.addEventListener("click", () => setView(button.dataset.graphView));
  });
  branchSizeSelect?.addEventListener("change", () => {
    branchSize = Number(branchSizeSelect.value || 12);
  });
  fitButton?.addEventListener("click", fitGraph);
  resetButton?.addEventListener("click", () => setView(currentView === "search" ? "overview" : currentView));
  search?.addEventListener("input", updateSuggestions);
  search?.addEventListener("keydown", (event) => {
    if (event.key === "Escape") hideSuggestions();
    if (event.key === "Enter") {
      const first = suggestions.querySelector("[data-graph-suggestion]");
      if (first) {
        event.preventDefault();
        revealSearchResult(first.dataset.graphSuggestion);
      }
    }
  });
  suggestions?.addEventListener("click", (event) => {
    const button = event.target.closest("[data-graph-suggestion]");
    if (button) revealSearchResult(button.dataset.graphSuggestion);
  });
  detail?.addEventListener("click", (event) => {
    const neighbor = event.target.closest("[data-graph-neighbor]");
    if (neighbor) selectNode(neighbor.dataset.graphNeighbor, false);
    const more = event.target.closest("[data-graph-more]");
    if (more) {
      addChildren(more.dataset.graphMore, true);
      render({ fit: true, focusId: more.dataset.graphMore });
    }
    const collapse = event.target.closest("[data-graph-collapse]");
    if (collapse) {
      collapseBranch(collapse.dataset.graphCollapse);
      render({ fit: true, focusId: collapse.dataset.graphCollapse });
    }
  });

  svg?.addEventListener("pointerdown", (event) => {
    if (event.target.closest?.(".lean-graph-node")) return;
    dragging = { pointerId: event.pointerId, x: event.clientX, y: event.clientY, startX: transform.x, startY: transform.y };
    svg.setPointerCapture?.(event.pointerId);
    canvas.classList.add("is-panning");
  });
  svg?.addEventListener("pointermove", (event) => {
    if (!dragging || dragging.pointerId !== event.pointerId) return;
    transform.x = dragging.startX + event.clientX - dragging.x;
    transform.y = dragging.startY + event.clientY - dragging.y;
    updateTransform();
  });
  const endDrag = (event) => {
    if (!dragging || dragging.pointerId !== event.pointerId) return;
    dragging = null;
    canvas.classList.remove("is-panning");
  };
  svg?.addEventListener("pointerup", endDrag);
  svg?.addEventListener("pointercancel", endDrag);
  canvas?.addEventListener(
    "wheel",
    (event) => {
      event.preventDefault();
      const bounds = canvas.getBoundingClientRect();
      const mouseX = event.clientX - bounds.left;
      const mouseY = event.clientY - bounds.top;
      const oldScale = transform.scale;
      const newScale = Math.min(2.2, Math.max(0.16, oldScale * Math.exp(-event.deltaY * 0.0012)));
      const graphX = (mouseX - transform.x) / oldScale;
      const graphY = (mouseY - transform.y) / oldScale;
      transform.scale = newScale;
      transform.x = mouseX - graphX * newScale;
      transform.y = mouseY - graphY * newScale;
      updateTransform();
    },
    { passive: false },
  );
  window.addEventListener("resize", () => {
    if (!data) return;
    svg.setAttribute("viewBox", `0 0 ${Math.max(320, canvas.clientWidth)} ${Math.max(420, canvas.clientHeight - 26)}`);
    fitGraph();
  });
  document.addEventListener("click", (event) => {
    if (!app.contains(event.target)) hideSuggestions();
  });

  fetch(app.dataset.graphSource)
    .then((response) => {
      if (!response.ok) throw new Error(`Graph data returned ${response.status}`);
      return response.json();
    })
    .then(initialize)
    .catch((error) => {
      count.textContent = "Graph data unavailable";
      empty.hidden = false;
      empty.textContent = "The generated Lean Graph could not be loaded. Use the declaration catalog while the static artifact is rebuilt.";
      console.error(error);
    });
})();
