(() => {
  const section = document.querySelector("[data-community-registry]");
  if (!section) return;

  const summary = section.querySelector("[data-community-summary]");
  const container = section.querySelector("[data-community-entries]");
  const statusLabel = {
    proposed: "Proposed",
    "in-review": "In review",
    "lean-checked": "Lean checked",
    integrated: "Integrated",
  };

  const card = (entry) => {
    const article = document.createElement("article");
    article.className = "community-entry info-card";

    const top = document.createElement("div");
    top.className = "community-entry-top";
    const status = document.createElement("span");
    status.className = `status ${entry.status === "lean-checked" ? "compiled" : entry.status === "in-review" ? "partial" : entry.status}`;
    status.textContent = statusLabel[entry.status] || entry.status;
    const domain = document.createElement("span");
    domain.className = "community-domain";
    domain.textContent = entry.domain || "Unclassified";
    top.append(status, domain);

    const title = document.createElement("h3");
    title.textContent = entry.title || entry.id;
    const statement = document.createElement("p");
    statement.textContent = entry.mathematics?.plain || "No plain-language statement supplied.";
    const credit = document.createElement("p");
    credit.className = "community-credit";
    credit.textContent = entry.contributor?.credit || entry.contributor?.name || "Contributor credit pending";
    article.append(top, title, statement, credit);
    return article;
  };

  fetch(section.dataset.registryUrl, { headers: { Accept: "application/json" } })
    .then((response) => {
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      return response.json();
    })
    .then((registry) => {
      const entries = registry.entries || [];
      container.replaceChildren(...entries.map(card));
      if (!entries.length) {
        const empty = document.createElement("div");
        empty.className = "callout";
        empty.innerHTML = "<strong>The registry is open.</strong> No external lemma packet has been accepted yet, so the site does not invent contributor names or results. The first reviewed proposal will appear here with its real status and credit.";
        container.append(empty);
      }
      summary.textContent = `${entries.length} public contribution packet${entries.length === 1 ? "" : "s"} in this snapshot.`;
    })
    .catch((error) => {
      summary.textContent = `The registry could not be loaded: ${error.message}`;
      container.replaceChildren();
    });
})();
