(() => {
  const search = document.getElementById("theorem-search-controls");
  if (!search) return;

  const query = document.getElementById("theorem-query");
  const count = document.getElementById("theorem-count");
  const results = document.querySelector(".theorem-results tbody");
  const entries = Array.from(results.querySelectorAll("[data-theorem]"), (node) => {
    const [name, symbols] = JSON.parse(node.dataset.theorem);
    const fullName = name.toLowerCase();
    const shortName = fullName.split(".").at(-1);
    return {
      name,
      element: node.closest(".theorem-entry"),
      names: [fullName, shortName],
      symbols: symbols.map((symbol) => symbol.toLowerCase()),
    };
  });

  function rank(entry, term) {
    if (entry.names.includes(term)) return 4;
    if (entry.symbols.includes(term)) return 3;
    if (entry.names.some((name) => name.startsWith(term))) return 2;
    if ([...entry.names, ...entry.symbols].some((name) => name.includes(term))) return 1;
    return 0;
  }

  function update() {
    const terms = query.value.toLowerCase().trim().split(/\s+/).filter(Boolean);
    const matches = [];
    for (const entry of entries) {
      const scores = terms.map((term) => rank(entry, term));
      if (scores.every(Boolean)) {
        matches.push({ entry, score: scores.reduce((sum, score) => sum + score, 0) });
      }
    }
    matches.sort((a, b) => b.score - a.score || a.entry.name.localeCompare(b.entry.name));
    count.textContent = terms.length ? `${matches.length} matches` : "";
    for (const entry of entries) entry.element.hidden = true;
    for (const { entry } of matches) {
      entry.element.hidden = false;
      results.append(entry.element);
    }
  }

  query.value = new URLSearchParams(window.location.search).get("theorem") || "";
  search.hidden = false;
  query.addEventListener("input", update);
  update();
})();
