/* Preserve direct question links while keeping the question list compact. */
(() => {
  const reveal = () => {
    let id;
    try { id = decodeURIComponent(location.hash.slice(1)); } catch { return; }
    const target = document.getElementById(id);
    if (!target?.closest('.bench-reader')) return;
    for (let node = target.parentElement; node; node = node.parentElement) {
      if (node.matches('details')) node.open = true;
    }
    requestAnimationFrame(() => target.scrollIntoView({block: 'start'}));
  };
  window.addEventListener('hashchange', reveal);
  reveal();
})();
