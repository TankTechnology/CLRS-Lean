/* Load the full-text index only when a reader uses the header search. */
(() => {
  let loading = false;
  document.addEventListener('focusin', event => {
    const box = event.target.closest('[role="searchbox"]');
    if (!box || window.searchIndex || loading) return;
    loading = true;
    const status = document.createElement('span');
    status.className = 'clrs-search-status';
    status.setAttribute('role', 'status');
    status.textContent = 'Loading full-text search…';
    box.parentElement.append(status);
    const script = document.createElement('script');
    script.src = new URL('-verso-search/searchIndex.js', document.baseURI).href;
    script.onload = () => {
      loading = false;
      status.remove();
      box.dispatchEvent(new Event('clrs-search-ready'));
    };
    script.onerror = () => {
      loading = false;
      status.textContent = 'Full-text search unavailable. Refocus search to retry.';
      box.addEventListener('focus', () => status.remove(), { once: true });
      script.remove();
    };
    document.head.append(script);
  });
})();
