/* Progressive enhancements only. Reading and navigation work without JavaScript. */
(() => {
  const menu = document.querySelector('.menu-toggle');
  const button = document.querySelector('.hamburger');
  const sidebar = document.querySelector('.sidebar');
  if (menu && button) {
    button.setAttribute('role', 'button');
    button.setAttribute('tabindex', '0');
    button.setAttribute('aria-label', 'Toggle chapter navigation');
    const syncMenu = () => button.setAttribute('aria-expanded', String(menu.checked));
    menu.addEventListener('change', syncMenu);
    button.addEventListener('keydown', event => {
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        menu.checked = !menu.checked;
        syncMenu();
      }
    });
    document.addEventListener('keydown', event => {
      if (event.key === 'Escape' && menu.checked) {
        menu.checked = false;
        syncMenu();
        button.focus();
      }
    });
    sidebar?.addEventListener('click', event => {
      if (event.target.closest('a')) {
        menu.checked = false;
        syncMenu();
      }
    });
    syncMenu();
  }
  document.querySelectorAll('.module-tree summary a').forEach(link => {
    link.addEventListener('click', event => event.stopPropagation());
  });
})();
