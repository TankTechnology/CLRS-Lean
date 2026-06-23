const search = document.querySelector("#search");
const filters = document.querySelectorAll(".filter");
const cards = document.querySelectorAll(".section-card");

let currentFilter = "all";

function normalize(value) {
  return value.trim().toLowerCase();
}

function updateCards() {
  const query = normalize(search.value);

  cards.forEach((card) => {
    const status = card.dataset.status;
    const text = normalize(`${card.textContent} ${card.dataset.keywords}`);
    const matchesStatus = currentFilter === "all" || currentFilter === status;
    const matchesQuery = query.length === 0 || text.includes(query);

    card.classList.toggle("is-hidden", !(matchesStatus && matchesQuery));
  });
}

filters.forEach((button) => {
  button.addEventListener("click", () => {
    filters.forEach((item) => item.classList.remove("is-selected"));
    button.classList.add("is-selected");
    currentFilter = button.dataset.filter;
    updateCards();
  });
});

search.addEventListener("input", updateCards);
