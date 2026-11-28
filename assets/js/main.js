/* ------------------------------------------------------------------ routing */

/* The pages, by the first part of the address: `#development/Name` is the card of `Name`. */
const RENDER = { "": pageOverview, foundations: pageFoundations, development: pageDevelopment,
  comparator: pageComparator };
const PAGE_TITLE = { foundations: "Foundations", development: "Development", comparator: "Comparator" };
/* The addresses of former versions of the page. */
const ALIASES = { intro: ["", ""], overview: ["", ""], results: ["development", ""],
  libraries: ["foundations", "libraries"], axioms: ["foundations", "axioms"],
  definitions: ["foundations", "definitions"] };

function parseHash() {
  let h = location.hash.slice(1);
  try { h = decodeURIComponent(h); } catch (e) { /* keep it as it is */ }
  const k = h.indexOf("/");
  let page = k < 0 ? h : h.slice(0, k);
  let target = k < 0 ? "" : h.slice(k + 1);
  const alias = own(ALIASES, page);
  if (alias) [page, target] = [alias[0], target || alias[1]];
  if (!own(RENDER, page)) [page, target] = ["", ""];
  return { page, target };
}

/* The element of a target: a declaration, or an element of the page with this id. */
function elementFor(page, target) {
  if (!target) return null;
  const id = page === "development" && CARD[target] ? "d:" + target
    : page === "foundations" && TRUSTED[target] ? "t:" + target
      : page === "" && MAIN_SET.has(target) ? "o:" + target : target;
  return document.getElementById(id);
}

let current = null;
/* The target that the page scrolled to: once the formulas are set, it scrolls there again, since
   they change the heights. */
let anchor = null;

function show() {
  const { page, target } = parseHash();
  if (page !== current) {
    if (window.MathJax && MathJax.typesetClear) MathJax.typesetClear([app]);
    FIGURE = 0;
    app.innerHTML = masthead(page) + RENDER[page]();
    current = page;
    document.title = (META.title || "") + (own(PAGE_TITLE, page) ? " · " + PAGE_TITLE[page] : "");
    layoutMaps(app);
    typeset(app);
  }
  const el = elementFor(page, target);
  if (el) {
    el.scrollIntoView({ block: "start" });
    el.classList.remove("flash");
    void el.offsetWidth;
    el.classList.add("flash");
    anchor = { el, y: window.scrollY };
  } else {
    window.scrollTo(0, 0);
    anchor = null;
  }
  spy();
}

/* ------------------------------------------------------------------ mathematics */

let queue = Promise.resolve();
/* Sets the formulas of `el` with MathJax, once it is loaded, then lays out the proof maps again. */
function typeset(el) {
  const mj = window.MathJax;
  if (!mj || typeof mj.typesetPromise !== "function") return;
  queue = queue.then(() => mj.typesetPromise([el])).then(() => {
    layoutMaps(el);
    if (anchor && document.contains(anchor.el) && Math.abs(window.scrollY - anchor.y) < 4) {
      anchor.el.scrollIntoView({ block: "start" });
      anchor.y = window.scrollY;
    }
    spy();
  }).catch((e) => console.warn("showcase: MathJax", e));
}
window.showcaseTypeset = () => typeset(app);

/* ------------------------------------------------------------------ table of contents */

/* Marks the entry of the table of contents being read, and shows the results of its section. */
function spy() {
  const nav = app.querySelector(".toc");
  if (!nav) return;
  const items = [...nav.querySelectorAll("li")];
  const line = (parseFloat(getComputedStyle(document.documentElement).fontSize) || 16) * 6;
  let here = -1;
  items.forEach((li, k) => {
    const el = document.getElementById(li.firstElementChild.dataset.target);
    if (el && el.getBoundingClientRect().top <= line) here = k;
  });
  let section = -1;
  for (let k = Math.max(here, 0); k >= 0; k--) if (items[k] && items[k].classList.contains("l2")) { section = k; break; }
  // the results before the first section, or of a text without sections, are always shown
  let inSection = section === -1;
  items.forEach((li, k) => {
    if (li.classList.contains("l2")) inSection = k === section;
    li.classList.toggle("on", inSection);
    const a = li.firstElementChild;
    if (k === here) a.setAttribute("aria-current", "location");
    else a.removeAttribute("aria-current");
  });
  const a = items[here] && items[here].firstElementChild;
  if (a && nav.scrollHeight > nav.clientHeight && getComputedStyle(nav).position === "sticky") {
    const n = nav.getBoundingClientRect(), r = a.getBoundingClientRect();
    if (r.top < n.top) nav.scrollTop -= n.top - r.top + 8;
    else if (r.bottom > n.bottom) nav.scrollTop += r.bottom - n.bottom + 8;
  }
}
let spying = false;
window.addEventListener("scroll", () => {
  if (spying) return;
  spying = true;
  requestAnimationFrame(() => { spying = false; spy(); });
}, { passive: true });
let resizing = false;
window.addEventListener("resize", () => {
  if (resizing) return;
  resizing = true;
  requestAnimationFrame(() => { resizing = false; layoutMaps(app); spy(); });
});

/* ------------------------------------------------------------------ interactions */

/* An image enlarged over the page. A click or the Escape key closes it. */
function openLightbox(img) {
  const box = document.createElement("div");
  box.className = "lightbox";
  box.setAttribute("role", "dialog");
  box.setAttribute("aria-modal", "true");
  box.setAttribute("aria-label", img.alt);
  box.tabIndex = -1;
  box.innerHTML = `<img src="${esc(img.getAttribute("src"))}" alt="${esc(img.alt)}"><button class="lightbox-close" type="button" aria-label="Close">×</button>`;
  const back = document.activeElement;
  const close = () => {
    box.remove();
    document.removeEventListener("keydown", onKey);
    if (back && back.focus) back.focus();
  };
  const onKey = (e) => { if (e.key === "Escape") close(); };
  box.addEventListener("click", close);
  document.addEventListener("keydown", onKey);
  document.body.appendChild(box);
  box.focus();
}

/* Opens or closes a panel of a theorem: its Lean statement, its source, the comments of its
   proof. */
function togglePanel(btn) {
  const env = btn.closest(".env");
  const kind = btn.dataset.panel;
  const panels = env.querySelector(".panels");
  if (btn.getAttribute("aria-expanded") === "true") {
    const p = panels.querySelector(`[data-kind="${kind}"]`);
    if (p) p.remove();
    btn.setAttribute("aria-expanded", "false");
    return;
  }
  const tmp = document.createElement("div");
  tmp.innerHTML = panelHtml(env.dataset.name, kind);
  const node = tmp.firstElementChild;
  const order = ["sig", "src", "comments"];
  const next = [...panels.children].find((c) => order.indexOf(c.dataset.kind) > order.indexOf(kind));
  panels.insertBefore(node, next || null);
  btn.setAttribute("aria-expanded", "true");
  typeset(node);
}

app.addEventListener("click", (e) => {
  const t = e.target;
  const panel = t.closest(".lean-bar button[data-panel]");
  if (panel) return togglePanel(panel);
  const zoom = t.closest(".fig-zoom");
  if (zoom) return openLightbox(zoom.querySelector("img"));
  const close = t.closest(".pmap-close");
  if (close) return selectNode(null, close.closest(".pmap"));
  const pn = t.closest(".pn");
  if (pn && !t.closest("a")) return selectNode(pn);
  const toggle = t.closest(".toc-toggle");
  if (toggle) {
    const nav = toggle.closest(".toc");
    toggle.setAttribute("aria-expanded", String(nav.classList.toggle("open")));
    return;
  }
  // a link to the address already shown scrolls to its target again
  const a = t.closest("a[href^='#']");
  if (a) {
    const nav = a.closest(".toc.open");
    if (nav) nav.classList.remove("open");
    if (a.getAttribute("href") === location.hash || (a.getAttribute("href") === "#" && !location.hash)) {
      e.preventDefault();
      show();
    }
  }
});
app.addEventListener("keydown", (e) => {
  const pn = e.target.closest && e.target.closest(".pn");
  if (pn && (e.key === "Enter" || e.key === " ")) { e.preventDefault(); selectNode(pn); }
});
["mouseover", "focusin"].forEach((type) => app.addEventListener(type, (e) => {
  const pn = e.target.closest && e.target.closest(".pn");
  if (pn) highlightNode(pn);
}));
["mouseout", "focusout"].forEach((type) => app.addEventListener(type, (e) => {
  const pn = e.target.closest && e.target.closest(".pn");
  if (pn && !pn.contains(e.relatedTarget)) highlightNode(null, pn.closest(".pmap"));
}));

window.addEventListener("hashchange", show);
// the fonts and dagre change the layout of the maps once they are loaded
window.addEventListener("DOMContentLoaded", () => layoutMaps(app));
if (document.fonts && document.fonts.ready) document.fonts.ready.then(() => layoutMaps(app));
show();
