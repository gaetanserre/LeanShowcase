/* Showcase: the website of a Lean formalization, from the data that `lake exe showcase` embeds in
   the page. The scripts share one scope, in the order of `Showcase.scripts`. */

const D = JSON.parse(document.getElementById("showcase-data").textContent);
/* A map without prototype: a key such as `constructor` or `toString` finds nothing in it. */
const dict = (o) => Object.assign(Object.create(null), o || {});
/* The value of a key of an object, without its inherited properties. */
const own = (o, k) => (o && Object.prototype.hasOwnProperty.call(o, k) ? o[k] : undefined);
const META = D.meta || {};
const PACKAGES = D.packages || [];
const MODULES = D.modules || [];   // [name, package, URL of the source]
const CONSTS = D.consts || [];     // [name, module]
const DECLS = dict(D.decls);
const NOTES = D.notes || {};       // kind -> declaration -> text
const TITLES = dict(D.titles);
const REFS = dict(D.refs);         // identifier of the text -> constant
const KEYWORDS = new Set(D.keywords || []);
const TRUST = Object.assign({ groups: [], notations: [], axioms: [] }, D.trust || {});
const MEDIA = dict(D.media);
const LINKS = dict(META.links);
const app = document.getElementById("app");

const note = (kind, name) => own(own(NOTES, kind), name);

/* ------------------------------------------------------------------ strings */

const ESC = { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" };
const esc = (s) => String(s == null ? "" : s).replace(/[&<>"']/g, (c) => ESC[c]);
const words = (s) => s.split(/\s+/).filter(Boolean);
const lastPart = (n) => n.split(".").pop();
const plural = (n, one, many) => `${n} ${n === 1 ? one : many || one + "s"}`;
/* "a", "a and b", "a, b and c". */
const listOf = (xs) =>
  xs.length <= 2 ? xs.join(" and ") : xs.slice(0, -1).join(", ") + " and " + xs[xs.length - 1];
const NUMBERS = ["no", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten"];
const count = (n) => NUMBERS[n] || String(n);
/* An URL that can go in an `href`: no `javascript:` or `data:`. */
const safeUrl = (u) => (/^\s*(javascript|data|vbscript):/i.test(u) ? "#" : u);
const extLink = (url, text, cls) =>
  `<a${cls ? ` class="${cls}"` : ""} href="${esc(safeUrl(url))}" target="_blank" rel="noopener">${text}</a>`;
/* A slug for an anchor: lowercase letters, digits and dashes. */
const slug = (s) => s.toLowerCase().replace(/<[^>]*>/g, "").replace(/\$[^$]*\$/g, "")
  .normalize("NFKD").replace(/[^\w\s-]/g, "").trim().replace(/[\s_]+/g, "-") || "section";

/* ------------------------------------------------------------------ constants */

const constIndex = new Map(CONSTS.map((c, i) => [c[0], i]));
const constName = (i) => (CONSTS[i] || [])[0];

/* The module of a declaration or of a linked constant, as an index of `MODULES`. */
function moduleOf(name) {
  if (DECLS[name]) return DECLS[name].mod;
  const i = constIndex.get(name);
  return i === undefined ? undefined : CONSTS[i][1];
}
const moduleName = (m) => (MODULES[m] || [])[0] || "";
const packageOfModule = (m) => PACKAGES[(MODULES[m] || [])[1]];
const packageOf = (name) => packageOfModule(moduleOf(name));
const isProject = (name) => { const p = packageOf(name); return !!p && p.kind === "project"; };

/* The name of a declaration as its author wrote it. */
const display = (name) => (DECLS[name] && DECLS[name].display) || name;

/* The page of a constant in the documentation of its package. */
function docsUrl(name) {
  if (name.startsWith("_private.")) return null;
  const m = moduleOf(name);
  const pkg = packageOfModule(m);
  if (!pkg || !pkg.docs) return null;
  return pkg.docs + moduleName(m).split(".").join("/") + ".html#" + name;
}

/* The lines of a declaration in its source. */
function sourceUrl(d) {
  const mod = MODULES[d.mod];
  return mod && mod[2] && d.line ? `${mod[2]}#L${d.line}-L${d.end}` : null;
}

/* The file of a module, as a reader finds it in the source. */
function modulePath(m) {
  const mod = MODULES[m];
  if (!mod) return "";
  const url = mod[2];
  if (url && META.repository && META.rev && url.startsWith(META.repository)) {
    return url.slice(`${META.repository}/blob/${META.rev}/`.length);
  }
  return mod[0];
}

/* ------------------------------------------------------------------ places on the page */

/* Where each declaration is shown: its card in the development, its entry in the foundations. */
const CARD = Object.create(null);
const TRUSTED = Object.create(null);
const LABEL = Object.create(null);

const routeHref = (page, target) => "#" + page + (target ? "/" + encodeURIComponent(target) : "");

/* A link to a constant: to its place on the page, otherwise to its documentation. */
function constHref(name) {
  if (CARD[name]) return routeHref("development", name);
  if (TRUSTED[name]) return routeHref("foundations", name);
  return docsUrl(name);
}
function constLink(name, text, cls) {
  const href = constHref(name);
  const t = esc(text);
  if (!href) return t;
  const ext = !href.startsWith("#");
  return `<a${cls ? ` class="${cls}"` : ""} href="${esc(href)}"${ext ? ' target="_blank" rel="noopener"' : ""} title="${esc(display(name))}">${t}</a>`;
}
