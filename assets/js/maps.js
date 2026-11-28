/* ------------------------------------------------------------------ proof maps */

/* A block ```diagram Name: one box per line `id: head <- dep, dep`, followed by its text on
   indented lines, and by its explanation on indented lines that start with `>`. The head is
   `step`, `goal`, a result of the page written as a code span, or a classical theorem: its name,
   the Lean name of its statement as a code span, and a citation `[Key]`. */
const MAPS = Object.create(null);
function parseMap(name) {
  if (MAPS[name]) return MAPS[name];
  const nodes = [];
  const byId = {};
  const errors = [];
  let cur = null;
  (note("diagram", name) || "").replace(/\r/g, "").split("\n").forEach((line) => {
    if (!line.trim()) return;
    if (/^\s/.test(line)) {
      if (!cur) return;
      const t = line.trim();
      if (t.startsWith(">")) cur.detail.push(t.replace(/^>\s?/, ""));
      else cur.text.push(t);
      return;
    }
    let left = line.trim();
    let deps = [];
    const arrow = left.lastIndexOf("<-");
    if (arrow >= 0) {
      deps = left.slice(arrow + 2).split(",").map((x) => x.trim()).filter(Boolean);
      left = left.slice(0, arrow).trim();
    }
    const colon = left.indexOf(":");
    const id = (colon >= 0 ? left.slice(0, colon) : left).trim();
    const head = (colon >= 0 ? left.slice(colon + 1) : left).trim();
    const n = { id, deps, text: [], detail: [] };
    let m;
    if (head === "goal" || (colon < 0 && id === "goal")) n.kind = "goal";
    else if (head === "step" || head === "") n.kind = "step";
    else if ((m = /^`([^`]+)`$/.exec(head))) {
      n.kind = "result";
      n.name = REFS[m[1]] !== undefined ? constName(REFS[m[1]]) : m[1];
    } else {
      n.kind = "classical";
      const c = /`([^`]+)`/.exec(head);
      if (c) n.name = REFS[c[1]] !== undefined ? constName(REFS[c[1]]) : c[1];
      const k = /\[([^\]]+)\]/.exec(head);
      if (k) n.cite = k[1];
      n.title = head.replace(/`[^`]*`/g, "").replace(/\[[^\]]*\]/g, "").trim();
    }
    if (byId[id]) errors.push(`duplicate box ${id}`);
    byId[id] = n;
    nodes.push(n);
    cur = n;
  });
  const edges = [];
  nodes.forEach((n) => n.deps.forEach((d) => {
    if (byId[d]) edges.push([d, n.id]);
    else errors.push(`unknown box ${d} in ${n.id}`);
  }));
  return (MAPS[name] = { nodes, byId, edges, errors });
}

/* The library of a constant, as a reader names it: Mathlib, the project, ... */
function libraryOf(name) {
  const p = packageOf(name);
  return p ? (p.kind === "project" ? null : p.label) : null;
}

function nodeLabel(n, goalLabel) {
  if (n.kind === "goal") return goalLabel;
  if (n.kind === "result") return LABEL[n.name] || lastPart(display(n.name));
  if (n.kind === "classical") return n.title;
  return "";
}

function mapHtml(name, goalLabel) {
  const g = parseMap(name);
  const boxes = g.nodes.map((n) => {
    const label = nodeLabel(n, goalLabel);
    const lib = n.kind === "classical" && n.name ? libraryOf(n.name) : null;
    const text = n.text.length ? n.text.join(" ")
      : n.kind === "result" && DECLS[n.name] ? titleOf(n.name) || "" : "";
    const more = n.detail.length || n.kind === "result" || (n.kind === "classical" && (n.name || n.cite));
    return `<div class="pn ${n.kind}${more ? " more" : ""}" data-id="${esc(n.id)}" tabindex="0" role="button" aria-label="${esc(label || "Step")}">
      ${label ? `<div class="pn-label">${inline(label)}${lib ? ` <span class="pn-lib">· ${esc(lib)}</span>` : ""}</div>` : ""}
      ${text ? `<div class="pn-text">${inline(text)}</div>` : ""}</div>`;
  }).join("");
  return `<figure class="pmap" data-name="${esc(name)}">
    <figcaption><span class="inline-label">Proof map</span><span class="hint">An arrow goes from a fact to the step that uses it. Select a box for details.</span></figcaption>
    ${g.errors.length ? `<p class="pmap-error">${esc(g.errors.join("; "))}</p>` : ""}
    <div class="pmap-scroll"><div class="pmap-sizer"><div class="pmap-canvas"><svg class="pmap-edges" aria-hidden="true"></svg>${boxes}</div></div></div>
    <div class="pmap-detail" hidden></div>
  </figure>`;
}

/* A smooth path through the points of an edge (the B-spline of d3's curveBasis). */
function basisPath(pts) {
  if (pts.length < 3) return "M" + pts.map((p) => `${p.x},${p.y}`).join("L");
  let d = `M${pts[0].x},${pts[0].y}`;
  let [x0, y0, x1, y1] = [pts[0].x, pts[0].y, pts[0].x, pts[0].y];
  const bez = (x, y) => {
    d += `C${(2 * x0 + x1) / 3},${(2 * y0 + y1) / 3},${(x0 + 2 * x1) / 3},${(y0 + 2 * y1) / 3},${(x0 + 4 * x1 + x) / 6},${(y0 + 4 * y1 + y) / 6}`;
  };
  pts.forEach((p, i) => {
    if (i === 0) return;
    if (i === 1) { x0 = x1; y0 = y1; x1 = p.x; y1 = p.y; return; }
    if (i === 2) d += `L${(5 * x0 + x1) / 6},${(5 * y0 + y1) / 6}`;
    bez(p.x, p.y);
    x0 = x1; y0 = y1; x1 = p.x; y1 = p.y;
  });
  bez(x1, y1);
  return d + `L${x1},${y1}`;
}

/* The margin of a map around its boxes, in pixels. */
const MAP_MARGIN = 8;

/* Layers by the longest path from the sources, when dagre is not available. */
function fallbackLayout(g, size) {
  const rank = {};
  const visit = (id, seen) => {
    if (id in rank) return rank[id];
    if (seen.has(id)) return 0;
    seen.add(id);
    rank[id] = g.byId[id].deps.filter((x) => g.byId[x]).reduce((r, x) => Math.max(r, visit(x, seen) + 1), 0);
    return rank[id];
  };
  g.nodes.forEach((n) => visit(n.id, new Set()));
  const rows = [];
  g.nodes.forEach((n) => (rows[rank[n.id]] = rows[rank[n.id]] || []).push(n.id));
  const gap = 24, rowGap = 40, m = MAP_MARGIN;
  const widths = rows.map((r) => r.reduce((w, id) => w + size[id].w, 0) + gap * (r.length - 1));
  const W = Math.max(...widths) + 2 * m;
  const pos = {};
  let y = m;
  rows.forEach((r, i) => {
    const h = Math.max(...r.map((id) => size[id].h));
    let x = (W - widths[i]) / 2;
    r.forEach((id) => { pos[id] = { x: x + size[id].w / 2, y: y + h / 2 }; x += size[id].w + gap; });
    y += h + rowGap;
  });
  const edges = g.edges.map(([a, b]) => [a, b, [
    { x: pos[a].x, y: pos[a].y + size[a].h / 2 }, { x: pos[b].x, y: pos[b].y - size[b].h / 2 }]]);
  return { pos, edges, W, H: y - rowGap + m };
}

/* Places the boxes of the maps in `root` and draws their arrows. The boxes are measured first, so
   that the layout follows the size of their formulas. */
function layoutMaps(root) {
  root.querySelectorAll(".pmap").forEach((fig) => {
    const g = parseMap(fig.getAttribute("data-name"));
    if (!g.nodes.length) return;
    const canvas = fig.querySelector(".pmap-canvas");
    const els = {};
    canvas.querySelectorAll(".pn").forEach((el) => { els[el.getAttribute("data-id")] = el; });
    // the boxes are measured at their own size: without the scale of a former layout
    canvas.style.transform = "";
    // a box is as wide as its text, up to the width of the style, unless a formula is wider
    g.nodes.forEach((n) => { els[n.id].style.width = ""; els[n.id].style.maxWidth = ""; });
    g.nodes.forEach((n) => {
      const el = els[n.id];
      if (el.scrollWidth > el.clientWidth + 1) {
        el.style.maxWidth = "none";
        el.style.width = `${Math.ceil(el.scrollWidth + parseFloat(getComputedStyle(el).paddingRight) + 2)}px`;
      }
    });
    // the sizes are rounded up, and each box is given its size, so that the layout holds it whole
    const size = {};
    g.nodes.forEach((n) => {
      const r = els[n.id].getBoundingClientRect();
      size[n.id] = { w: Math.ceil(r.width), h: Math.ceil(r.height) };
    });
    if (g.nodes.some((n) => !size[n.id].w)) return;   // not displayed yet
    g.nodes.forEach((n) => {
      els[n.id].style.width = `${size[n.id].w}px`;
      els[n.id].style.maxWidth = "none";
    });
    let L;
    if (window.dagre) {
      const G = new dagre.graphlib.Graph();
      // a margin around the boxes keeps their borders and the outline of a selected box inside
      G.setGraph({ rankdir: "TB", nodesep: 22, ranksep: 34, edgesep: 12, marginx: MAP_MARGIN, marginy: MAP_MARGIN });
      G.setDefaultEdgeLabel(() => ({}));
      g.nodes.forEach((n) => G.setNode(n.id, { width: size[n.id].w, height: size[n.id].h }));
      g.edges.forEach(([a, b]) => G.setEdge(a, b));
      dagre.layout(G);
      const pos = {};
      g.nodes.forEach((n) => { const v = G.node(n.id); pos[n.id] = { x: v.x, y: v.y }; });
      L = { pos, edges: g.edges.map(([a, b]) => [a, b, G.edge(a, b).points]), W: G.graph().width, H: G.graph().height };
    } else L = fallbackLayout(g, size);
    g.nodes.forEach((n) => {
      els[n.id].style.left = `${L.pos[n.id].x - size[n.id].w / 2}px`;
      els[n.id].style.top = `${L.pos[n.id].y - size[n.id].h / 2}px`;
    });
    canvas.style.width = `${Math.ceil(L.W)}px`;
    canvas.style.height = `${Math.ceil(L.H)}px`;
    // a map wider than the column is scaled down to its width, so that it is always seen whole
    const avail = fig.querySelector(".pmap-scroll").clientWidth;
    const f = L.W > avail ? avail / L.W : 1;
    canvas.style.transform = f < 1 ? `scale(${f})` : "";
    const sizer = fig.querySelector(".pmap-sizer");
    sizer.style.width = `${Math.ceil(L.W * f)}px`;
    sizer.style.height = `${Math.ceil(L.H * f)}px`;
    const svg = canvas.querySelector(".pmap-edges");
    svg.setAttribute("viewBox", `0 0 ${Math.ceil(L.W)} ${Math.ceil(L.H)}`);
    svg.setAttribute("width", Math.ceil(L.W));
    svg.setAttribute("height", Math.ceil(L.H));
    svg.innerHTML = `<defs><marker id="pm-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M1 1L9 5L1 9" fill="none" stroke="context-stroke" stroke-width="1.4" stroke-linecap="round" stroke-linejoin="round"/></marker></defs>` +
      L.edges.map(([a, b, pts]) => `<path class="pe" data-from="${esc(a)}" data-to="${esc(b)}" d="${basisPath(pts)}" marker-end="url(#pm-arrow)"/>`).join("");
    fig.classList.add("laid");
  });
}

/* Hovering a box shows what it rests on: its incoming arrows and their sources. */
function highlightNode(pn, fig) {
  fig = fig || pn.closest(".pmap");
  fig.querySelectorAll(".hl, .src").forEach((el) => el.classList.remove("hl", "src"));
  fig.classList.toggle("focus", !!pn);
  if (!pn) return;
  const id = pn.getAttribute("data-id");
  pn.classList.add("hl");
  fig.querySelectorAll(".pe").forEach((e) => {
    if (e.getAttribute("data-to") !== id) return;
    e.classList.add("hl");
    const s = fig.querySelector(`.pn[data-id="${CSS.escape(e.getAttribute("data-from"))}"]`);
    if (s) s.classList.add("src");
  });
}

/* Selecting a box shows its details under the map: the statement of a result, the Lean version of
   a classical theorem, the explanation of a step. */
function selectNode(pn, fig) {
  fig = fig || pn.closest(".pmap");
  const box = fig.querySelector(".pmap-detail");
  const prev = fig.querySelector(".pn.sel");
  if (prev) prev.classList.remove("sel");
  const hide = () => { box.hidden = true; box.innerHTML = ""; };
  if (!pn || prev === pn) return hide();
  const g = parseMap(fig.getAttribute("data-name"));
  const n = g.byId[pn.getAttribute("data-id")];
  const env = fig.closest(".env");
  const label = nodeLabel(n, env ? env.getAttribute("data-label") : "");
  let body = n.detail.length ? markdown(n.detail.join("\n")) : "";
  if (n.kind === "result" && DECLS[n.name]) {
    const t = titleOf(n.name);
    const href = constHref(n.name);
    body = `<p><strong>${inline(label)}</strong>${t ? ` (${inline(t)})` : ""}.</p>` + statementHtml(n.name) + body +
      (href ? `<p><a href="${esc(href)}">Go to ${inline(label)}</a></p>` : "");
  } else if (n.kind === "classical") {
    const lib = n.name ? libraryOf(n.name) : null;
    body = `<p><strong>${inline(label)}</strong>${n.cite && BIB[n.cite] ? " " + cite([n.cite]) : ""}.</p>` + body +
      (n.name ? `<p>In Lean${lib ? `, in ${esc(lib)}` : ""}: <code class="lean-code">${constLink(n.name, n.name)}</code>.</p>` : "");
  } else if (!body) return hide();
  pn.classList.add("sel");
  box.innerHTML = `<button class="pmap-close" type="button" aria-label="Close">×</button>${body}`;
  box.hidden = false;
  typeset(box);
}
