/* ------------------------------------------------------------------ bibliography */

/* The entries of a BibTeX file, by key, with their fields in lowercase. */
function parseBib(src) {
  const out = Object.create(null);
  const entry = /@(\w+)\s*[{(]\s*([^,\s]+)\s*,/g;
  let m;
  while ((m = entry.exec(src))) {
    const fields = {};
    let i = entry.lastIndex;
    for (;;) {
      const key = /\s*([\w-]+)\s*=\s*/y;
      key.lastIndex = i;
      const k = key.exec(src);
      if (!k) break;
      i = key.lastIndex;
      let val;
      if (src[i] === "{") {
        let depth = 0, j = i;
        for (; j < src.length; j++) {
          if (src[j] === "{") depth++;
          else if (src[j] === "}" && --depth === 0) break;
        }
        val = src.slice(i + 1, j);
        i = j + 1;
      } else if (src[i] === '"') {
        let j = i + 1;
        while (j < src.length && !(src[j] === '"' && src[j - 1] !== "\\")) j++;
        val = src.slice(i + 1, j);
        i = j + 1;
      } else {
        const w = /[^,})\s]*/y;
        w.lastIndex = i;
        val = w.exec(src)[0];
        i = w.lastIndex;
      }
      fields[k[1].toLowerCase()] = val.replace(/\s+/g, " ").trim();
      const sep = /\s*,?\s*/y;
      sep.lastIndex = i;
      sep.exec(src);
      i = sep.lastIndex;
    }
    if (!/^(comment|string|preamble)$/i.test(m[1])) out[m[2]] = fields;
    entry.lastIndex = Math.max(i, entry.lastIndex);
  }
  return out;
}

const BIB = parseBib(D.bibliography || "");

const ACCENTS = { "'": "\u0301", "`": "\u0300", "^": "\u0302", '"': "\u0308", "~": "\u0303",
  "=": "\u0304", ".": "\u0307", c: "\u0327", v: "\u030C", u: "\u0306", H: "\u030B" };
/* A BibTeX field as text: accents, dashes and braces resolved, the formulas `$...$` kept. */
function cleanTex(s) {
  return String(s || "").split(/(\$[^$]*\$)/).map((part, i) => (i % 2 ? part : cleanText(part)))
    .join("").trim();
}
/* A BibTeX field as HTML: its formulas are set by MathJax. */
function texHtml(s) {
  return cleanTex(s).split(/(\$[^$]*\$)/).map((part, i) =>
    (i % 2 ? `<span class="math">\\(${esc(part.slice(1, -1))}\\)</span>` : esc(part))).join("");
}
function cleanText(s) {
  return s
    .replace(/\\([`'^"~=.])\s*\{?\\?([A-Za-z])\}?/g, (m, a, c) => (c + ACCENTS[a]).normalize("NFC"))
    .replace(/\\([cvuH])\s*\{\\?([A-Za-z])\}/g, (m, a, c) => (c + ACCENTS[a]).normalize("NFC"))
    .replace(/\\ss\b\s*/g, "ß").replace(/\\o\b\s*/g, "ø").replace(/\\ae\b\s*/g, "æ")
    .replace(/\\&/g, "&").replace(/---/g, "—").replace(/--/g, "–").replace(/~/g, " ")
    .replace(/\\[a-zA-Z]+\s*/g, "").replace(/[{}]/g, "");
}
function bibAuthors(a) {
  const names = cleanTex(a).split(/\s+and\s+/).map((p) => {
    const [last, first] = p.split(",").map((s) => s.trim());
    return first ? `${first} ${last}` : last;
  });
  if (names[names.length - 1] === "others") return names[0] + " et al.";
  return names.length > 4 ? names[0] + " et al." : listOf(names);
}

/* The citations, numbered in the order of the texts that the page shows: the abstract, the
   development, then the foundations and the panels. A citation is `[Key]`, `[Key, Key]` or
   `[text][Key]`, outside code and mathematics. */
const CITE_NUM = Object.create(null);
(function numberCitations() {
  const texts = [META.abstract || ""];
  const seen = new Set();
  const decl = (n) => {
    if (seen.has(n)) return;
    seen.add(n);
    texts.push(note("informal", n) || (DECLS[n] || {}).doc || "");
    ["figure", "sketch", "diagram", "proof"].forEach((k) => texts.push(note(k, n) || ""));
  };
  (D.blocks || []).forEach((b) => (b.md !== undefined ? texts.push(b.md) : b.decl && decl(b.decl)));
  (D.main || []).forEach((m) => decl(m.name));
  TRUST.groups.forEach((g) => g.items.forEach(decl));
  TRUST.notations.forEach((x) => texts.push(note("informal", x.pattern || "") || x.doc || ""));
  Object.keys(META.axiomDocs || {}).forEach((k) => texts.push(META.axiomDocs[k]));
  PACKAGES.forEach((p) => texts.push(p.description || ""));
  Object.keys(DECLS).forEach(decl);
  let n = 0;
  const number = (key) => { if (!(key in CITE_NUM)) CITE_NUM[key] = ++n; };
  texts.forEach((t) => t.replace(/`[^`]*`|\$\$[\s\S]*?\$\$|\$[^$]*\$/g, "")
    .replace(/\]\[([^\]]+)\]|\[([^\][]+)\](?!\()/g, (m, k, inner) => {
      if (k) { if (BIB[k]) number(k); return m; }
      const keys = inner.split(/\s*[,;]\s*/);
      if (keys.every((key) => BIB[key])) keys.forEach(number);
      return m;
    }));
})();
const citeTitle = (k) => {
  const e = BIB[k];
  return `${bibAuthors(e.author || e.editor || "")}, ${cleanTex(e.title || "")}${e.year ? ` (${e.year})` : ""}`;
};
const citeHref = (k) => routeHref("development", "ref-" + k);
function cite(keys, text) {
  if (text !== undefined) {
    return `<a class="cite" href="${esc(citeHref(keys[0]))}" title="${esc(citeTitle(keys[0]))}">${text}</a>`;
  }
  return "[" + keys.map((k) =>
    `<a class="cite" href="${esc(citeHref(k))}" title="${esc(citeTitle(k))}">${CITE_NUM[k] || esc(k)}</a>`)
    .join(", ") + "]";
}

/* ------------------------------------------------------------------ inline Markdown */

/* Unicode mathematics, with `_x`, `_{...}`, `^x` and `^{...}` as sub- and superscripts. */
function mathText(s) {
  const cs = Array.from(s);
  let out = "";
  for (let i = 0; i < cs.length;) {
    const c = cs[i];
    if ((c === "_" || c === "^") && i > 0 && i + 1 < cs.length && cs[i + 1] !== " ") {
      const tag = c === "_" ? "sub" : "sup";
      if (cs[i + 1] === "{") {
        let depth = 1, j = i + 2;
        for (; j < cs.length && depth > 0; j++) {
          if (cs[j] === "{") depth++;
          else if (cs[j] === "}") depth--;
        }
        out += `<${tag}>${mathText(cs.slice(i + 2, j - 1).join(""))}</${tag}>`;
        i = j;
      } else {
        out += `<${tag}>${esc(cs[i + 1])}</${tag}>`;
        i += 2;
      }
      continue;
    }
    out += esc(c);
    i++;
  }
  return out;
}

/* Whether a code span that names no known constant is mathematics, as `x_i` or `E_ρ[g] = 0`,
   rather than code, as `lift_eq` or `git rev-parse HEAD`. A single identifier is mathematics if it
   is short or only has one-letter subscripts; another text, if it has a non-ASCII character or a
   subscript or a superscript. */
function isMath(t) {
  IDENT_RE.lastIndex = 0;
  const m = IDENT_RE.exec(t);
  if (m && m[0].length === t.length) {
    if (Array.from(t).length <= 2) return true;
    return t.includes("_") && t.split(".").every((part) =>
      part.split("_").slice(1).every((p) => Array.from(p).length <= 1 || /^\d+$/.test(p)));
  }
  return /[^\x00-\x7f]|[_^]/.test(t);
}

/* A code span: Lean code if it names a known constant, otherwise mathematics or plain code. */
function codeSpan(src) {
  const t = src.trim();
  let lean = KEYWORDS.has(t) || t === "sorry";
  if (!lean) forEachIdent(src, (id) => { if (REFS[id] !== undefined) lean = true; });
  if (!lean && isMath(t)) return `<span class="m">${mathText(src)}</span>`;
  return `<code class="lean-code">${highlight(src, null, { plain: true })}</code>`;
}

/* The width and the height of an image, so that the page keeps its place while it loads. */
function sizeAttrs(src) {
  const sz = MEDIA[src];
  return sz ? ` width="${sz[0]}" height="${sz[1]}"` : "";
}

/* A link of the text. `#Name` goes to the declaration `Name` on the page, `#slug` to a section of
   the development. */
function linkHtml(text, url) {
  if (!url.startsWith("#")) return extLink(url, text);
  const target = url.slice(1);
  const href = constHref(target) || routeHref("development", target);
  return href.startsWith("#") ? `<a href="${esc(href)}">${text}</a>` : extLink(href, text);
}

const unescapeHtml = (s) => s.replace(/&quot;/g, '"').replace(/&#39;/g, "'").replace(/&lt;/g, "<")
  .replace(/&gt;/g, ">").replace(/&amp;/g, "&");

/* Inline Markdown: code spans, mathematics in TeX (`$...$` and `$$...$$`, as in docgen), images,
   links, citations, emphasis. Code and mathematics are set aside first, so that nothing else
   touches them. */
function inline(text) {
  const held = [];
  const hold = (html) => "\u0000" + (held.push(html) - 1) + "\u0001";
  const holdMath = (html) => "\u0002" + (held.push(html) - 1) + "\u0003";
  let s = String(text);
  s = s.replace(/(`+)(?!`)([\s\S]*?[^`])\1(?!`)/g, (m, ticks, code) =>
    hold(codeSpan(/^ [\s\S]* $/.test(code) ? code.slice(1, -1) : code)));
  s = s.replace(/\\\$/g, () => hold("$"));
  s = s.replace(/\$\$([\s\S]+?)\$\$/g, (m, t) => hold(`<span class="math display">\\[${esc(t)}\\]</span>`));
  s = s.replace(/\$(?=\S)((?:\\[\s\S]|[^$\\])+?)\$(?!\d)/g, (m, t) =>
    /\s$/.test(t) ? m : holdMath(`<span class="math">\\(${esc(t)}\\)</span>`));
  s = s.replace(/\\([\\`*_{}\[\]()#+\-.!|<>~])/g, (m, c) => hold(esc(c)));
  s = esc(s);
  // the HTML that the rules write is set aside too, so that the emphasis does not touch it
  const emph = (x) => x
    .replace(/\*\*(?=\S)([\s\S]*?\S)\*\*/g, "<strong>$1</strong>")
    .replace(/(^|[^\w*])\*(?=[^\s*])([\s\S]*?[^\s*])\*(?!\w)/g, "$1<em>$2</em>")
    .replace(/(^|[^\w])_(?=\S)([\s\S]*?\S)_(?!\w)/g, "$1<em>$2</em>");
  // a URL may contain balanced parentheses, as `.../wiki/Flow_(mathematics)`
  const URL_RE = "((?:[^()\\s]|\\([^()\\s]*\\))+)";
  s = s.replace(new RegExp(`!\\[([^\\]]*)\\]\\(${URL_RE}(?:\\s+&quot;(.*?)&quot;)?\\)`, "g"), (m, alt, src, title) => {
    const u = unescapeHtml(src);
    return hold(`<img class="inline-img" src="${esc(safeUrl(u))}" alt="${alt}"${title ? ` title="${title}"` : ""}${sizeAttrs(u)} loading="lazy" decoding="async">`);
  });
  s = s.replace(new RegExp(`\\[([^\\]]+)\\]\\(${URL_RE}\\)`, "g"), (m, t, u) => hold(linkHtml(emph(t), unescapeHtml(u))));
  s = s.replace(/\[([^\]]+)\]\[([^\]]+)\]/g, (m, t, k) => (BIB[k] ? hold(cite([k], emph(t))) : m));
  s = s.replace(/\[([^\][]+)\]/g, (m, inner) => {
    const keys = inner.split(/\s*[,;]\s*/);
    return keys.every((k) => BIB[k]) ? hold(cite(keys)) : m;
  });
  s = s.replace(/(^|[\s(])(https?:\/\/[^\s<\u0000-\u0003]*[^\s<.,;:!?)\]'"\u0000-\u0003])/g, (m, pre, u) =>
    pre + hold(extLink(unescapeHtml(u), u)));
  s = emph(s);
  // An inline formula stays on one line with the characters glued to it, as in "$f$-almost,".
  s = s.replace(/([^\s\u0000-\u0003>]*)\u0002(\d+)\u0003([^\s\u0000-\u0003<]*)/g, (m, lead, k, tail) =>
    lead || tail ? `<span class="nobr">${lead}\u0002${k}\u0003${tail}</span>` : m);
  // the set-aside pieces, which may contain others
  const piece = /[\u0000\u0002](\d+)[\u0001\u0003]/g;
  for (let k = 0; k < 4 && piece.test(s); k++) {
    piece.lastIndex = 0;
    s = s.replace(piece, (m, i) => held[Number(i)]);
  }
  return s;
}

/* ------------------------------------------------------------------ figures */

/* The figures are numbered in the order of the page. */
let FIGURE = 0;
/* A figure alone on its row is at most this many times its own size, so that a text set at 9pt in
   the figure is about as large as the text of the page. */
const FIGURE_SCALE = 1.6;
const IMAGE_RE = /^[^\s|]+\.(svg|png|jpe?g|gif|webp|avif)$/i;

/* A block ```figure: one image per line, `path` or `path | caption`, then the caption. */
function figureHtml(body) {
  const images = [];
  const caption = [];
  body.split("\n").forEach((l) => {
    const [src, ...rest] = l.split("|");
    if (IMAGE_RE.test(src.trim())) images.push({ src: src.trim(), sub: rest.join("|").trim() });
    else if (l.trim()) caption.push(l.trim());
  });
  const n = ++FIGURE;
  const many = images.length > 1;
  const items = images.map((im, k) => {
    const letter = many ? String.fromCharCode(97 + k) + ")" : "";
    const sub = letter || im.sub ? `<figcaption>${letter ? `<b>${letter}</b> ` : ""}${inline(im.sub)}</figcaption>` : "";
    const sz = MEDIA[im.src];
    const width = !many && sz ? ` style="max-width: ${Math.round(FIGURE_SCALE * sz[0])}px"` : "";
    const alt = `Figure ${n}${letter ? " " + letter : ""}`;
    return `<div class="fig-item"${width}><button class="fig-zoom" type="button" aria-label="Enlarge ${alt}"><img src="${esc(im.src)}" alt="${alt}"${sizeAttrs(im.src)} loading="lazy" decoding="async"></button>${sub}</div>`;
  }).join("");
  const text = caption.join(" ");
  return `<figure class="fig" id="figure-${n}"><div class="fig-row">${items}</div><figcaption><b>Figure ${n}.</b>${text ? " " + inline(text) : ""}</figcaption></figure>`;
}

/* ------------------------------------------------------------------ block Markdown */

const indentOf = (l) => l.match(/^\s*/)[0].length;
const isBlank = (l) => /^\s*$/.test(l);
const FENCE_RE = /^(\s*)(`{3,}|~{3,})\s*([^`]*)$/;
const LIST_RE = /^(\s*)([*+-]|\d{1,9}[.)])(\s+|$)(.*)$/;
const HEADING_RE = /^\s{0,3}(#{1,6})\s+(.*?)\s*#*\s*$/;
const RULE_RE = /^\s{0,3}([-*_])(\s*\1){2,}\s*$/;
/* Whether a line starts a block that interrupts a paragraph. */
const interrupts = (l) => FENCE_RE.test(l) || HEADING_RE.test(l) || /^\s{0,3}>/.test(l) ||
  RULE_RE.test(l) || /^\s{0,3}([*+-]|1[.)])\s+\S/.test(l);

/* The cells of a row of a table: split at the bars outside code and formulas, and not escaped. */
function splitCells(l) {
  const cells = [""];
  let code = false, math = false;
  for (let i = 0; i < l.length; i++) {
    const c = l[i];
    if (c === "\\" && l[i + 1] === "|") { cells[cells.length - 1] += "|"; i++; continue; }
    if (c === "`") code = !code;
    else if (c === "$" && !code) math = !math;
    if (c === "|" && !code && !math) cells.push("");
    else cells[cells.length - 1] += c;
  }
  return cells.map((x) => x.trim());
}

/* Block Markdown. `opt.heading(level, text)` renders the headings. */
function markdown(text, opt) {
  opt = opt || {};
  // the HTML comments are notes of the author, not shown
  const lines = String(text || "").replace(/\r/g, "").replace(/<!--[\s\S]*?-->/g, "").split("\n");
  const out = [];
  let i = 0;
  while (i < lines.length) {
    const line = lines[i];
    if (isBlank(line)) { i++; continue; }
    let m;
    if ((m = FENCE_RE.exec(line))) {
      const fence = m[2];
      const lang = m[3].trim().split(/\s+/)[0];
      const close = new RegExp(`^\\s*${fence[0]}{${fence.length},}\\s*$`);
      const body = [];
      for (i++; i < lines.length && !close.test(lines[i]); i++) {
        body.push(lines[i].slice(Math.min(m[1].length, indentOf(lines[i]))));
      }
      i++;
      const code = body.join("\n");
      if (lang === "figure") out.push(figureHtml(code));
      else if (!lang || /^lean4?$/.test(lang)) out.push(`<pre class="lean"><code>${highlight(code, null)}</code></pre>`);
      else out.push(`<pre class="code"><code>${esc(code)}</code></pre>`);
      continue;
    }
    if ((m = HEADING_RE.exec(line))) {
      const level = m[1].length;
      out.push(opt.heading ? opt.heading(level, m[2]) : `<h${Math.min(6, level + 1)}>${inline(m[2])}</h${Math.min(6, level + 1)}>`);
      i++;
      continue;
    }
    if (RULE_RE.test(line)) { out.push("<hr>"); i++; continue; }
    if (line.includes("|") && i + 1 < lines.length &&
        /^\s*\|?\s*:?-+:?\s*(\|\s*:?-+:?\s*)*\|?\s*$/.test(lines[i + 1]) && lines[i + 1].includes("-")) {
      const row = (l) => splitCells(l.trim().replace(/^\|/, "").replace(/\|$/, ""));
      const aligns = row(lines[i + 1]).map((c) => (/:$/.test(c) ? (/^:/.test(c) ? "center" : "right") : ""));
      const head = row(line);
      const cell = (tag, c, k) => `<${tag}${aligns[k] ? ` style="text-align:${aligns[k]}"` : ""}>${inline(c)}</${tag}>`;
      const body = [];
      for (i += 2; i < lines.length && lines[i].includes("|") && !isBlank(lines[i]); i++) body.push(row(lines[i]));
      out.push(`<div class="table-wrap"><table class="rules"><thead><tr>${head.map((c, k) => cell("th", c, k)).join("")}</tr></thead><tbody>${body.map((r) => `<tr>${r.map((c, k) => cell("td", c, k)).join("")}</tr>`).join("")}</tbody></table></div>`);
      continue;
    }
    if (/^\s{0,3}>/.test(line)) {
      const buf = [];
      while (i < lines.length && !isBlank(lines[i])) buf.push(lines[i++].replace(/^\s{0,3}>\s?/, ""));
      out.push(`<blockquote>${markdown(buf.join("\n"), opt)}</blockquote>`);
      continue;
    }
    if ((m = LIST_RE.exec(line)) && m[4].trim()) {
      const indent = m[1].length;
      const ordered = /\d/.test(m[2]);
      const start = ordered ? parseInt(m[2], 10) : 1;
      const items = [];
      let loose = false;
      while (i < lines.length) {
        const l = lines[i];
        const mm = LIST_RE.exec(l);
        if (mm && mm[1].length === indent && /\d/.test(mm[2]) === ordered) {
          items.push({ lines: [mm[4]], indent: indent + mm[2].length + Math.max(1, mm[3].length) });
          i++;
          continue;
        }
        if (isBlank(l)) {
          let j = i + 1;
          while (j < lines.length && isBlank(lines[j])) j++;
          const next = j < lines.length ? LIST_RE.exec(lines[j]) : null;
          if (j < lines.length && ((next && next[1].length === indent) || indentOf(lines[j]) > indent)) {
            loose = true;
            items[items.length - 1].lines.push("");
            i = j;
            continue;
          }
          break;
        }
        if (indentOf(l) > indent) {
          const it = items[items.length - 1];
          it.lines.push(l.slice(Math.min(indentOf(l), it.indent)));
          i++;
          continue;
        }
        if (interrupts(l)) break;
        items[items.length - 1].lines.push(l.trim());
        i++;
      }
      const tag = ordered ? "ol" : "ul";
      out.push(`<${tag}${start !== 1 ? ` start="${start}"` : ""}>${items.map((it) => {
        let html = markdown(it.lines.join("\n"), opt);
        if (!loose) html = html.replace(/^<p>([\s\S]*?)<\/p>/, "$1");
        return `<li>${html}</li>`;
      }).join("")}</${tag}>`);
      continue;
    }
    // a paragraph, which goes on through a displayed formula
    const buf = [];
    let display = false;
    while (i < lines.length) {
      const l = lines[i];
      if (!display && (isBlank(l) || (buf.length && interrupts(l)))) break;
      buf.push(l.trim());
      if ((l.match(/\$\$/g) || []).length % 2) display = !display;
      i++;
    }
    out.push(`<p>${inline(buf.join("\n"))}</p>`);
  }
  return out.join("\n");
}
