/* ------------------------------------------------------------------ Lean code */

/* Identifiers, as Lean reads them: letters, `_`, Greek letters but λ, Π and Σ, the letter-like
   symbols and the mathematical alphanumerics, then also digits, `'`, `!`, `?` and subscripts. */
const ID_FIRST = "A-Za-z_\\u00C0-\\u00D6\\u00D8-\\u00F6\\u00F8-\\u017F\\u0391-\\u039F\\u03A1\\u03A4-\\u03A9" +
  "\\u03B1-\\u03BA\\u03BC-\\u03C9\\u03CA-\\u03FB\\u1F00-\\u1FFE\\u2100-\\u214F\\u{1D49C}-\\u{1D59F}";
const ID_REST = ID_FIRST + "0-9'!?\\u2080-\\u2089\\u2090-\\u209C\\u1D62-\\u1D6A\\u2C7C";
const ID_PART = `(?:[${ID_FIRST}][${ID_REST}]*|«[^»]*»)`;
const IDENT_RE = new RegExp(`${ID_PART}(?:\\.${ID_PART})*`, "uy");
const ID_CHAR_RE = new RegExp(`[${ID_REST}.]`, "u");

/* Calls `f` on each identifier of a text. */
function forEachIdent(src, f) {
  const re = new RegExp(IDENT_RE.source, "gu");
  let m;
  while ((m = re.exec(src))) {
    const before = src[m.index - 1] || "";
    if (!ID_CHAR_RE.test(before)) f(m[0]);
  }
}

/* The keywords of Lean that the page knows without the data: the tokens of the sources come with
   it (`D.keywords`), tactics included. */
const CORE_KEYWORDS = new Set(words("theorem lemma def abbrev instance structure class inductive " +
  "axiom opaque example where extends deriving fun λ by have show from let in if then else match " +
  "with do return at calc suffices obtain namespace section end open variable universe " +
  "noncomputable private protected public partial unsafe mutual Type Prop Sort sorry"));
const DECL_KEYWORDS = new Set(words("theorem lemma def abbrev instance structure class inductive " +
  "axiom opaque example"));
const isKeyword = (id) => KEYWORDS.has(id) || CORE_KEYWORDS.has(id);

/* Lean source as HTML: keywords, brackets, comments, strings, numbers, the declared name, colored as
   by the lexer of CodeLatex with the Catppuccin Latte theme. An identifier links
   to the constant it names: from `links` (an identifier → constant map of a declaration) or else
   from the names of the text. With `opt.plain`, no keyword is marked. */
function highlight(src, links, opt) {
  opt = opt || {};
  const n = src.length;
  let out = "";
  let declName = false;   // after `theorem`, `def`, ...: the next identifier is the declared name
  const span = (cls, text) => `<span class="${cls}">${esc(text)}</span>`;
  for (let i = 0; i < n;) {
    const c = src[i];
    const two = src.substr(i, 2);
    if (two === "--") {
      const j = src.indexOf("\n", i);
      const end = j < 0 ? n : j;
      out += span("c", src.slice(i, end));
      i = end;
      continue;
    }
    if (two === "/-") {
      let depth = 0, j = i;
      while (j < n) {
        if (src.substr(j, 2) === "/-") { depth++; j += 2; }
        else if (src.substr(j, 2) === "-/") { depth--; j += 2; if (depth === 0) break; }
        else j++;
      }
      out += span("c", src.slice(i, j));
      i = j;
      continue;
    }
    if (c === '"') {
      let j = i + 1;
      while (j < n && src[j] !== '"') j += src[j] === "\\" ? 2 : 1;
      out += span("s", src.slice(i, j + 1));
      i = j + 1;
      declName = false;
      continue;
    }
    if (c === "'" && !ID_CHAR_RE.test(src[i - 1] || "") && /^'(\\.|[^\\'])'/.test(src.slice(i, i + 4))) {
      const lit = /^'(\\.|[^\\'])'/.exec(src.slice(i, i + 4))[0];
      out += span("s", lit);
      i += lit.length;
      continue;
    }
    if (two === "@[") {
      let depth = 0, j = i + 1;
      for (; j < n; j++) {
        if (src[j] === "[") depth++;
        else if (src[j] === "]" && --depth === 0) break;
      }
      out += span("a", src.slice(i, j + 1));
      i = j + 1;
      continue;
    }
    if ("()[]{}⦃⦄⟨⟩".includes(c)) {
      out += span("b", c);
      declName = false;
      i++;
      continue;
    }
    if (/[0-9]/.test(c) && !ID_CHAR_RE.test(src[i - 1] || "")) {
      const m = /^[0-9]+(\.[0-9]+)?/.exec(src.slice(i));
      out += span("n", m[0]);
      i += m[0].length;
      declName = false;
      continue;
    }
    IDENT_RE.lastIndex = i;
    const m = ID_CHAR_RE.test(src[i - 1] || "") ? null : IDENT_RE.exec(src);
    if (m) {
      const id = m[0];
      let next = false;
      if (id === "sorry") out += span("x", id);
      else if (!opt.plain && isKeyword(id)) {
        out += span("k", id);
        next = DECL_KEYWORDS.has(id);
      } else if (declName) out += span("d", id);
      else {
        const k = own(links, id) !== undefined ? own(links, id) : REFS[id];
        out += k !== undefined && !opt.noLinks ? constLink(constName(k), id) : esc(id);
      }
      declName = next;
      i += id.length;
      continue;
    }
    if (!/\s/.test(c)) declName = false;
    out += esc(c);
    i++;
  }
  return out;
}

/* The keyword of a declaration. */
const KIND_KEYWORD = { theorem: "theorem", def: "def", abbrev: "abbrev", instance: "instance",
  structure: "structure", class: "class", inductive: "inductive", opaque: "opaque", axiom: "axiom" };

/* The statement of a declaration as Lean elaborates it: every hypothesis explicit, and a link for
   every constant. */
function signatureHtml(name) {
  const d = DECLS[name];
  const kw = own(KIND_KEYWORD, d.kind);
  let out = kw ? `<span class="k">${kw}</span> ` : "";
  (d.sig || []).forEach((p, idx) => {
    let [text, k] = typeof p === "string" ? [p, undefined] : p;
    if (idx === 0) {
      // the declared name, without its universe parameters
      text = text.replace(/^(\S+?)\.\{[^}]*\}/, "$1");
      const m = /^(\S+)([\s\S]*)$/.exec(text);
      if (m) {
        out += `<span class="d">${esc(m[1])}</span>` + highlight(m[2], null, { noLinks: true });
        return;
      }
    }
    const m = /^(\s*)([\s\S]*?)(\s*)$/.exec(text);
    if (k === undefined || !m[2] || /^[()[\]{},:⦃⦄⟨⟩]+$/.test(m[2])) {
      out += highlight(text, null, { noLinks: true });
      return;
    }
    out += esc(m[1]) + constLink(constName(k), m[2]) + esc(m[3]);
  });
  return out;
}

/* The source of a declaration, with links. */
const sourceHtml = (name) => highlight(DECLS[name].src || "", DECLS[name].links || {});
