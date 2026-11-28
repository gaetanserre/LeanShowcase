/* ------------------------------------------------------------------ declarations */

const KIND_NAME = { theorem: "Theorem", def: "Definition", abbrev: "Definition", opaque: "Definition",
  structure: "Structure", class: "Class", inductive: "Inductive type", instance: "Instance",
  axiom: "Axiom" };
const kindName = (name) => own(KIND_NAME, (DECLS[name] || {}).kind) || "Declaration";

/* A docstring `**Title** (Theorem 3 of [Paper]). Statement`: its title, its reference and the
   statement. */
function docParts(doc) {
  const m = /^\s*\*\*(.+?)\*\*\s*([\s\S]*)$/.exec(doc || "");
  if (!m) return { title: null, ref: null, rest: doc || "" };
  let rest = m[2];
  let ref = null;
  const r = /^\(((?:[^()]|\([^()]*\))*)\)\s*[.:]\s*/.exec(rest);
  if (r) { ref = r[1]; rest = rest.slice(r[0].length); }
  return { title: m[1].replace(/[.:]$/, ""), ref, rest: rest.replace(/^[.:]\s*/, "") };
}
const titleOf = (name) => TITLES[name] || docParts((DECLS[name] || {}).doc).title;

/* The informal statement of a declaration: its block `informal`, or else its docstring. */
function statementHtml(name) {
  const informal = note("informal", name);
  if (informal) return markdown(informal);
  const d = DECLS[name] || {};
  return markdown(docParts(d.doc).rest);
}

/* The axioms outside the standard ones, that a declaration depends on. */
const extraAxioms = (name) => ((DECLS[name] || {}).axioms || []).filter(isExtraAxiom);

/* ------------------------------------------------------------------ places */

const BLOCKS = D.blocks || [];
const MAIN = (D.main || []).filter((m) => DECLS[m.name]);
const MAIN_SET = new Set(MAIN.map((m) => m.name));
/* Without any label in `showcase.md`, the results are numbered in order, as in a paper. */
const AUTO_NUMBER = !BLOCKS.some((b) => b.decl && b.label);
(function places() {
  let k = 0;
  BLOCKS.forEach((b) => {
    if (!b.decl || !DECLS[b.decl] || CARD[b.decl]) return;
    CARD[b.decl] = true;
    LABEL[b.decl] = b.label || (AUTO_NUMBER ? `${kindName(b.decl)} ${++k}` : null);
  });
  MAIN.forEach((m) => { if (!LABEL[m.name] && m.label) LABEL[m.name] = m.label; });
  TRUST.groups.forEach((g) => g.items.forEach((n) => { if (!CARD[n]) TRUSTED[n] = true; }));
})();
const labelOf = (name) => LABEL[name] || kindName(name);
const SHOWN = Object.keys(CARD);

/* ------------------------------------------------------------------ comparator */

const CHECKERS = {
  "Lean default": ["The kernel of Lean, the small program that checks every proof, run again on the whole solution.",
    [["Lean", "https://github.com/leanprover/lean4"]]],
  "Lean paranoid": ["The same kernel in a stricter mode, which also checks what the default mode takes from the elaborator.",
    [["Lean", "https://github.com/leanprover/lean4"]]],
  "lean4lean": ["A kernel for Lean written in Lean, meant to be verified against a model of the type theory of Lean.",
    [["lean4lean", "https://github.com/digama0/lean4lean"]]],
  "nanoda": ["An independent type checker for Lean, written in Rust.",
    [["nanoda_lib", "https://github.com/ammkrn/nanoda_lib"]]],
};

/* The verdict of the report of comparator embedded in the page, if any. */
const CMP = (function () {
  const c = D.comparator || {};
  const rep = c.report;
  if (!rep || !rep.report) return { state: "none", kernels: [], config: c.config || {} };
  const r = rep.report;
  const order = Object.keys(CHECKERS);
  const rank = (k) => (order.includes(k) ? order.indexOf(k) : order.length);
  const kernels = Object.keys(r.kernel_reports || {}).sort((a, b) => rank(a) - rank(b));
  const judgement = (k) => (own(r.kernel_reports, k) || {}).judgement;
  const message = (st) => {
    const o = st.output || {};
    if (o.str && o.str.string) return o.str.string.trim();
    if (o.proc) {
      const t = ((o.proc.stderr || "") + "\n" + (o.proc.stdout || "")).trim();
      return t.length > 800 ? "…" + t.slice(-800) : t;
    }
    return "";
  };
  const failedSteps = Object.keys(r).filter((k) => k !== "kernel_reports" && r[k] && r[k].judgement && r[k].judgement !== "success")
    .map((k) => ({ key: k, judgement: r[k].judgement, message: message(r[k]) }));
  let date = null;
  if (c.time) {
    try { date = new Date(c.time * 1000).toLocaleDateString("en-GB", { year: "numeric", month: "long", day: "numeric" }); }
    catch (e) { date = null; }
  }
  return {
    state: rep.judgement === "accepted" ? "accepted" : "rejected", kernels, judgement,
    failed: kernels.filter((k) => !["success", "skipped"].includes(judgement(k))),
    failedSteps, sandboxed: rep.sandboxed !== false, date, config: c.config || {},
  };
})();

/* Why comparator rejected the formalization, in its own words. */
function rejection() {
  const line = CMP.failedSteps.find((st) => st.message && !st.message.includes("\n") && st.message.length <= 160);
  if (line) return line.message;
  return CMP.failedSteps.map((st) => `${st.key}: ${st.judgement}`)
    .concat(CMP.failed.map((k) => `${k}: ${CMP.judgement(k)}`)).join("; ") || "a check failed";
}

/* The verdict of comparator, as a paragraph. */
function verdictHtml(here) {
  if (CMP.state === "none") return "";
  const when = CMP.date ? ` on ${esc(CMP.date)}` : "";
  const more = here ? "" : ` <a href="#comparator">What this means</a>.`;
  if (CMP.state === "rejected") {
    return `<p class="verdict bad"><span class="tag bad">Rejected</span>Comparator, run${when}, rejected this formalization: ${esc(rejection())}.${more}</p>`;
  }
  const n = (CMP.config.theorem_names || []).length;
  const ks = CMP.kernels.length;
  return `<p class="verdict ok"><span class="tag ok">Checked</span>Comparator, run${when}, found that ${n ? `the ${n} theorems` : "the theorems"} state what the challenge states, that their proofs use only the permitted axioms, and that ${ks > 1 ? `${count(ks)} independent kernels accept them` : "the kernel accepts them"}${CMP.sandboxed ? "" : ". The run was not sandboxed"}.${more}</p>`;
}

/* The seal of comparator: its verdict, set large on the front page and on its own page. */
function sealHtml() {
  if (CMP.state === "none") return "";
  if (CMP.state === "rejected") {
    return `<a class="seal bad" href="#comparator"><span class="seal-mark" aria-hidden="true">✕</span><span class="seal-text"><b>Rejected by comparator</b><span>${esc(rejection())}</span></span></a>`;
  }
  const n = (CMP.config.theorem_names || []).length;
  const ks = CMP.kernels.length;
  const facts = [];
  if (n) facts.push(`${n} theorems match their statements`);
  facts.push("permitted axioms only");
  if (ks) facts.push(`${ks} independent ${ks === 1 ? "kernel" : "kernels"}`);
  if (CMP.date) facts.push(esc(CMP.date));
  if (!CMP.sandboxed) facts.push("not sandboxed");
  // a fact is never cut at the end of a line
  const line = facts.map((f) => `<span class="nobr">${f}</span>`).join(" · ");
  return `<a class="seal ok" href="#comparator"><span class="seal-mark" aria-hidden="true">✓</span><span class="seal-text"><b>Checked by comparator</b><span>${line}</span></span></a>`;
}

/* ------------------------------------------------------------------ libraries and axioms */

/* What readers know of the usual libraries: their names and their descriptions. The key
   `libraries` of `showcase.md` comes first, then these, then the description of the lakefile. */
const KNOWN_LIBRARIES = {
  mathlib: ["Mathlib", "The community library of formalized mathematics: algebra, analysis, measure " +
    "theory, probability, topology... The statements use its definitions (real numbers, measures, " +
    "integrals, derivatives, Hilbert spaces)."],
  tauceti: ["Tau Ceti", "A library of formalized mathematics built on Mathlib, incubated by the Lean " +
    "FRO and the Mathlib Initiative. Humans write its roadmaps and the public criteria of its " +
    "review. AIs write its code, and other AIs review it against these criteria."],
};
const OUTSIDE_MATHLIB = "A library outside Mathlib. Its definitions are not reviewed by the Mathlib community.";
PACKAGES.forEach((p) => {
  const known = own(KNOWN_LIBRARIES, String(p.name || "").toLowerCase());
  if (known) p.label = known[0];
  p.description = p.description || (known && known[1]) || p.lakeDescription || null;
});
const projectPackage = PACKAGES[META.project] || {};
const LEAN_PACKAGE = PACKAGES.find((p) => p.kind === "lean") || { modules: 0, statementModules: null };
const hasChallenge = CMP.state !== "none" && PACKAGES.some((p) => p.statementModules !== null && p.statementModules !== undefined);
const MATHLIB = PACKAGES.find((p) => p.name === "mathlib");
/* The libraries, as a reader sees them: Mathlib with its dependencies, then the others. */
const LIBRARIES = (function () {
  const deps = PACKAGES.filter((p) => p.partOf === "mathlib");
  const sum = (key) => (p) => (p[key] || 0) + (p === MATHLIB ? deps.reduce((n, q) => n + (q[key] || 0), 0) : 0);
  const libs = PACKAGES.filter((p) => p.kind !== "lean" && p.kind !== "project" && !(MATHLIB && deps.includes(p)))
    .map((p) => Object.assign({}, p, {
      modules: sum("modules")(p),
      statementModules: hasChallenge ? sum("statementModules")(p) : null,
      with: p === MATHLIB ? deps.filter((q) => q.modules > 0).map((q) => q.label) : [],
    }));
  const rank = (l) => (l === MATHLIB || l.name === "mathlib" ? 0 : l.kind === "reviewed" ? 1 : 2);
  return libs.sort((a, b) => rank(a) - rank(b) || b.modules - a.modules || a.label.localeCompare(b.label));
})();
const usedLibs = LIBRARIES.filter((l) => l.modules > 0);
const statementLibs = hasChallenge ? usedLibs.filter((l) => l.statementModules > 0) : usedLibs;
const proofLibs = hasChallenge ? usedLibs.filter((l) => !(l.statementModules > 0)) : [];
/* The libraries that only the proofs use are checked, not trusted, if comparator accepted. */
const replayed = CMP.state === "accepted";
const trustedLibs = replayed ? statementLibs : usedLibs;

const TPIL = "https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/";
const AXIOMS = {
  "propext": {
    title: "Propositional extensionality",
    plain: "Two statements that imply each other are equal.",
    math: String.raw`For all propositions $P$ and $Q$, $$(P \Leftrightarrow Q) \implies P = Q.$$`,
    lean: "axiom propext {a b : Prop} : (a ↔ b) → a = b",
    why: "It lets one replace a statement by an equivalent one anywhere. It holds in every " +
      "standard foundation of mathematics.",
    wiki: "https://en.wikipedia.org/wiki/Extensionality",
  },
  "Quot.sound": {
    title: "Quotients",
    plain: "Two elements related by a relation r have the same class in the quotient by r.",
    math: String.raw`For every set $\alpha$, every relation $r$ on $\alpha$ and all $a, b \in \alpha$, $$r(a, b) \implies [a]_r = [b]_r,$$ where $[a]_r$ is the equivalence class of $a$ in the quotient $\alpha / r$.`,
    lean: "axiom Quot.sound {α : Sort u} {r : α → α → Prop} {a b : α} :\n  r a b → Quot.mk r a = Quot.mk r b",
    why: "Quotients build the integers, the rationals, the reals and many other objects. " +
      "Function extensionality (two functions equal at every point are equal) follows from it.",
    wiki: "https://en.wikipedia.org/wiki/Quotient_type",
  },
  "Classical.choice": {
    title: "Axiom of choice",
    plain: "From the knowledge that a set has an element, one can pick one.",
    math: String.raw`There is a function $\varepsilon$ that picks an element of every nonempty set: for every set $\alpha$, $$\alpha \neq \emptyset \implies \varepsilon(\alpha) \in \alpha.$$`,
    lean: "axiom Classical.choice {α : Sort u} : Nonempty α → α",
    why: "It gives classical logic (the excluded middle follows from it by Diaconescu's " +
      "theorem) and the choices used throughout analysis.",
    wiki: "https://en.wikipedia.org/wiki/Axiom_of_choice",
  },
  "sorryAx": {
    title: "Unfinished proof", extra: true,
    plain: "A placeholder for a missing proof. It proves anything.",
    math: String.raw`Every proposition $P$ is true.`,
    lean: "axiom sorryAx (α : Sort u) (synthetic := false) : α",
    why: "A result that depends on it is not proved.",
  },
  "Lean.ofReduceBool": {
    title: "Trust in the compiler", extra: true,
    plain: "The result of a computation run by compiled code is accepted without a kernel check.",
    math: String.raw`For all booleans $a$ and $b$, if the compiled program evaluates $a$ to $b$, then $$a = b.$$`,
    lean: "axiom Lean.ofReduceBool (a b : Bool) (h : Lean.reduceBool a = b) : a = b",
    why: "Used by `native_decide`. It adds the Lean compiler to what one has to trust.",
  },
  "Lean.trustCompiler": {
    title: "Trust in the compiler", extra: true,
    plain: "Marks the use of compiled code in a proof.",
    lean: "axiom Lean.trustCompiler : True",
    why: "It adds the Lean compiler to what one has to trust.",
  },
};
function isExtraAxiom(a) { return !own(AXIOMS, a) || !!AXIOMS[a].extra; }
const ALL_AXIOMS = TRUST.axioms.map((a) => a.name);
const AXIOM_ORDER = Object.keys(AXIOMS);
const axiomRank = (a) => AXIOM_ORDER.indexOf(a);

const codeName = (x) => `<code>${esc(x)}</code>`;
/* What Lean has checked: every proof, but those that use `sorry`. */
const CHECKED_SENTENCE = ALL_AXIOMS.includes("sorryAx")
  ? "Lean has checked every proof, but some results depend on <code>sorry</code>: they are not proved."
  : "Lean has checked every proof.";
function axiomsSentence() {
  const axs = ALL_AXIOMS.slice().sort((a, b) => axiomRank(a) - axiomRank(b) || a.localeCompare(b));
  const extra = axs.filter(isExtraAxiom);
  if (extra.length) {
    return `Some results depend on ${extra.length > 1 ? "axioms" : "an axiom"} outside the standard ones of Lean: ${listOf(extra.map(codeName))}.`;
  }
  return `Only the standard axioms of Lean${axs.length ? ` (${listOf(axs.map(codeName))})` : ""}, and no ${codeName("sorry")}.`;
}
const libLabel = (l) => esc(l.label);
function librariesSentence() {
  const lean = "Lean";
  if (!usedLibs.length) return "Lean alone: no other library.";
  const it = (ls) => (ls.length > 1 ? "them" : "it");
  if (!hasChallenge) return `${listOf([lean].concat(usedLibs.map(libLabel)))}.`;
  let s = `The statements use ${listOf([lean].concat(statementLibs.map(libLabel)))}.`;
  if (proofLibs.length) {
    s += ` Only the proofs use ${listOf(proofLibs.map(libLabel))}${replayed
      ? `, which comparator checks: you do not need to trust ${it(proofLibs)}.`
      : `. Comparator rejected the formalization, so you trust ${it(proofLibs)} too.`}`;
  }
  return s;
}
const DEF_COUNT = TRUST.groups.reduce((n, g) => n + g.items.length, 0) + TRUST.notations.length;
/* The files that the development presents: their definitions are read there. */
const PRESENTED = (META.presented || []).map((n) => {
  const i = MODULES.findIndex((m) => m[0] === n);
  return i >= 0 ? modulePath(i) : n;
});
const presentedNote = () => PRESENTED.length
  ? ` The definitions of ${PRESENTED.length > 1 ? "the presented files" : listOf(PRESENTED.map(codeName))} are stated with the results, in the <a href="#development">development</a>.`
  : "";
function definitionsSentence() {
  if (!DEF_COUNT) return `No definition outside the reviewed libraries and the development.${presentedNote()}`;
  return `${plural(DEF_COUNT, "definition")} outside the reviewed libraries and the presented files. No checker can tell whether they mean what they should: they are shown in full, to be read.`;
}

/* ------------------------------------------------------------------ chrome */

const PAGES = [["", "Overview"], ["foundations", "Foundations"], ["development", "Development"]];

function masthead(page) {
  return `<header class="masthead"><div class="masthead-in">
    <a class="brand" href="#"><span class="brand-mark" aria-hidden="true">⊢</span><span class="brand-title">${esc(META.title)}</span></a>
    ${CMP.state === "accepted" ? `<a class="mast-check" href="#comparator"><span aria-hidden="true">✓</span>Checked by comparator</a>` : ""}
    <nav aria-label="Pages">${PAGES.map(([p, t]) =>
      `<a href="#${p}"${p === page ? ' aria-current="page"' : ""}>${t}</a>`).join("")}</nav>
  </div></header>`;
}

function colophon() {
  const bits = [];
  if (META.repository) bits.push(extLink(META.repository, "Source"));
  if (META.docs) bits.push(extLink(META.docs, "API documentation"));
  bits.push(`<span>Lean ${esc(META.lean || "")}</span>`);
  if (META.rev) {
    const commit = `Commit ${esc(META.rev.slice(0, 7))}`;
    bits.push(`<span>${META.repository ? extLink(`${META.repository}/tree/${META.rev}`, commit) : commit}${META.dirty ? ` <span title="The website was generated from files that differ from this commit.">(modified)</span>` : ""}</span>`);
  }
  bits.push(`<span>Made with ${extLink("https://github.com/gaetanserre/LeanShowcase", "Showcase")}</span>`);
  return `<footer class="colophon">${bits.join("")}</footer>`;
}

/* A row of a sheet: a label in the margin, then the content. */
const row = (id, label, body, num) =>
  `<section class="row"${id ? ` id="${esc(id)}"` : ""}><h2 class="row-label">${num ? `<span class="n">${num}</span>` : ""}${label}</h2><div class="row-body">${body}</div></section>`;

/* ------------------------------------------------------------------ theorems */

/* The kind of a declaration, for its color: proved, defined, assumed, or resting on `sorry`. */
function kindClass(name) {
  const d = DECLS[name] || {};
  if (d.kind === "axiom") return "k-ax";
  if (extraAxioms(name).includes("sorryAx")) return "k-bad";
  return d.kind === "theorem" ? "k-thm" : "k-def";
}

/* A declaration as a result: its label and its title, its statement, its figures, its proof, and the
   bar to see its Lean version. `where` is the page. */
function envHtml(name, where) {
  const d = DECLS[name];
  if (!d) return "";
  const isThm = d.kind === "theorem";
  const label = labelOf(name);
  const parts = docParts(d.doc);
  const title = TITLES[name] || parts.title;
  let ref = parts.ref;
  if (ref && label && ref.startsWith(label)) ref = ref.slice(label.length).replace(/^\s*(of|in)\s+/, "");
  let body = statementHtml(name);
  if (!body.trim()) body = `<pre class="lean lean-sig"><code>${signatureHtml(name)}</code></pre>`;
  const after = [];
  if (note("figure", name)) after.push(figureHtml(note("figure", name)));
  if (isThm && note("sketch", name)) {
    after.push(`<p><span class="inline-label">Proof idea</span>${inline(note("sketch", name).replace(/\s*\n\s*/g, " "))}</p>`);
  }
  if (isThm && note("diagram", name)) after.push(mapHtml(name, label));
  if (isThm && note("proof", name)) {
    // "Proof." runs into the first paragraph
    let proof = markdown(note("proof", name));
    proof = proof.startsWith("<p>") ? `<p><span class="proof-label">Proof.</span> ${proof.slice(3)}`
      : `<p><span class="proof-label">Proof.</span></p>${proof}`;
    after.push(`<details class="proof"><summary></summary><div class="proof-body prose">${proof}</div><span class="qed" role="img" aria-label="End of proof"></span></details>`);
  }
  const written = note("sketch", name) || note("diagram", name) || note("proof", name);
  const uses = (d.uses || []).filter((u) => CARD[u]);
  if (isThm && !written && uses.length) {
    after.push(`<p class="uses"><span class="inline-label">Uses</span>${listOf(uses.map((u) => `<a href="${esc(routeHref("development", u))}">${inline(labelOf(u))}</a>`))}</p>`);
  }
  const main = where === "development" && MAIN_SET.has(name);
  return `<section class="env ${kindClass(name)}" id="${esc(where === "development" ? "d:" + name : "o:" + name)}" data-name="${esc(name)}" data-label="${esc(label)}">
    <div class="env-main">
    ${main ? `<p class="env-kicker">${isThm ? "Main result" : "Key definition"}</p>` : ""}
    <p class="env-label"><span class="mark"></span><b>${inline(label)}</b>${ref && ref.trim() ? `<span class="ref">${inline(ref.trim())}</span>` : ""}${checkedHtml(name)}</p>
    ${title ? `<p class="env-title">${inline(title)}</p>` : ""}
    <div class="env-body prose">${body}</div>
    ${after.length ? `<div class="after prose">${after.join("")}</div>` : ""}
    </div>
    ${leanBar(name, where)}
    <div class="panels"></div>
  </section>`;
}

/* Whether comparator checked a theorem, in its label line. */
function checkedHtml(name) {
  const d = DECLS[name];
  if (d.kind !== "theorem" || CMP.state !== "accepted") return "";
  return d.checked ? `<a class="checked" href="#comparator" title="Comparator checked this theorem">✓ Checked by comparator</a>`
    : `<span class="unchecked">Not checked by comparator</span>`;
}

/* The bar under a result: the buttons that show its Lean statement, its source and the comments of
   its proof, its Lean name, and the links to its source and its documentation. */
function leanBar(name, where) {
  const d = DECLS[name];
  const isThm = d.kind === "theorem";
  const button = (kind, text) => `<button type="button" data-panel="${kind}" aria-expanded="false">${text}</button>`;
  const buttons = [button("sig", "Statement")];
  if (d.src) buttons.push(button("src", isThm ? "Proof" : "Definition"));
  const written = note("sketch", name) || note("diagram", name) || note("proof", name);
  if (isThm && !written && ((d.comments || []).length || (d.aux || []).some((a) => (DECLS[a] || {}).comments))) {
    buttons.push(button("comments", "Comments"));
  }
  const bits = [`<span class="seg" role="group" aria-label="Lean">${buttons.join("")}</span>`,
    `<code class="lean-name">${esc(display(name))}</code>`];
  const src = sourceUrl(d);
  if (src) bits.push(extLink(src, "Source ↗"));
  const docs = docsUrl(name);
  if (docs) bits.push(extLink(docs, "Docs ↗"));
  if (where !== "development" && CARD[name]) bits.push(`<a href="${esc(routeHref("development", name))}">In context</a>`);
  const extra = d.kind === "axiom" ? [] : extraAxioms(name);
  if (extra.length) {
    bits.push(`<a class="flag" href="#foundations/axioms">${extra.includes("sorryAx") ? "Uses sorry" : `Uses ${listOf(extra.map((x) => esc(display(x))))}`}</a>`);
  }
  return `<div class="lean-bar">${bits.join("")}</div>`;
}

/* A panel under a result. */
function panelHtml(name, kind) {
  const d = DECLS[name];
  if (kind === "sig") {
    return `<div class="panel" data-kind="sig"><p class="caption">Statement, as Lean elaborates it</p><pre class="lean"><code>${signatureHtml(name)}</code></pre></div>`;
  }
  const aux = (d.aux || []).filter((a) => DECLS[a]);
  if (kind === "src") {
    return `<div class="panel" data-kind="src"><p class="caption">${esc(modulePath(d.mod) || moduleName(d.mod))}${d.line ? ` · lines ${d.line}–${d.end}` : ""}</p><pre class="lean"><code>${sourceHtml(name)}</code></pre>${aux.length ? `<div class="aux">${aux.map((a) =>
      `<h5>${esc(display(a))} <span class="muted">(private)</span></h5><pre class="lean"><code>${sourceHtml(a)}</code></pre>`).join("")}</div>` : ""}</div>`;
  }
  const comments = (cs) => `<ul class="comments">${cs.map(([k, t]) => `<li class="d${Math.min(3, k)}">${inline(t)}</li>`).join("")}</ul>`;
  return `<div class="panel" data-kind="comments"><p class="caption">Comments of the Lean proof, in order</p>${(d.comments || []).length ? comments(d.comments) : ""}${aux.filter((a) => (DECLS[a].comments || []).length).map((a) =>
    `<div class="aux"><h5>${esc(display(a))}</h5>${DECLS[a].doc ? markdown(DECLS[a].doc) : ""}${comments(DECLS[a].comments)}</div>`).join("")}</div>`;
}

/* ------------------------------------------------------------------ overview */

const THEOREMS = SHOWN.filter((n) => DECLS[n].kind === "theorem");
const EXTRA_AXIOMS = ALL_AXIOMS.filter(isExtraAxiom);

/* The line of status under the title: what the page holds. */
function statusLine() {
  const items = [];
  items.push(`<a href="#development"><span class="mark k-thm"></span><b>${THEOREMS.length}</b>${THEOREMS.length === 1 ? "theorem" : "theorems"}</a>`);
  items.push(`<a href="#foundations/definitions"><span class="mark k-def"></span><b>${DEF_COUNT}</b>${DEF_COUNT === 1 ? "definition" : "definitions"} to read</a>`);
  items.push(EXTRA_AXIOMS.length
    ? `<a class="bad" href="#foundations/axioms"><span class="mark k-ax"></span>${EXTRA_AXIOMS.includes("sorryAx") ? "Uses sorry" : `<b>${EXTRA_AXIOMS.length}</b>non-standard ${EXTRA_AXIOMS.length === 1 ? "axiom" : "axioms"}`}</a>`
    : `<a href="#foundations/axioms"><span class="mark"></span>Standard axioms only</a>`);
  return `<ul class="status">${items.map((i) => `<li>${i}</li>`).join("")}</ul>`;
}

function pageOverview() {
  const actions = [`<a class="btn primary" href="#development">Read the development</a>`,
    `<a class="btn" href="#foundations">What it rests on</a>`];
  if (META.paper) actions.push(META.paperUrl ? extLink(META.paperUrl, esc(META.paper), "btn quiet") : `<span class="btn quiet">${esc(META.paper)}</span>`);
  if (META.repository) actions.push(extLink(META.repository, "Source ↗", "btn quiet"));
  const n = MAIN.length;
  const mainBody = `<p class="lede">${MAIN.every((m) => DECLS[m.name].kind === "theorem")
    ? `The formalization proves the following ${n > 1 ? `${count(n)} results` : "result"}.`
    : "The main results of the formalization, with the definitions needed to read them."} The <a href="#development">development</a> presents the ${plural(SHOWN.length, "definition and result", "definitions and results")} they rest on, with their proofs.</p>
    ${MAIN.map((m) => envHtml(m.name, "overview")).join("")}`;
  const metric = (href, n, cls, term, text) => `<div class="metric"><span class="metric-n ${cls}">${n}</span><div><a class="metric-k" href="${esc(href)}">${term}</a><p>${text}</p></div></div>`;
  const nChecked = (CMP.config.theorem_names || []).length;
  const ks = CMP.kernels.length;
  const checkedMetric = CMP.state === "accepted" && nChecked
    ? metric("#comparator", nChecked, "ok", "Theorems checked by comparator", `Comparator checked that they state what the challenge states, that their proofs use only the permitted axioms, and that ${ks > 1 ? `${count(ks)} independent kernels accept them` : "the kernel accepts them"}.`)
    : "";
  const basis = `<p>${CHECKED_SENTENCE} A proof checker cannot check the starting points of the proofs: the axioms of the logic, the libraries and the definitions.</p>
    <div class="metrics">
      ${checkedMetric}
      ${metric("#foundations/axioms", ALL_AXIOMS.length, EXTRA_AXIOMS.length ? "bad" : "ok", ALL_AXIOMS.length === 1 ? "Axiom" : "Axioms", axiomsSentence())}
      ${metric("#foundations/libraries", usedLibs.length + 1, "", usedLibs.length ? "Libraries" : "Library", librariesSentence())}
      ${metric("#foundations/definitions", DEF_COUNT, "def", DEF_COUNT === 1 ? "Definition to read" : "Definitions to read", definitionsSentence())}
    </div>`;
  return `<main class="page">
    <header class="hero">
      <p class="kicker">Lean formalization · Lean ${esc(META.lean || "")}</p>
      <h1>${inline(META.title || "")}</h1>
      ${META.subtitle ? `<p class="subtitle">${inline(META.subtitle)}</p>` : ""}
      ${(META.authors || []).length ? `<p class="authors">${esc(listOf(META.authors))}</p>` : ""}
      ${sealHtml()}
      ${statusLine()}
      <div class="actions">${actions.join("")}</div>
    </header>
    <div class="sheet">
      ${CMP.state !== "none" ? row("", "Verdict", verdictHtml()) : ""}
      ${META.abstract ? row("abstract", "Abstract", `<div class="prose abstract">${markdown(META.abstract)}</div>`) : ""}
      ${n ? row("main", n > 1 ? "Main results" : "Main result", mainBody) : ""}
      ${row("basis", "What it rests on", basis)}
    </div>
    ${colophon()}</main>`;
}

/* ------------------------------------------------------------------ foundations */

function libraryEntry(l, tag) {
  const url = l.url || "";
  const meta = [];
  if (l.inputRev) meta.push(esc(l.inputRev));
  if (l.rev) meta.push(esc(l.rev.slice(0, 10)));
  const n = hasChallenge && l.statementModules > 0 ? l.statementModules : l.modules;
  meta.push(hasChallenge && l.statementModules > 0 ? `${plural(n, "module")} imported by the statements` : `${plural(n, "module")} imported`);
  const outside = l.kind !== "reviewed" && l.name !== "mathlib";
  const desc = inline(l.description || (outside ? OUTSIDE_MATHLIB : ""));
  return `<div class="item">
    <div class="item-head"><h3>${esc(l.label)}</h3>${tag}</div>
    <p class="item-meta">${meta.join(" · ")}</p>
    ${desc ? `<p>${desc}</p>` : ""}
    ${l.with && l.with.length ? `<p class="muted">With its dependencies ${listOf(l.with.map(esc))}.</p>` : ""}
    ${url ? `<p class="links">${extLink(url, esc(url.replace(/^https?:\/\//, "")))}</p>` : ""}
  </div>`;
}

function sectionLibraries() {
  const leanModules = hasChallenge ? LEAN_PACKAGE.statementModules : LEAN_PACKAGE.modules;
  const lean = `<div class="item">
    <div class="item-head"><h3>Lean ${esc(META.lean || "")}</h3><span class="tag">Core</span></div>
    <p class="item-meta">${plural(leanModules || 0, "module")} imported${hasChallenge ? " by the statements" : ""}</p>
    <p>The language, its kernel and its core libraries (<code>Init</code>, <code>Std</code>, <code>Lean</code>). The kernel is the small program that checks every proof.</p>
    <p class="links">${extLink("https://lean-lang.org", "lean-lang.org")}</p>
  </div>`;
  const outsideOf = (l) => l.kind !== "reviewed" && l.name !== "mathlib";
  const outside = trustedLibs.filter(outsideOf);
  const unused = LIBRARIES.filter((l) => !l.modules);
  const body = `<p>The statements use definitions of other libraries. Lean checks the proofs of these libraries as it checks those of the project. What remains to trust is that their definitions mean what their names say.${outside.length ? ` The definitions of ${listOf(outside.map(libLabel))} that the statements use are listed under <a href="#foundations/definitions">Definitions</a>.` : ""}</p>
    ${lean}${trustedLibs.map((l) => libraryEntry(l, outsideOf(l) ? `<span class="tag def">Outside Mathlib</span>` : `<span class="tag ok">Reviewed</span>`)).join("")}
    ${replayed && proofLibs.length ? `<p class="subhead">Used only by the proofs</p><p>The challenge of <a href="#comparator">comparator</a> does not import these libraries, and comparator checks every proof again. You do not need to trust them.</p>${proofLibs.map((l) => libraryEntry(l, `<span class="tag ok">Checked by comparator</span>`)).join("")}` : ""}
    ${unused.length ? `<p class="muted">The build also fetches ${listOf(unused.map(libLabel))}, which no file of the formalization imports.</p>` : ""}`;
  return row("libraries", "Libraries", body, "01");
}

function axiomEntry(a) {
  const k = own(AXIOMS, a.name);
  const users = (a.users || []).filter((u) => CARD[u]);
  const usedBy = users.length ? `<p class="muted">Used by ${listOf(users.slice(0, 8).map((u) => `<a href="${esc(routeHref("development", u))}">${inline(labelOf(u))}</a>`))}${users.length > 8 ? ` and ${users.length - 8} more` : ""}.</p>` : "";
  if (!k) {
    // an axiom that Lean does not provide, declared by the author or a library
    const d = DECLS[a.name];
    return `<div class="item">
      <div class="item-head"><h3><code>${esc(display(a.name))}</code></h3><span class="tag bad">Not standard</span></div>
      ${d && d.doc ? `<div class="prose">${markdown(d.doc)}</div>` : ""}
      <p>An axiom ${isProject(a.name) ? "of the project" : `of ${esc((packageOf(a.name) || {}).label || "a library")}`}. Lean assumes it without proof: the results that use it are proved only under this assumption.</p>
      ${d && d.src ? `<pre class="lean"><code>${sourceHtml(a.name)}</code></pre>` : ""}
      ${usedBy}
    </div>`;
  }
  const docs = docsUrl(a.name);
  const extra = own(META.axiomDocs, a.name);
  return `<div class="item">
    <div class="item-head"><h3>${esc(k.title)}</h3><code>${esc(a.name)}</code>${k.extra ? `<span class="tag bad">Not standard</span>` : `<span class="tag ok">Standard</span>`}</div>
    ${k.math ? `<div class="prose ax-stmt">${markdown(k.math)}</div><p>${inline(k.why || "")}</p>` : `<p><strong>${inline(k.plain)}</strong> ${inline(k.why || "")}</p>`}
    ${extra ? `<div class="prose">${markdown(extra)}</div>` : ""}
    ${k.extra ? usedBy : ""}
    <pre class="lean"><code>${highlight(k.lean, null)}</code></pre>
    <p class="links">${docs ? extLink(docs, "Lean documentation") : ""}${extLink(TPIL, "Axioms in Lean (Theorem Proving in Lean 4)")}${k.wiki ? extLink(k.wiki, "Wikipedia") : ""}</p>
  </div>`;
}

function sectionAxioms() {
  const axs = TRUST.axioms.slice().sort((a, b) => {
    const ra = isExtraAxiom(a.name) ? -1 : axiomRank(a.name), rb = isExtraAxiom(b.name) ? -1 : axiomRank(b.name);
    return ra - rb || a.name.localeCompare(b.name);
  });
  // one line, and the axioms in a menu, open when one of them is not standard
  const body = `<p>${axiomsSentence()}</p>
    <details class="more"${EXTRA_AXIOMS.length ? " open" : ""}><summary>The axioms, for the curious</summary>
      <p>The logic of Lean is extended by a few axioms, statements assumed without proof. Lean records the axioms that every result depends on.${!EXTRA_AXIOMS.length && axs.length === 3 ? " These are the three standard axioms of Lean. Together they give classical mathematics, with the excluded middle and the axiom of choice." : ""}</p>
      ${axs.map(axiomEntry).join("")}
    </details>`;
  return row("axioms", "Axioms", body, "02");
}

function definitionEntry(name) {
  const d = DECLS[name];
  if (!d) return "";
  const title = titleOf(name);
  const kind = `<p class="defn-kind"><span class="mark"></span>${esc(own(KIND_KEYWORD, d.kind) || d.kind)}<code>${esc(display(name))}</code></p>`;
  const informal = note("informal", name);
  const links = [];
  // a definition that the development states too: a link to its card there
  if (CARD[name]) links.push(`<a href="${esc(routeHref("development", name))}">${inline(labelOf(name))} in the development</a>`);
  const src = sourceUrl(d);
  if (src) links.push(extLink(src, "Source ↗"));
  const docs = docsUrl(name);
  if (docs) links.push(extLink(docs, "Docs ↗"));
  const wiki = LINKS[name] || LINKS[display(name)];
  if (wiki) links.push(extLink(wiki, "Wikipedia ↗"));
  return `<div class="defn k-def" id="${esc("t:" + name)}">
    ${kind}
    ${title ? `<p class="defn-title">${inline(title)}</p>` : ""}
    ${informal ? `<div class="prose">${markdown(informal)}</div>` : d.doc ? `<div class="prose">${markdown(docParts(d.doc).rest || d.doc)}</div>` : ""}
    <pre class="lean"><code>${sourceHtml(name)}</code></pre>
    ${links.length ? `<p class="links">${links.join("")}</p>` : ""}
  </div>`;
}

function notationEntry(n) {
  const key = n.pattern || "";
  const title = TITLES[key];
  const informal = note("informal", key);
  return `<div class="defn k-def">
    <p class="defn-kind"><span class="mark"></span>notation${key ? `<code>${esc(key)}</code>` : ""}</p>
    ${title ? `<p class="defn-title">${inline(title)}</p>` : ""}
    ${informal ? `<div class="prose">${markdown(informal)}</div>` : n.doc ? `<div class="prose">${markdown(n.doc)}</div>` : ""}
    <pre class="lean"><code>${highlight(n.src, null)}</code></pre>
  </div>`;
}

function sectionDefinitions() {
  const mods = [];
  TRUST.groups.forEach((g) => { if (!mods.includes(g.mod)) mods.push(g.mod); });
  TRUST.notations.forEach((n) => { if (!mods.includes(n.mod)) mods.push(n.mod); });
  const groups = mods.map((m) => {
    const g = TRUST.groups.find((x) => x.mod === m) || { items: [] };
    const ns = TRUST.notations.filter((n) => n.mod === m);
    const pkg = packageOfModule(m);
    return `<p class="module-head"><code>${esc(modulePath(m) || moduleName(m))}</code>${pkg && pkg.kind !== "project" ? ` · ${esc(pkg.label)}` : ""}</p>
      ${ns.map(notationEntry).join("")}${g.items.map(definitionEntry).join("")}`;
  }).join("");
  const body = `<p>A proof checker confirms that a proof is correct. It cannot confirm that a definition captures the intended notion: a wrong definition gives a correct proof of a wrong statement. ${DEF_COUNT ? `The statements rest on the ${plural(DEF_COUNT, "definition")} below${trustedLibs.some((l) => l.kind !== "reviewed" && l.name !== "mathlib") ? ", from the project and from the libraries outside Mathlib" : " of the project"}.` : "The statements use no other definition."}${presentedNote()}</p>
    ${groups}`;
  return row("definitions", "Definitions", body, "03");
}

function pageFoundations() {
  return `<main class="page">
    <header class="pagehead"><p class="kicker">Foundations</p><h1>What the results rest on</h1>
      <p class="lede">${CHECKED_SENTENCE} A proof checker can only confirm that the results follow from their starting points: the libraries that the statements use, the axioms of the logic and the definitions.</p></header>
    <div class="sheet">${sectionLibraries()}${sectionAxioms()}${sectionDefinitions()}</div>
    ${colophon()}</main>`;
}

/* ------------------------------------------------------------------ development */

/* The level of the headings of the text: the highest one is a section. */
const TOP_LEVEL = (function () {
  let top = 6;
  BLOCKS.forEach((b) => {
    if (b.md === undefined) return;
    let fence = false;
    b.md.split("\n").forEach((l) => {
      if (FENCE_RE.test(l)) fence = !fence;
      const m = !fence && HEADING_RE.exec(l);
      if (m) top = Math.min(top, m[1].length);
    });
  });
  return top;
})();

function pageDevelopment() {
  const toc = [];
  const used = {};
  const numbers = [0, 0];
  const two = (k) => String(k).padStart(2, "0");
  const heading = (level, text) => {
    const depth = level - TOP_LEVEL;   // 0: section, 1: subsection, then unnumbered
    let num = "";
    if (depth <= 1 && !/^\d/.test(text)) {
      if (depth === 0) { numbers[0]++; numbers[1] = 0; num = two(numbers[0]); }
      else { numbers[1]++; num = `${two(numbers[0])}.${numbers[1]}`; }
    }
    let id = slug(text);
    if (used[id]) id += "-" + ++used[id]; else used[id] = 1;
    const tag = "h" + Math.min(6, depth + 2);
    if (depth <= 1) toc.push({ level: depth + 2, id, text, num });
    return `<${tag} id="${esc(id)}">${num ? `<span class="secnum">${num}</span>` : ""}${inline(text)}</${tag}>`;
  };
  let body = "";
  const done = new Set();
  BLOCKS.forEach((b) => {
    if (b.md !== undefined) body += `<div class="prose">${markdown(b.md, { heading })}</div>`;
    else if (b.decl && DECLS[b.decl] && !done.has(b.decl)) {
      done.add(b.decl);
      body += envHtml(b.decl, "development");
      toc.push({ level: 0, id: "d:" + b.decl, name: b.decl, text: titleOf(b.decl) || lastPart(display(b.decl)) });
    }
  });
  const cited = Object.keys(CITE_NUM).sort((a, b) => CITE_NUM[a] - CITE_NUM[b]);
  const refs = cited.length ? `<section class="references" id="references"><h2>References</h2><ol>${cited.map((k) => {
    const e = BIB[k];
    const venue = cleanTex(e.journal || e.booktitle || e.publisher || e.school || "");
    const url = e.url || (e.doi ? `https://doi.org/${e.doi}` : "");
    return `<li id="${esc("ref-" + k)}"><span class="key">[${CITE_NUM[k]}]</span><span>${esc(bibAuthors(e.author || e.editor || ""))}. <em>${texHtml(e.title || "")}</em>.${venue ? " " + esc(venue) + "," : ""} ${esc(e.year || "")}.${url ? " " + extLink(url, url.startsWith("https://doi.org/") ? "doi" : "link") : ""}</span></li>`;
  }).join("")}</ol></section>` : "";
  if (cited.length) toc.push({ level: 2, id: "references", text: "References", num: "" });
  // the entries of the table of contents are links: their own links are removed
  const plain = (t) => inline(t).replace(/<a\b[^>]*>|<\/a>/g, "");
  const tocHtml = `<nav class="toc" aria-label="Contents"><button class="toc-toggle" type="button" aria-expanded="false">Contents</button><p class="toc-title">Contents</p><ol>${toc.map((t) =>
    t.level === 0
      ? `<li class="res ${kindClass(t.name)}"><a href="${esc(routeHref("development", t.name))}" data-target="${esc(t.id)}"><span class="mark"></span><span>${plain(labelOf(t.name))}${t.text ? ` · ${plain(t.text)}` : ""}</span></a></li>`
      : `<li class="l${t.level}"><a href="${esc(routeHref("development", t.id))}" data-target="${esc(t.id)}">${t.num ? `<span class="num">${t.num}</span>` : ""}<span>${plain(t.text)}</span></a></li>`).join("")}</ol></nav>`;
  return `<main class="page"><div class="dev">
    <header class="pagehead dev-head"><p class="kicker">Development · ${plural(SHOWN.length, "declaration")}${CMP.state === "accepted" ? ` · <a class="ok" href="#comparator">✓ Checked by comparator</a>` : ""}</p><h1>${inline(META.title || "")}</h1>
      ${(META.authors || []).length ? `<p class="lede">${esc(listOf(META.authors))}</p>` : ""}</header>
    ${tocHtml}<article class="paper">${body}${refs}</article>
  </div>${colophon()}</main>`;
}

/* ------------------------------------------------------------------ comparator */

function pageComparator() {
  const cfg = CMP.config || {};
  const n = (cfg.theorem_names || []).length;
  const kernels = CMP.kernels.length ? CMP.kernels : Object.keys(CHECKERS);
  const rep = ((D.comparator || {}).report || {}).report || {};
  const status = CMP.state === "none"
    ? `<p>No report of comparator comes with this page: comparator has not checked this formalization. Anyone can run it on the source.</p>`
    : verdictHtml(true) + (CMP.state === "rejected" ? CMP.failedSteps.map((st) =>
      `<p>${codeName(st.key)}: ${esc(st.judgement)}</p>${st.message ? `<pre class="code"><code>${esc(st.message)}</code></pre>` : ""}`).join("") : "") +
      (CMP.sandboxed ? "" : `<p>This run did not use the sandbox of comparator, which does not exist on macOS. The sandbox keeps a malicious proof from tampering with the check. Without it, the verdict assumes that the source is not malicious.</p>`);
  const steps = `<ol class="steps">
      <li><span><b>The challenge</b> is a copy of the file of the results where every proof is replaced by <code>sorry</code>. Its definitions and statements are those that a reader checks.</span></li>
      <li><span><b>The solution</b> is the file with its proofs, built in a sandbox so that it cannot tamper with the check.</span></li>
      <li><span>Comparator checks that the ${n ? n + " " : ""}theorems of the solution state exactly the theorems of the challenge.</span></li>
      <li><span>It checks that their proofs use no axiom outside ${(cfg.permitted_axioms || []).length ? listOf(cfg.permitted_axioms.map(codeName)) : "the permitted ones"}.</span></li>
      <li><span>It checks every proof again in each of the kernels below.</span></li>
    </ol>`;
  const table = `<div class="table-wrap"><table class="rules"><thead><tr><th>Kernel</th><th>Verdict</th><th>What it is</th></tr></thead><tbody>
      ${kernels.map((k) => {
        const info = own(CHECKERS, k) || ["", []];
        const res = own(rep.kernel_reports, k);
        return `<tr><td>${esc(k)}</td><td>${res ? `<span class="tag ${res.judgement === "success" ? "ok" : "bad"}">${esc(res.judgement)}</span>` : "—"}</td><td>${inline(info[0])} ${info[1].map(([t, u]) => extLink(u, esc(t))).join(" ")}</td></tr>`;
      }).join("")}
    </tbody></table></div>`;
  return `<main class="page">
    <header class="pagehead"><p class="kicker">Verification</p><h1>Comparator</h1>
      ${sealHtml()}
      <p class="lede">Lean checks every proof when the project is built. ${extLink("https://github.com/leanprover/comparator", "Comparator")} checks it a second time, independently. It guards against a proof that changes the statement it claims to prove, that uses an unexpected axiom, or that exploits a bug of a checker.</p></header>
    <div class="sheet">
      ${row("", "Verdict", status)}
      ${row("", "What it checks", steps, "01")}
      ${row("", "The kernels", table, "02")}
      ${row("", "What it does not check", `<p>Comparator cannot tell whether a statement means what its author intends. This is why the <a href="#foundations/definitions">definitions</a> and the statements are shown: they are the part that a human reads.</p>`, "03")}
      ${row("", "Running it", `<p>From a clone of the source, on Linux with <code>bubblewrap</code> installed:</p><pre class="code"><code>lake comparator --paranoid</code></pre><p>On macOS, where <code>bubblewrap</code> does not exist, add <code>--inadvisably-no-sandbox</code>.</p>`, "04")}
    </div>
    ${colophon()}</main>`;
}
