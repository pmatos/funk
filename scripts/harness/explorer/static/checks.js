import { $, el } from "./dom.js";
import { lineOf } from "./editor.js";

const NODES = [
  ["rust", "Rust verifier"],
  ["lean", "Lean validator"],
  ["round", "Round trip"],
  ["asm", "x86-64"],
  ["native", "Native run"],
];
const GLYPH = { ok: "✓", bad: "✕", warn: "!", idle: "–" };

const SAYS = {
  accepted: "accepts this module",
  "parse-error": "reports a parse error",
  "validation-error": "reports a validation error",
  "io-error": "could not read the module",
  "tool-error": "did not give a report",
};

export class Chain {
  constructor() {
    this.items = new Map();
    const list = $("chain");
    for (const [id, name] of NODES) {
      const state = el("span", { class: "state" });
      const glyph = el("span", { class: "glyph", ariaHidden: "true" });
      const item = el("li", { class: "idle" }, glyph, el("b", {}, name), state);
      this.items.set(id, { item, glyph, state });
      list.append(item);
    }
  }

  set(id, kind, words) {
    const { item, glyph, state } = this.items.get(id);
    item.className = kind;
    glyph.textContent = GLYPH[kind];
    state.textContent = words;
  }
}

function diagnostic(d, lines, goto) {
  const line = lineOf(lines, d);
  if (line === null) return el("li", {}, d.message);
  return el(
    "li",
    {},
    el("button", { class: "link", type: "button", onclick: () => goto(line, d.column ?? 1) }, `Line ${line}: ${d.message}`),
  );
}

function tool(name, report, lines, goto) {
  const said = SAYS[report.verdict] ?? report.verdict;
  const parts = [el("p", { class: `verdict v-${report.verdict}` }, `${name} ${said}.`)];
  if (report.message) parts.push(el("p", { class: "note" }, report.message));
  if (report.diagnostics.length) {
    parts.push(el("ul", { class: "diags" }, ...report.diagnostics.map((d) => diagnostic(d, lines, goto))));
  }
  return parts;
}

function roundTrip(r) {
  const words = {
    same: "Lean reprints Rust's text byte for byte.",
    differs: "Lean's text differs from Rust's.",
    rejected: `Lean cannot reprint Rust's text: ${r.why}`,
    skipped: `No round trip: ${r.why}.`,
  };
  const parts = [el("p", { class: `verdict r-${r.status}` }, words[r.status])];
  if (r.status === "differs") {
    parts.push(el("pre", { class: "dump" }, `Rust\n${r.rust}\nLean\n${r.lean}`));
  }
  return parts;
}

export function renderChecks(a, lines, goto) {
  const notes = [];
  if (a.format.verdict === "accepted") {
    notes.push(
      el("p", { class: "note" }, a.format.canonical ? "The text is canonical." : "The text is not canonical. Format rewrites it."),
    );
  }
  $("checks").replaceChildren(
    ...tool("Rust", a.rust, lines, goto),
    ...tool("Lean", a.lean, lines, goto),
    ...roundTrip(a.roundTrip),
    ...notes,
  );
}

export function updateChain(chain, a) {
  const verdicts = { accepted: ["ok", "accepts"], "tool-error": ["warn", "no report"] };
  const accepts = (r) => verdicts[r.verdict] ?? ["bad", "rejects"];
  chain.set("rust", ...accepts(a.rust));
  chain.set("lean", ...accepts(a.lean));
  const round = {
    same: ["ok", "same bytes"],
    differs: ["bad", "bytes differ"],
    rejected: ["bad", "not reprinted"],
    skipped: ["idle", "not run"],
  };
  chain.set("round", ...round[a.roundTrip.status]);
  const asm = {
    accepted: ["ok", "lowered"],
    unsupported: ["warn", "cannot lower"],
    skipped: ["idle", "not run"],
  };
  chain.set("asm", ...(asm[a.assembly.verdict] ?? ["bad", "failed"]));
}

export function diagnosticMarks(a, lines) {
  const marks = new Map();
  const add = (report, kind) => {
    for (const d of report.diagnostics ?? []) {
      const line = lineOf(lines, d);
      if (line !== null) marks.set(line, kind);
    }
  };
  add(a.assembly, "warn");
  add(a.rust, "bad");
  add(a.lean, "bad");
  return marks;
}

export function assemblyMessage(a) {
  if (a.assembly.verdict === "skipped") return "Fix the module to see its assembly.";
  const first = a.assembly.diagnostics?.[0]?.message;
  if (a.assembly.verdict === "unsupported") return `The backend cannot lower this module. ${first}`;
  return a.assembly.message ?? first ?? "The backend gave no assembly.";
}
