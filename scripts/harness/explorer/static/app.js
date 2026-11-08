import { $, el, get, post } from "./dom.js";
import { Assembly } from "./assembly.js";
import { Chain, assemblyMessage, diagnosticMarks, renderChecks, updateChain } from "./checks.js";
import { Editor, lineOfOp, opAt } from "./editor.js";
import { HEADLINE, Runner } from "./run.js";

const DEBOUNCE = 300;
const FIRST = ["canonical", "freeze-i8"];

const chain = new Chain();
const alarms = new Map();
let analysis = null;
let timer = null;
let busy = false;
let again = false;

const editor = new Editor({
  onChange: edited,
  onCaret: (index) => assembly.select(opAt(editor.lines, index)),
  onRun: () => runner.run(),
});
const assembly = new Assembly({
  onOp: (op) => {
    const line = lineOfOp(editor.lines, op);
    if (line !== null) editor.goto(line);
    assembly.select(op);
  },
});
const runner = new Runner({
  text: () => editor.text,
  onNative: showNative,
  onError: (e) => alarm("server", e.message),
});

function alarm(key, text) {
  if (text) alarms.set(key, text);
  else alarms.delete(key);
  const box = $("alarm");
  box.replaceChildren(...[...alarms.values()].map((t) => el("p", {}, t)));
  box.hidden = alarms.size === 0;
}

function showNative(c) {
  if (c === null) {
    chain.set("native", "idle", "running");
    alarm("native", null);
    return;
  }
  const kinds = {
    passed: ["ok", "refines"],
    failed: ["bad", "does not refine"],
    invalid: ["warn", "cannot judge"],
    unavailable: ["idle", "not run"],
  };
  chain.set("native", ...(kinds[c.status] ?? ["warn", c.status]));
  alarm("native", c.status === "failed" ? `${HEADLINE.failed} ${c.detail}` : null);
}

function edited() {
  analysis = null;
  $("format").disabled = true;
  runner.clear();
  chain.set("native", "idle", "press Run");
  alarm("native", null);
  clearTimeout(timer);
  timer = setTimeout(analyze, DEBOUNCE);
}

function validatorAlarm({ agree, why }) {
  if (agree === false) return `Rust and Lean disagree. ${why}.`;
  if (agree === null) return `A validator failed. ${why}.`;
  return null;
}

function show(a) {
  analysis = a;
  const lines = editor.lines;
  renderChecks(a, lines, (line, column) => editor.goto(line, column));
  updateChain(chain, a);
  editor.mark(diagnosticMarks(a, lines));
  if (a.assembly.verdict === "accepted") assembly.show(a.assembly.text);
  else assembly.message(assemblyMessage(a));
  $("format").disabled = !(a.format.verdict === "accepted" && !a.format.canonical);
  runner.setFunctions(a.format.verdict === "accepted" ? a.functions : runner.functions, a.rust.verdict === "accepted" && a.lean.verdict === "accepted");
  alarm("disagree", validatorAlarm(a.agreement));
  alarm("round", a.roundTrip.status === "differs" ? "Lean does not reprint Rust's text byte for byte." : null);
}

async function analyze() {
  if (busy) {
    again = true;
    return;
  }
  busy = true;
  const text = editor.text;
  try {
    const a = await post("/api/analyze", { text });
    alarm("server", null);
    if (text === editor.text) show(a);
  } catch (e) {
    alarm("server", `The explorer could not check this module. ${e.message}`);
  } finally {
    busy = false;
    if (again) {
      again = false;
      void analyze();
    }
  }
}

async function load(group, name) {
  const example = await get(`/api/example?group=${encodeURIComponent(group)}&name=${encodeURIComponent(name)}`);
  editor.set(example.text);
  runner.setSaved(example.runs);
  edited();
  clearTimeout(timer);
  await analyze();
}

async function start() {
  for (const id of ["rust", "lean", "round", "asm"]) chain.set(id, "idle", "checking");
  chain.set("native", "idle", "press Run");
  const groups = await get("/api/examples");
  const select = $("example");
  const titles = { canonical: "Corpus", llvm: "Ported from LLVM" };
  for (const [group, names] of Object.entries(groups)) {
    select.append(
      el("optgroup", { label: titles[group] ?? group }, ...names.map((n) => el("option", { value: `${group}/${n}` }, n))),
    );
  }
  select.addEventListener("change", () => {
    const [group, name] = select.value.split("/");
    load(group, name).catch((e) => alarm("server", `The explorer could not load this example. ${e.message}`));
  });
  $("format").addEventListener("click", () => {
    if (analysis?.format?.text) {
      editor.set(analysis.format.text);
      edited();
    }
  });
  const [group, name] = FIRST;
  if (groups[group]?.includes(name)) {
    select.value = `${group}/${name}`;
    await load(group, name);
  } else {
    await analyze();
  }
}

try {
  await start();
} catch (e) {
  alarm("server", `The explorer could not start. ${e.message}`);
}
