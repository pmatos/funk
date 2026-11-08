import { $, el, post } from "./dom.js";

const MODES = { exhaustive: "bits-field", scripted: "choices-field", seed: "seed-field" };

function outcomeRow(o) {
  const body = [];
  if (o.kind === "return") {
    body.push("returns ");
    if (o.values.length === 0) body.push("nothing");
    o.values.forEach((v, i) => {
      if (i) body.push(", ");
      body.push(el("code", { class: v === "poison" ? "poison" : "" }, v));
    });
  } else {
    body.push(o.shown);
  }
  return el("li", { class: `o-${o.kind}` }, ...body);
}

function count(n, thing) {
  return `${n} ${thing}${n === 1 ? "" : "s"}`;
}

function reference(r) {
  const title = el("h3", {}, "On fir-ref");
  if (r.kind === "error") return [title, el("p", { class: "verdict v-parse-error" }, r.message)];
  if (r.kind === "budget") {
    return [
      title,
      el("p", { class: "verdict r-rejected" }, `A path chooses more than ${count(r.budget, "bit")}, so the outcome set was not computed.`),
      el("p", { class: "note" }, "Raise the bits, or follow one path with a seed."),
    ];
  }
  if (r.kind === "outcomes") {
    const made = r.choices === 0 ? "no choices" : `at most ${count(r.choices, "choice")} on a path`;
    return [
      title,
      el("p", { class: "note" }, `${count(r.outcomes.length, "outcome")}, with ${made}.`),
      el("ul", { class: "outcomes" }, ...r.outcomes.map(outcomeRow)),
    ];
  }
  const parts = [title, el("ul", { class: "outcomes" }, outcomeRow(r.outcome))];
  const drew = r.sequence ? `: ${r.sequence.join(", ")}` : "";
  parts.push(el("p", { class: "note" }, `This path made ${count(r.choices, "choice")}${drew}.`));
  return parts;
}

const HEADLINE = {
  passed: "Native code refines fir-ref.",
  failed: "Native code does not refine fir-ref.",
  invalid: "This run cannot be judged.",
  unavailable: "Native code did not run.",
};

function native(c) {
  const parts = [
    el("h3", {}, "As native code"),
    el("p", { class: `verdict j-${c.status}` }, HEADLINE[c.status] ?? c.status),
  ];
  if (c.native.length) {
    parts.push(
      el(
        "ul",
        { class: "outcomes" },
        ...c.native.map((n) =>
          el(
            "li",
            { class: n.result.error ? "o-ub" : "o-return" },
            el("code", {}, n.args.join(" ") || "no arguments"),
            n.result.error ? `: ${n.result.error}` : `: returns ${n.result.values.join(", ") || "nothing"}`,
          ),
        ),
      ),
    );
  }
  parts.push(el("p", { class: "note" }, c.detail));
  return parts;
}

export class Runner {
  constructor({ text, onNative, onError }) {
    this.text = text;
    this.onNative = onNative;
    this.onError = onError;
    this.functions = [];
    this.saved = [];
    this.results = $("results");
    this.running = false;
    this.ready = false;
    $("run").addEventListener("submit", (e) => {
      e.preventDefault();
      this.run();
    });
    $("mode").addEventListener("change", () => this.showMode());
    $("func").addEventListener("change", () => this.inputs());
    $("saved").addEventListener("change", () => this.applySaved());
    this.showMode();
  }

  showMode() {
    const mode = $("mode").value;
    for (const [name, id] of Object.entries(MODES)) $(id).hidden = name !== mode;
  }

  inputs(values = []) {
    const fn = this.functions.find((f) => f.name === $("func").value);
    const wrap = $("args");
    if (!fn) {
      wrap.replaceChildren();
      return;
    }
    wrap.replaceChildren(
      ...fn.params.map((type, i) =>
        el(
          "label",
          { class: "field" },
          `Argument ${i + 1}, ${type}`,
          el("input", { type: "text", spellcheck: false, autocomplete: "off", value: values[i] ?? "0", className: "arg" }),
        ),
      ),
    );
  }

  setFunctions(functions, canRun) {
    const before = $("func").value;
    const same =
      functions.length === this.functions.length &&
      functions.every((f, i) => f.name === this.functions[i].name && f.params.join() === this.functions[i].params.join());
    this.functions = functions;
    this.ready = canRun && functions.length > 0;
    $("go").disabled = !this.ready || this.running;
    if (same) return;
    $("func").replaceChildren(...functions.map((f) => el("option", { value: f.name }, f.name)));
    if (functions.some((f) => f.name === before)) $("func").value = before;
    this.inputs();
  }

  setSaved(runs) {
    this.saved = runs;
    $("saved").replaceChildren(
      el("option", { value: "" }, runs.length ? "Choose a saved run" : "This example has none"),
      ...runs.map((r, i) => el("option", { value: String(i) }, `${r.func}(${r.args.join(", ")})`)),
    );
    $("saved").disabled = runs.length === 0;
  }

  applySaved() {
    const run = this.saved[Number($("saved").value)];
    if ($("saved").value === "" || !run) return;
    $("func").value = run.func;
    this.inputs(run.args);
    if (run.fuel !== null && run.fuel !== undefined) $("fuel").value = run.fuel;
    if (run.choices) {
      $("mode").value = "scripted";
      $("choices").value = run.choices.join(",");
      this.showMode();
    }
  }

  clear() {
    this.results.replaceChildren();
  }

  request() {
    const req = {
      text: this.text(),
      func: $("func").value,
      args: [...document.querySelectorAll("#args .arg")].map((i) => i.value.trim()),
      fuel: Number($("fuel").value),
      mode: $("mode").value,
    };
    if (req.mode === "exhaustive") req.bits = Number($("bits").value);
    if (req.mode === "scripted") {
      const typed = $("choices").value.trim();
      req.choices = typed === "" ? [] : typed.split(",").map((c) => c.trim());
    }
    if (req.mode === "seed") req.seed = Number($("seed").value);
    return req;
  }

  async run() {
    if (!this.ready || this.running) return;
    this.running = true;
    $("go").disabled = true;
    const text = this.text();
    this.results.replaceChildren(el("p", { class: "note" }, "Running"));
    this.onNative(null);
    try {
      const req = this.request();
      const ref = await post("/api/run", req);
      this.results.replaceChildren(...reference(ref));
      const compared = await post("/api/compare", req);
      if (text === this.text()) {
        this.results.append(...native(compared));
        this.onNative(compared);
      }
    } catch (e) {
      this.results.replaceChildren(el("p", { class: "verdict v-parse-error" }, e.message));
      this.onError(e);
    } finally {
      this.running = false;
      $("go").disabled = !this.ready;
    }
  }
}
