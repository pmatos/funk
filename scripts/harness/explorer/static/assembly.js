import { $, el } from "./dom.js";
import { asmLine } from "./highlight.js";

/** Splits the backend's text into lines, tying each to the op whose comment
 *  comes before it. The backend writes one comment per op. */
export function parse(text) {
  const out = [];
  const seen = new Map();
  let func = null;
  let op = null;
  for (const line of text.replace(/\n$/, "").split("\n")) {
    const comment = /^\s*# (.*)$/.exec(line);
    if (comment && comment[1].startsWith("@")) {
      func = comment[1];
      op = null;
    } else if (comment) {
      const key = `${func}\n${comment[1]}`;
      const nth = seen.get(key) ?? 0;
      seen.set(key, nth + 1);
      op = { func, text: comment[1], nth };
    } else if (/^\S.*:/.test(line) || /^\s*\.size/.test(line)) {
      op = null;
    }
    out.push({ line, comment: comment?.[1] ?? null, op });
  }
  return out;
}

const same = (a, b) => a && b && a.func === b.func && a.text === b.text && a.nth === b.nth;

export class Assembly {
  constructor({ onOp }) {
    this.root = $("asm");
    this.rows = [];
    this.root.addEventListener("click", (e) => {
      const row = e.target.closest("[data-index]");
      if (row) {
        const op = this.rows[Number(row.dataset.index)].op;
        if (op) onOp(op);
      }
    });
  }

  message(text) {
    this.rows = [];
    this.root.replaceChildren(el("p", { class: "empty" }, text));
  }

  show(text) {
    this.rows = parse(text);
    this.root.replaceChildren(
      ...this.rows.map((row, i) =>
        el(
          "div",
          { class: `asm-line${row.comment !== null ? " asm-op" : ""}${row.op ? " linked" : ""}` },
          ...(row.comment !== null ? [row.line] : asmLine(row.line)),
          "\n",
        ),
      ),
    );
    [...this.root.children].forEach((node, i) => {
      node.dataset.index = i;
    });
  }

  select(op) {
    let first = null;
    [...this.root.children].forEach((node, i) => {
      const on = same(this.rows[i]?.op, op);
      node.classList.toggle("selected", Boolean(on));
      if (on && !first) first = node;
    });
    if (first) first.scrollIntoView({ block: "nearest" });
  }
}
