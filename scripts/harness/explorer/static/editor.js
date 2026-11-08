import { $, el } from "./dom.js";
import { firLine } from "./highlight.js";

const SYMBOL_OF_FUNC = /^func (@"(?:[^"\\]|\\.)*"|@[^\s(]+)\(/;

/** Finds the line (from 1) that a diagnostic points at, or null. */
export function lineOf(lines, d) {
  if (Number.isInteger(d.line)) return d.line;
  if (typeof d.func !== "string") return null;
  const heads = [`func @${d.func}(`, `func @"${d.func}"(`];
  const start = lines.findIndex((l) => heads.some((h) => l.startsWith(h)));
  if (start < 0) return null;
  if (typeof d.block !== "string") return start + 1;
  const head = `^${d.block}`;
  for (let i = start + 1; i < lines.length && lines[i] !== "}"; i++) {
    if (lines[i] !== head && !lines[i].startsWith(`${head}(`) && !lines[i].startsWith(`${head}:`)) {
      continue;
    }
    if (!Number.isInteger(d.op)) return i + 1;
    let seen = -1;
    for (let j = i + 1; j < lines.length && lines[j] !== "}"; j++) {
      if (lines[j].trim() !== "" && ++seen === d.op) return j + 1;
    }
    return i + 1;
  }
  return start + 1;
}

/** Which op a line of canonical text holds, for finding its assembly. */
export function opAt(lines, index) {
  const text = lines[index]?.trim();
  if (!text || text.startsWith("^") || text.startsWith("func ") || text === "}") return null;
  for (let i = index; i >= 0; i--) {
    const head = SYMBOL_OF_FUNC.exec(lines[i]);
    if (!head) continue;
    let nth = 0;
    for (let j = i + 1; j < index; j++) if (lines[j].trim() === text) nth++;
    return { func: head[1], text, nth };
  }
  return null;
}

export function lineOfOp(lines, op) {
  const start = lines.findIndex((l) => SYMBOL_OF_FUNC.exec(l)?.[1] === op.func);
  if (start < 0) return null;
  let nth = 0;
  for (let i = start + 1; i < lines.length && lines[i] !== "}"; i++) {
    if (lines[i].trim() === op.text && nth++ === op.nth) return i + 1;
  }
  return null;
}

export class Editor {
  constructor({ onChange, onCaret, onRun }) {
    this.source = $("source");
    this.shadow = $("shadow");
    this.gutter = $("gutter");
    this.marks = new Map();
    this.focusLine = null;
    this.released = false;
    this.source.addEventListener("input", () => {
      this.paint();
      onChange();
    });
    this.source.addEventListener("scroll", () => this.sync());
    for (const event of ["keyup", "click"]) {
      this.source.addEventListener(event, () => onCaret(this.caretLine()));
    }
    this.source.addEventListener("keydown", (e) => this.key(e, onChange, onRun));
  }

  key(e, onChange, onRun) {
    if ((e.ctrlKey || e.metaKey) && e.key === "Enter") {
      e.preventDefault();
      onRun();
    } else if (e.key === "Escape") {
      this.released = true;
    } else if (e.key === "Tab" && !this.released && !e.shiftKey) {
      e.preventDefault();
      this.source.setRangeText("  ", this.source.selectionStart, this.source.selectionEnd, "end");
      this.paint();
      onChange();
    } else if (e.key !== "Shift") {
      this.released = false;
    }
  }

  get text() {
    return this.source.value;
  }

  get lines() {
    return this.source.value.split("\n");
  }

  set(text) {
    this.source.value = text;
    this.marks = new Map();
    this.focusLine = null;
    this.paint();
    this.source.scrollTop = 0;
  }

  caretLine() {
    return this.source.value.slice(0, this.source.selectionStart).split("\n").length - 1;
  }

  mark(marks) {
    this.marks = marks;
    this.paint();
  }

  showLine(line) {
    this.focusLine = line;
    this.paint();
    const height = parseFloat(getComputedStyle(this.source).lineHeight);
    const top = (line - 1) * height;
    const view = this.source.clientHeight;
    if (top < this.source.scrollTop || top > this.source.scrollTop + view - height) {
      this.source.scrollTop = Math.max(0, top - view / 3);
    }
    this.sync();
  }

  goto(line, column = 1) {
    const lines = this.lines;
    let at = 0;
    for (let i = 0; i < Math.min(line - 1, lines.length); i++) at += lines[i].length + 1;
    at += Math.max(0, column - 1);
    this.source.focus({ preventScroll: true });
    this.source.setSelectionRange(at, at);
    this.showLine(line);
  }

  classes(line) {
    const parts = [];
    if (this.marks.has(line)) parts.push(`mark-${this.marks.get(line)}`);
    if (this.focusLine === line) parts.push("focus");
    return parts.join(" ");
  }

  paint() {
    const lines = this.lines;
    const gutter = [];
    const shadow = [];
    lines.forEach((text, i) => {
      const cls = this.classes(i + 1);
      gutter.push(el("div", { class: cls }, String(i + 1)));
      shadow.push(el("div", { class: `line ${cls}` }, ...firLine(text), "\n"));
    });
    this.gutter.replaceChildren(...gutter);
    this.shadow.replaceChildren(...shadow);
    this.sync();
  }

  sync() {
    this.shadow.scrollTop = this.source.scrollTop;
    this.shadow.scrollLeft = this.source.scrollLeft;
    this.gutter.scrollTop = this.source.scrollTop;
  }
}
