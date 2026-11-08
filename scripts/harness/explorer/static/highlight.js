import { el } from "./dom.js";

const SYMBOL = String.raw`@"(?:[^"\\]|\\.)*"|@[^\s(),:]+`;
const TOKEN = new RegExp(
  String.raw`(?<string>"(?:[^"\\]|\\.)*")|(?<comment>//.*$)|(?<symbol>${SYMBOL})|(?<value>%[^\s(),:]+)|` +
    String.raw`(?<label>\^[^\s(),:]+)|(?<type>\bi[1-9][0-9]*\b|\bptr\b)|` +
    String.raw`(?<constant>\btrue\b|\bfalse\b|\bpoison\b|-?\b[0-9]+\b)|(?<word>[A-Za-z_][\w.]*)`,
  "g",
);

export function firLine(text) {
  const parts = [];
  let at = 0;
  for (const match of text.matchAll(TOKEN)) {
    if (match.index > at) parts.push(text.slice(at, match.index));
    const kind = Object.keys(match.groups).find((k) => match.groups[k] !== undefined);
    parts.push(el("span", { class: `t-${kind}` }, match[0]));
    at = match.index + match[0].length;
  }
  if (at < text.length) parts.push(text.slice(at));
  return parts;
}

export function asmLine(text) {
  const label = /^(\.?[\w$.]+):(.*)$/.exec(text);
  if (label) return [el("span", { class: "t-label" }, `${label[1]}:`), label[2]];
  const op = /^(\s*)(\.?[a-z][\w.]*)(.*)$/.exec(text);
  if (!op) return [text];
  const directive = op[2].startsWith(".");
  return [op[1], el("span", { class: directive ? "t-directive" : "t-word" }, op[2]), op[3]];
}
