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
  const body = text.trimStart();
  const indent = text.slice(0, text.length - body.length);
  const space = body.search(/\s/);
  const word = space < 0 ? body : body.slice(0, space);
  const rest = body.slice(word.length);
  if (indent === "" && word.endsWith(":")) return [el("span", { class: "t-label" }, word), rest];
  if (!/^\.?[a-z]/.test(word)) return [text];
  return [indent, el("span", { class: word.startsWith(".") ? "t-directive" : "t-word" }, word), rest];
}
