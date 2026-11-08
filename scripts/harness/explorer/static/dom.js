export function el(tag, props = {}, ...children) {
  const node = document.createElement(tag);
  for (const [key, value] of Object.entries(props)) {
    if (key === "class") node.className = value;
    else if (key.startsWith("on")) node.addEventListener(key.slice(2), value);
    else node[key] = value;
  }
  node.append(...children.filter((c) => c !== null && c !== undefined));
  return node;
}

export const $ = (id) => document.getElementById(id);

async function request(path, init) {
  const response = await fetch(path, init);
  const value = await response.json();
  if (!response.ok) throw new Error(value.error);
  return value;
}

export const get = (path) => request(path);

export const post = (path, body) =>
  request(path, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
