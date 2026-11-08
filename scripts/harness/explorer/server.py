"""The explorer's HTTP server.

It answers one request at a time: the harness's native runs use
`preexec_fn`, which is not safe with threads. It compiles and runs what it
is sent, so it binds to the loopback address and checks that each request
comes from its own page. A web page elsewhere could otherwise post to it.
"""

import json
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlsplit

from . import examples

LOOPBACK = "127.0.0.1"
MOST_BODY = 1 << 20
MOST_FUEL = 1 << 40
MOST_BITS = 64
MOST_ARGS = 4096
STATIC = Path(__file__).parent / "static"
TYPES = {
    ".html": "text/html; charset=utf-8",
    ".css": "text/css; charset=utf-8",
    ".js": "text/javascript; charset=utf-8",
}
HEADERS = {
    "Content-Security-Policy": "default-src 'self'; frame-ancestors 'none'",
    "X-Content-Type-Options": "nosniff",
    "Referrer-Policy": "no-referrer",
    "Cache-Control": "no-store",
}


class BadRequest(Exception):
    pass


def _strings(value, what: str) -> list[str]:
    if (
        not isinstance(value, list)
        or len(value) > MOST_ARGS
        or not all(isinstance(v, str) and "\0" not in v for v in value)
    ):
        raise BadRequest(f"{what} must be a list of strings")
    return value


def _count(value, what: str, limit: int) -> int:
    if type(value) is not int or not 0 <= value <= limit:
        raise BadRequest(f"{what} must be a whole number from 0 to {limit}")
    return value


def module_text(body: dict) -> str:
    text = body.get("text")
    if not isinstance(text, str):
        raise BadRequest("text must be a string")
    try:
        text.encode("utf-8")
    except UnicodeEncodeError as e:
        raise BadRequest("text is not valid Unicode") from e
    return text


def call(body: dict) -> dict:
    """The function and arguments of a run."""
    func = body.get("func")
    if not isinstance(func, str) or not func.startswith("@") or "\0" in func:
        raise BadRequest("func must name a function, starting with @")
    return {
        "func": func,
        "args": _strings(body.get("args", []), "args"),
        "fuel": _count(body.get("fuel", 1_000_000), "fuel", MOST_FUEL),
    }


def run_request(body: dict) -> dict:
    req = call(body)
    mode = body.get("mode", "exhaustive")
    if mode not in ("exhaustive", "scripted", "seed"):
        raise BadRequest("mode must be exhaustive, scripted or seed")
    req["mode"] = mode
    if mode == "scripted":
        req["choices"] = _strings(body.get("choices", []), "choices")
    if mode == "seed":
        req["seed"] = _count(body.get("seed"), "seed", (1 << 64) - 1)
    if mode == "exhaustive":
        bits = body.get("bits")
        req["bits"] = None if bits is None else _count(bits, "bits", MOST_BITS)
    return req


class Explorer(HTTPServer):
    def __init__(self, port: int, toolchain, corpus_root: Path):
        super().__init__((LOOPBACK, port), Handler)
        self.toolchain = toolchain
        self.corpus_root = corpus_root
        self.files = {
            p.name: p for p in STATIC.iterdir() if p.suffix in TYPES and p.is_file()
        }

    def hosts(self) -> set[str]:
        port = self.server_address[1]
        return {f"{LOOPBACK}:{port}", f"localhost:{port}"}


class Handler(BaseHTTPRequestHandler):
    server_version = "fir-explorer"
    sys_version = ""

    def log_message(self, format, *args):
        pass

    def _send(self, status: HTTPStatus, kind: str, data: bytes):
        self.send_response(status)
        self.send_header("Content-Type", kind)
        self.send_header("Content-Length", str(len(data)))
        for name, value in HEADERS.items():
            self.send_header(name, value)
        self.end_headers()
        self.wfile.write(data)

    def _json(self, value, status: HTTPStatus = HTTPStatus.OK):
        self._send(status, "application/json", json.dumps(value).encode("utf-8"))

    def _refuse(self, status: HTTPStatus, why: str):
        self._json({"error": why}, status)

    def _from_this_machine(self) -> bool:
        if self.headers.get("Host") in self.server.hosts():
            return True
        self._refuse(HTTPStatus.FORBIDDEN, "this request names another host")
        return False

    def do_GET(self):
        if not self._from_this_machine():
            return
        url = urlsplit(self.path)
        if url.path == "/favicon.ico":
            self._send(HTTPStatus.NO_CONTENT, "image/x-icon", b"")
        elif url.path == "/api/examples":
            self._json(examples.catalogue(self.server.corpus_root))
        elif url.path == "/api/example":
            q = parse_qs(url.query)
            found = examples.example(
                self.server.corpus_root,
                q.get("group", [""])[0],
                q.get("name", [""])[0],
            )
            if found is None:
                self._refuse(HTTPStatus.NOT_FOUND, "no such example")
            else:
                self._json(found)
        else:
            self._static(url.path)

    def _static(self, path: str):
        name = "index.html" if path == "/" else path.removeprefix("/")
        file = self.server.files.get(name)
        if file is None:
            self._refuse(HTTPStatus.NOT_FOUND, "no such page")
            return
        self._send(HTTPStatus.OK, TYPES[file.suffix], file.read_bytes())

    def _body(self) -> dict | None:
        origin = {f"http://{h}" for h in self.server.hosts()}
        if self.headers.get("Origin") not in origin:
            self._refuse(HTTPStatus.FORBIDDEN, "this request comes from another page")
            return None
        if self.headers.get_content_type() != "application/json":
            self._refuse(HTTPStatus.UNSUPPORTED_MEDIA_TYPE, "send application/json")
            return None
        try:
            length = int(self.headers.get("Content-Length", ""))
        except ValueError:
            length = -1
        if not 0 <= length <= MOST_BODY:
            self.close_connection = True
            self._refuse(HTTPStatus.REQUEST_ENTITY_TOO_LARGE, "the module is too long")
            return None
        try:
            body = json.loads(self.rfile.read(length))
        except ValueError:
            self._refuse(HTTPStatus.BAD_REQUEST, "the body is not JSON")
            return None
        if not isinstance(body, dict):
            self._refuse(HTTPStatus.BAD_REQUEST, "the body must be a JSON object")
            return None
        return body

    def do_POST(self):
        if not self._from_this_machine():
            return
        body = self._body()
        if body is None:
            return
        chain = self.server.toolchain
        try:
            text = module_text(body)
            path = urlsplit(self.path).path
            if path == "/api/analyze":
                result = chain.analyze(text)
            elif path == "/api/run":
                result = chain.run(text, run_request(body))
            elif path == "/api/compare":
                result = chain.compare(text, call(body))
            else:
                self._refuse(HTTPStatus.NOT_FOUND, "no such action")
                return
        except BadRequest as e:
            self._refuse(HTTPStatus.BAD_REQUEST, str(e))
        except OSError as e:
            self._refuse(HTTPStatus.INTERNAL_SERVER_ERROR, f"cannot run a tool: {e}")
        else:
            self._json(result)
