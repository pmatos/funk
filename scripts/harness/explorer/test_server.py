"""The explorer's HTTP surface: who may reach it, and what it accepts."""

import http.client
import json
import socket
import tempfile
import threading
import unittest
from pathlib import Path
from unittest import mock

from explorer import examples
from explorer.server import LOOPBACK, MOST_BODY, Explorer, Handler

TEXT = "func @f() {\n}\n"


class Recorder:
    def __init__(self):
        self.calls = []

    def analyze(self, text):
        self.calls.append(("analyze", text))
        return {"seen": text}

    def run(self, text, req):
        self.calls.append(("run", req))
        return {"kind": "error", "message": "stand-in"}

    def compare(self, text, req):
        self.calls.append(("compare", req))
        return {"status": "passed"}


class ServerTest(unittest.TestCase):
    def setUp(self):
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        root = Path(d.name)
        for group in examples.GROUPS:
            (root / group).mkdir()
        (root / "canonical" / "one.fir").write_text(TEXT)
        (root / "canonical" / "one.toml").write_text(
            'tests = [{ func = "@f", args = ["1"], fuel = 5 }]\n'
        )
        self.tools = Recorder()
        self.server = Explorer(0, self.tools, root)
        self.port = self.server.server_address[1]
        thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        thread.start()
        self.addCleanup(thread.join)
        self.addCleanup(self.server.server_close)
        self.addCleanup(self.server.shutdown)

    def request(self, method, path, body=None, **headers):
        conn = http.client.HTTPConnection(LOOPBACK, self.port)
        self.addCleanup(conn.close)
        conn.request(method, path, body=body, headers=headers)
        r = conn.getresponse()
        return r.status, r.read()

    def origin(self):
        return f"http://{LOOPBACK}:{self.port}"

    def post(self, path, value, **headers):
        merged = {
            "Origin": self.origin(),
            "Content-Type": "application/json",
            **headers,
        }
        return self.request("POST", path, json.dumps(value), **merged)

    def test_it_listens_only_on_the_loopback_address(self):
        self.assertEqual(self.server.server_address[0], LOOPBACK)

    def test_the_page_and_its_modules_are_served(self):
        status, page = self.request("GET", "/")
        self.assertEqual(status, 200)
        self.assertIn(b"fir explorer", page)
        for name in ("app.js", "app.css", "editor.js"):
            self.assertEqual(self.request("GET", f"/{name}")[0], 200, name)

    def test_paths_outside_the_static_files_are_not_served(self):
        for path in ("/../server.py", "/..%2fserver.py", "/etc/passwd", "/server.py"):
            self.assertEqual(self.request("GET", path)[0], 404, path)

    def test_another_host_is_refused(self):
        self.assertEqual(self.request("GET", "/", Host="evil.example")[0], 403)
        status, _ = self.post("/api/analyze", {"text": TEXT}, Host="evil.example")
        self.assertEqual(status, 403)
        self.assertEqual(self.tools.calls, [])

    def test_a_post_from_another_page_runs_nothing(self):
        status, _ = self.post(
            "/api/analyze", {"text": TEXT}, Origin="http://evil.example"
        )
        self.assertEqual(status, 403)
        headers = {"Content-Type": "application/json"}
        status, _ = self.request(
            "POST", "/api/analyze", json.dumps({"text": TEXT}), **headers
        )
        self.assertEqual(status, 403)
        self.assertEqual(self.tools.calls, [])

    def test_a_simple_cross_site_form_post_is_refused(self):
        status, _ = self.post(
            "/api/analyze", {"text": TEXT}, **{"Content-Type": "text/plain"}
        )
        self.assertEqual(status, 415)
        self.assertEqual(self.tools.calls, [])

    def test_analyze_reaches_the_tools(self):
        status, body = self.post("/api/analyze", {"text": TEXT})
        self.assertEqual(status, 200)
        self.assertEqual(json.loads(body), {"seen": TEXT})

    def test_bad_requests_run_nothing(self):
        bad = [
            ("/api/analyze", {"text": 3}),
            ("/api/run", {"text": TEXT, "func": "f"}),
            ("/api/run", {"text": TEXT, "func": "@f", "args": [1]}),
            ("/api/run", {"text": TEXT, "func": "@f", "args": ["a\0"]}),
            ("/api/run", {"text": TEXT, "func": "@f", "fuel": -1}),
            ("/api/run", {"text": TEXT, "func": "@f", "mode": "other"}),
            ("/api/run", {"text": TEXT, "func": "@f", "mode": "seed", "seed": 1 << 64}),
            ("/api/run", {"text": TEXT, "func": "@f", "bits": 65}),
            ("/api/compare", {"text": TEXT}),
        ]
        for path, body in bad:
            self.assertEqual(self.post(path, body)[0], 400, body)
        self.assertEqual(self.tools.calls, [])

    def test_a_module_past_the_size_limit_is_refused(self):
        status, _ = self.post("/api/analyze", {"text": "x" * (MOST_BODY + 1)})
        self.assertEqual(status, 413)

    def test_a_silent_connection_does_not_hold_up_the_others(self):
        with mock.patch.object(Handler, "timeout", 0.1):
            idle = socket.create_connection((LOOPBACK, self.port))
            self.addCleanup(idle.close)
            conn = http.client.HTTPConnection(LOOPBACK, self.port, timeout=5)
            self.addCleanup(conn.close)
            conn.request("GET", "/")
            self.assertEqual(conn.getresponse().status, 200)

    def test_a_seed_sent_as_text_keeps_every_digit(self):
        seed = (1 << 64) - 1
        body = {"text": TEXT, "func": "@f", "mode": "seed", "seed": str(seed)}
        self.assertEqual(self.post("/api/run", body)[0], 200)
        self.assertEqual(self.tools.calls[0][1]["seed"], seed)

    def test_a_seed_that_is_not_a_whole_number_in_range_is_refused(self):
        for seed in ("", "1.5", "-1", str(1 << 64), "9" * 5000):
            body = {"text": TEXT, "func": "@f", "mode": "seed", "seed": seed}
            self.assertEqual(self.post("/api/run", body)[0], 400, seed)

    def test_a_comparison_gets_the_budget_of_the_run(self):
        body = {"text": TEXT, "func": "@f", "bits": 32}
        self.post("/api/compare", body)
        self.assertEqual(self.tools.calls[0][1]["bits"], 32)
        self.assertEqual(self.post("/api/compare", {**body, "bits": 65})[0], 400)

    def test_a_run_gets_defaults_and_a_mode(self):
        self.post("/api/run", {"text": TEXT, "func": "@f"})
        self.assertEqual(
            self.tools.calls,
            [
                (
                    "run",
                    {
                        "func": "@f",
                        "args": [],
                        "fuel": 1_000_000,
                        "mode": "exhaustive",
                        "bits": None,
                    },
                )
            ],
        )

    def test_examples_come_from_the_catalogue_with_their_saved_runs(self):
        _, body = self.request("GET", "/api/examples")
        self.assertEqual(json.loads(body)["canonical"], ["one"])
        _, body = self.request("GET", "/api/example?group=canonical&name=one")
        found = json.loads(body)
        self.assertEqual(found["text"], TEXT)
        self.assertEqual(found["runs"][0]["fuel"], 5)
        for query in ("group=canonical&name=../x", "group=../canonical&name=one"):
            self.assertEqual(self.request("GET", f"/api/example?{query}")[0], 404)
