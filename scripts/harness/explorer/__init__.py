"""A local web app for writing fir and seeing what the tools make of it.

It shows what `funk` and `fir-ref` report and has no semantics of its own
(ADR-2026-11-08-1806). Its modules live under the harness so that they can
share the harness's process mechanics and its judgement of a native run.
"""
