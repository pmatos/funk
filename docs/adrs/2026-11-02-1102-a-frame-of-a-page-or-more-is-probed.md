# A frame of a page or more is probed

Status: accepted
Tier: implementation; area: x86-64-backend

## Context

ADR-2026-10-30-1230 probes a frame larger than a page, so that every
access to the stack is at most a page below one already made, and makes a
frame of at most a page one `subq $S, %rsp`.

Calls ([#20](https://github.com/pmatos/funk/issues/20)) write below the
frame: a call pushes its return address 8 bytes below `%rsp`, after the
stack arguments and their padding (ADR-2026-10-30-1232). With a frame of
exactly 4096 bytes, the last access before that write can be the
prologue's `pushq %rbp`, at `%rbp`, and the write lands 4104 bytes below
it. When `%rbp` sits just above a one-page guard region, the write skips
the guard page and lands in memory below it, with no fault. The entry
wrapper of ADR-2026-10-30-1233 uses the same prologue and calls the
runtime right after it, so a wrapper with a frame of 4096 bytes had the
same gap. No other frame size had one.

## Decision

- **A page or more is probed.** `frame::prologue` probes every full page
  of a frame of 4096 bytes or more, a page at a time, then subtracts the
  rest, less than a page. A frame of exactly 4096 bytes is one probed page
  and no rest.
- **Less than a page is one `subq`.** Frames are multiples of 16, so such
  a frame is at most 4080 bytes.
- So a call's first write below a frame, its return address, or its
  padding and first stack argument, is at most 16 bytes below the frame
  and at most a page below the last access: the saved `%rbp` for a small
  frame, the lowest probe for a large one. ADR-2026-10-30-1230's rule
  holds with calls.

## Alternatives

- **Touch the frame's lowest slot before each call.** It closes the same
  gap, but costs an access at every call site and in every wrapper,
  rather than one probe in the prologue of one frame size.

## Consequences

- A frame of exactly 4096 bytes costs the probe loop, run once.
- Read ADR-2026-10-30-1230's "at most a page" for an unprobed frame as
  "less than a page".
- `frame.rs` tests the prologue of a 4096-byte frame, and the backend's
  call tests walk the assembly of calls from frames of 0 to 13, 500 to
  530 and 1015 to 1030 values, checking that every access is at most a
  page below the deepest one before it.
