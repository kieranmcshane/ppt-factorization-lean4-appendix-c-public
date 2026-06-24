# From-Scratch U-AUB-02 Article

This folder contains a fresh pure-math LaTeX article built from the current
mathematical frontier, not from the older paper drafts.

Canonical source:

```text
article/from_scratch_u_aub_02/main.tex
```

Canonical build:

```bash
make -C article/from_scratch_u_aub_02 pdf
```

Output:

```text
article/from_scratch_u_aub_02/main.pdf
```

Current mathematical status:

- The article is a self-contained conditional reduction theorem.
- It proves the rank/bidefect identity, shifted-base scalar absorption, parity,
  and genus-induction reduction.
- It does not claim U-AUB-02 is done.
- The publishable PDF deliberately contains no Lean-status appendix or
  proof-assistant theorem names.
- Lean alignment is tracked separately in:

```text
article/from_scratch_u_aub_02/lean_sync_status.md
```

The Grok referee pass is saved in:

```text
article/from_scratch_u_aub_02/grok_referee_report.md
```

The response to the Grok referee objections is saved in:

```text
article/from_scratch_u_aub_02/grok_referee_response.md
```
