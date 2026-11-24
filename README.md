# Chess pieces on the square spiral

A piece starts on square 1 of the square spiral and always moves to the lowest-numbered square it
has not visited. Does it ever get trapped, with no unvisited square to move to?

This repository holds proofs, programs and write-ups for the pieces made of the five leapers
W (0,1), F (1,1), D (0,2), N (1,2) and A (2,2). There are 31 such pieces, and with the piece that has no leaper and cannot move, 32. `doc/pieces.md` lists
them all with their OEIS entries.

## Read first

- The paper for F+A: [web page](https://norpan.github.io/spiral-walks/doc/falafel-paper/falafel-paper.html),
  [PDF](https://norpan.github.io/spiral-walks/doc/falafel-paper/falafel-paper.pdf). It is a draft.
- [The 32 pieces](doc/pieces.md): what is proved, what is trapped, what is open.
- [The walk viewer](https://norpan.github.io/spiral-walks/viz/walk-viewer.html): runs the walk of any piece in the browser.

## Results

Three kinds of claim are kept apart: proved, checked by program up to a bound, and observed.

| Piece | OEIS | Result | Basis |
| --- | --- | --- | --- |
| F (Ferz) | A316884 | never trapped | Proved in Lean 4, for every (s,s)-leaper. `lean/Leaper/` |
| A (Alfil) | A317467 | never trapped | The same proof, s = 2. |
| F+A | A399160 | never trapped; a permutation of the odd positive integers; a formula for every term from the 81st on | Proved in Lean 4. `lean/Falafel/`, paper in `doc/falafel-paper/` |
| 16 pieces with W | A000027 | never trapped; the walk is 1, 2, 3, ... | Proved in Lean 4. `lean/Straight/` |
| F+D, F+D+A | A005408 | never trapped; the walk is 1, 3, 5, ... | Proved in Lean 4. `lean/Fortress/` |
| D, D+A | A399158 | never trapped; the squares with both coordinates even, in increasing order | Proved in Lean 4. `lean/Straight/` |
| N | A316667 | trapped at step 2016 | Known. Reproduced by program. |
| F+N | A398717 | trapped at step 1051 | Known. Reproduced by program. |
| A+N | A398779 | trapped at step 59,677 | Known. Reproduced by program. |
| D+N | A398965 | trapped at step 253,925,076 | Known. Reproduced by program. |
| F+A+N | A399167 | trapped at step 256,730,882 on square 267,545,105 | By program. Proposed as a comment on the OEIS entry on 23 Nov 2026. |
| D+A+N (Squirrel) | A399315 | open | No trap in 1.0×10¹³ steps (observed). |
| F+D+N | A398194 | open | No trap in 9×10¹² steps (observed). |
| F+D+A+N | A396103 | open | No trap in 9×10¹² steps (observed). |

The figures for the three open pieces were read on 24 Nov 2026; `doc/pieces.md`
has them in full.

## The Lean proofs

`lean/` is one Lake project with four libraries, on Lean v4.36.0 and Mathlib v4.36.0.
Its `README.md` says how to build it and how the proofs go.

A reader who wants to trust the results has to read five short files and nothing else:

- `lean/Statement.lean` (70 lines): the spiral, the moves of F+A, the walk, four claims.
- `lean/PathStatement.lean` (92 lines): a table that gives every term of A399160 from the 81st on,
  and the claim that it does. Only needed for that formula.
- `lean/LeaperStatement.lean` (50 lines): the same for the (s,s)-leaper.
- `lean/StraightStatement.lean` (57 lines): the same for every piece that can move s squares
  straight and stays on the squares with both coordinates multiples of s.
- `lean/FortressStatement.lean` (42 lines): the same for every piece that has the moves of F and
  of D and whose moves all change x + y by an even number.

The build checks the rest. There is no `sorry` and no `native_decide`. The theorems depend only
on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Programs

| File | What it does |
| --- | --- |
| `programs/walk.c` | Plain simulator for any piece, whole board in memory. `walk LETTERS N H`: piece letters, number of steps, half-width of the board. |
| `programs/piece_frontier.c` | Any piece, storing only the boundary of the visited region, so memory grows with the square root of the step count. Stops and resumes. |
| `programs/squirrel_frontier.c` | The same method for the Squirrel alone, with more statistics. |
| `ferz-alfil/check.py` | Checks the proof by hand for Ferz and Alfil against a simulation. |
| `falafel-proof/` | Scripts for the older proof of F+A by hand and by program. |
| `viz/walk-viewer.html` | A page that runs the walk of any piece in the browser, with pan and zoom. |

Build a C program with `cc -O2 -o walk programs/walk.c`. Usage is in the header comment of each
file. To reproduce the trap of F+A+N:

```
./walk FAN 300000000 9000
```

This needs a board of 18,001 × 18,001 squares, one bit each, about 40 MB.

## Write-ups

| File | What it is |
| --- | --- |
| `doc/pieces.md` | The 32 pieces: names, OEIS entries, results, the figures of the open pieces, the proof for Ferz and Alfil for human readers, and a summary of the proof for F+A. It links to the Lean files. |
| `doc/falafel-paper/` | The proof for F+A as a paper: `falafel-paper.pdf`, also as a web page and LaTeX. `build.py` checks every formula of its tables against the Lean definitions and a simulation before it writes the three files. |
| `doc/falafel-proof.md` | The older proof for F+A by hand and by program. The Lean proof does not depend on it. |

## How this was made

The proofs, programs and texts were written with Claude (Anthropic), in sessions directed by
Martin Norbäck Olivers. The Lean kernel checks the proofs, so they do not rest on who wrote
them. What rests on a person is that the four statement files say what is meant. Martin has read
and approved them. Nobody else has reviewed them yet.

## Licence

MIT, see `LICENSE`.
