Machine checks for the claim that the Falafel walk (OEIS A399160) never ends.
Coordinates: u=(x+y)/2, v=(x-y)/2, in which the Falafel moves 1 or 2 squares like a rook.

python3 lapcheck.py 3000000     the closed formula for the laps against the simulated walk (laps 4..666)
python3 induct.py 300 8 12      check A (all squares distinct), check B (every step is the lowest unvisited
                                neighbour, with "visited" defined by the formula), and that the local picture
                                depends only on a step's address
python3 sources.py 300 8 12     check C: every neighbour of every step is visited by a fixed stretch of a
                                fixed nearby lap at a fixed relative position
induct.py takes about 2 s and sources.py about 9 s in plain Python 3 (measured 23 Nov 2026,
with the four runs going).
python3 extend.py 300           check D: the facts that let checks B and C extend to all laps (section 3,
                                items 3 to 5): neighbour quadrants and same-stretch visit order fixed
                                within an address for all R, address set 12-periodic, key = spiral order. 10 s.

python3 lapnumber.py 1200 250   the lap-number function L(u,v) of the no-overlap lemma: L = R on every square
                                of laps 4..1200; for laps 4..250 the squares with L = R are exactly lap R;
                                the first 80 squares are exactly those with L <= 3 or in the centre block
python3 lapsquares.py 1200      the closed-form list of each lap's squares, stretch by stretch, against the
                                move table, with the region of every square. Both run in seconds.
