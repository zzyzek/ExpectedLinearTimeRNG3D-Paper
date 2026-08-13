Data For Convex Hull Graphic
===

Quick Start
---

```
$ ./fmt
$ gnuplot
gnuplot> splot  'p.gp' with lp, 0, 'q.gp' with lp, 'c.gp' with lp
```

Description
---

Simple script to create some points and a convex hull to be used
in a figure for the paper.

The anchor point, $p$, is explicitely set to be the origin `[0,0,0]`.
`Qn` (=30) neighbor points, $Q = (q _ 0, q _ q, \dots, q _ {n-1})$, are generated within a unit cube centered at $p$.

$n$ planes are defined by the point $q _ i$ passing through it with normal
$(q _ i - p)$.
The unnormalized plane equation being $P _ {q _ i}(u) = (q _ i - p) \cdot (u - q)$.

Take all plane triples and solve the linear equation to find the intersection point and
collect them into `candidate_points`.
Points are random, so we're ignoring pathological cases.

From the candidate points, go though and test against each of the planes to see
if they're 'inside' or 'outside', up to some epsilon tolerance.
The remaining points that haven't been discarded by this process make up the
vertex enumeration of the convex hull defined by the intersection of $Q$ planes.

To find the connectivity, run a standard off-the-shelf convex hull algorithm.

The output format is JSON:

```
{
  "n": 30,
  "p": [0,0,0],
  "Q": [ ... ],

  "Q_ch_idx" : [ ... ],
  "Q_ch_v": [ ... ],

  "ch_idx" : [ ... ],
  "ch_p" : [ ... ]
}
```

| Field | Description |
|---|---|
| `n` | $|Q|$ |
| `p` | anchor point |
| `Q` | array of nearby points |
| `Q_ch_v` | array of normalized two point vector, from anchor to $q$, to one of the $q$ that make up the convex hull cutting plane |
| `Q_ch_idx` | indices in $Q$ of $Q$ points that make up convex hull |
| `ch_p` | array of faces (3 points) of vertex enumerated convex hull |
| `ch_idx` | array of face indices (3 points) of vertex enumerated convex hull |

The focus was on getting data ready for ease of display in a graphic.
Some of the data is provided because it was used as an intermediate step and easy to include in the output.

TODO
---

* Use the data to create the graphic

