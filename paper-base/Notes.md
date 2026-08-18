Notes
===

Title should be something more like "Expected Linear Time Algorithm for Computing
Relative Neighborhood Graph for Uniform Random Points in a 3D Unit Cube."

To get something started, I'm using the template provided by [information processing letters (elsevier)](https://www.sciencedirect.com/journal/information-processing-letters/publish/guide-for-authors#writing-and-formatting-latex)

---


###### 2026-08-14

We're settling on terminology:

* *anchor point* : point, $p$, doing the relative neighborhood graph calculation
* *cut plane* : (*cutting plane*, *partitioning plane*) plane defined by anchor point, $p$, and some nearby point $q$
* *partition* : separates a point (e.g. fence post) from some other point (e.g. anchor point)
  (deprecated terminology: *cleave*)
* *fence* : bounding, grid aligned cube
* *fence face patch*: (*face patch*, *patch*) small 2d portion on a fence face,
  in this context it'll be square but in a broader context could be any geometry
* *secure*: (*secure the fence*, *fence is secured*, *patch is secured*, *secured patch*)
  indicates that a cutting plane partitions anchor point from the appropriate target
  (patch, face, fence)
* *fence post*: (4) point corner of a fence patch. Used as proxies that when
  tested for partioned or securitization, under appropriate conditions will indicate 
  whole patch is secured

###### 2026-08-03

I think the algorithm pseudo code should go before the proofs.
The proofs are pretty technical and we should provide them there
for completeness.
I think providing the algorithm first, especially after the motivation
section, will be more enlightening.

Math Preliminaries
---

* plane partition heuristic lemma (done)
* neighbors in convex hull lemma (done)
* convex hull extension lemma (done)
* bbox convex hull securitization 
  - bbox around convex hull max lune outgrowth 
* plume volume in nested cubes is non-zero (and finite) (appendix, mostly done)
  - coupon collector bounds are hand-waivy, try to get better bounds
* expected number of points to make a convex hull (around origin)
  from origin in smaller cube nested in larger cube is bounded above 
  - coupon collector on plume volume (or half plume volume if near side) (done, caveat above)
  - coupon collector should (?) bound outer cube radius (done/see above)

---

You need to discuss the convex hull and how that could lead to a linear expected time
algorithm and why you didn't choose it. (done, talks about conceptual complexity and
constant runtime inflation)


> Working with the convex hull directly could yield an expected linear time algorithm.
> We've chosen to focus on the coarser but conceptually and practically simpler bounding
> cubes.
> ... the reader is encouraged to use the convex hull idea to create an alternative
> expected linear time algorithm ...


---

One issue we missed, in the algorithm implementation as well,
is a check to make sure the $N _ {p,q}$ plane, if it secures the patch,
will keep on securing the patch as the fence is increased.

I believe this is a check to make sure the face normal with the $N _ {p,q}$
normal is positive, but I need to think about this more.

Regardless, we have to:

* add it to the paper as an extra check (done)
* add it to the reference implementation
  - implement it (done)
    + it looks like this might already be implemented. Meant as an optimization, this is
      now a necesary check. The line is when calculating the opposite `idir` from the
      `Nqp` vector and skipping the opposite `idir`. (nope)
  - try to add a test case that triggers this condition to make sure we've actually solved it (todo)
  - go through randomized tests to make sure there's no regression (todo)

UPDATE: this has been added to the code. I've run validation successfully, so no regression happened.
What really needs to be done is some test cases to trigger this issue to make sure it's resolved.

* create a small instance, with bin size hard coded
* place anchor point in some central cell
* place $q$ points nearby
  - focus on top face, place $q$ so that it cleaves the top face but doesn't secure it
  - make sure algorithm notices that it cleaves but doesn't secure
  - do this for all faces


---



Figures
---

The figures are going to be doing a lot of the work.
All lemmas,  theorems and pseudo-code is fine but I think they should be there
for completeness.
The figures are the ones that will describe how the algorithm works.

* (IP) example lune with edge, and excluded edge (2d) (`fig_lune`)
* (IP) hero shot of 2d and 3d relative neighborhood graph (in progress, `fig_rng2d`, `fig_rng3d`)
  - consider adding axies
  - consider adding grid lines
* (IP) graphic of fence and cluster? (`secure_fence` ?)
* (IP) inadmissible region between points p,q, along with cut plane heuristic (2d) (`fig_lune_inadmissible`, `fig_lune_heuristic`)
  - also show an extra point, w, that will always be excluded because of q in lune(p,w)
  - label regions that mirror lemma 1
* (IP) sabotage point in extended region that precludes connection in-region (`fig_sabotage`)
* (SK) securing fence graphic (see `secure_fence` sketch in notes directory)
  - show cutting plane that secures cluster of posts
  - shows cutting plane that partiall cleaves a cluster (and so doesn't secure
* (SK) comic showing outline of math foundations (see `fence_sketch` in notes directory)
  - cut plane, to
  - convex hull, to
  - fence, to
  - extended fence, to
  - (naive rng?)
* (TK) 2d graphic of fence, win center, anchor point, q0 and q1 where
  (p,q0) cutting plane secures two fence posts and (p,q1) partitions fenceposts
  but does not secure them
  - show extended fence with 'ghost' posts, where fence posts would be after fence is
    extended, to show that the cut plane keeps the posts secured whereas the other one
    only partitions the nearest fence posts and doesn't partition the ghost points further on
* (TK) graphic of growing fence, along grid lines (2d)
  - color code growth
  - show 'radius' of cell growth
  - show list of neighbor points
  - highlight anchor point
  - maybe we can get away with showing a wire frame color coded region for the fence growth in 3d
* (TK) algorithm RNGp comic/graphic, detailing operation
  - bin points
  - highlight single point
  - show growing fence
  - cutting planes that block off posts
  - secure fence
  - extend fence
  - naive rng
* (TK) we really should have a 3d lune, maybe with a cut plane as the paper is talking about 3d rng

| Code | Description |
|---|---|
| `IP` | in progress |
| `SK` | sketch |
| `TK` | to come |
