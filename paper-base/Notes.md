Notes
===

To get something started, I'm using the template provided by [information processing letters (elsevier)](https://www.sciencedirect.com/journal/information-processing-letters/publish/guide-for-authors#writing-and-formatting-latex)

---

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

Figures
---

The figures are going to be doing a lot of the work.
All lemmas,  theorems and pseudo-code is fine but I think they should be there
for completeness.
The figures are the ones that will describe how the algorithm works.

* example lune with edge, and excluded edge (2d)
* hero shot of 2d and 3d relative neighborhood graph
* inadmissible region between points p,q, along with cut plane heuristic (2d)
  - also show an extra point, w, that will always be excluded because of q in lune(p,w)
  - label regions that mirror lemma 1
* algorithm RNGp comic/graphic, detailing operation
  - bin points
  - highlight single point
  - show growing fence
  - cutting planes that block off posts
  - secure fence
  - extend fence
  - naive rng
* securing fence graphic
  - show cutting plane that secures cluster of posts
  - shows cutting plane that partiall cleaves a cluster (and so doesn't secure
* comic showing outline of math foundations
  - cut plane, to
  - convex hull, to
  - fence, to
  - extended fence, to
  - (naive rng?)
* sabotage point in extended region that precludes connection in-region
* graphic of fence and cluster?
