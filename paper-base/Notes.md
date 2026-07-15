Notes
===

To get something started, I'm using the template provided by [information processing letters (elsevier)](https://www.sciencedirect.com/journal/information-processing-letters/publish/guide-for-authors#writing-and-formatting-latex)

---

Math Preliminaries
---

* plane partition heuristic
* neighbors in convex hull
* bbox around convex hull max lune outgrowth
* plume volume in nested cubes is non-zero (and finite)
* expected number of points to make a convex hull (around origin)
  from origin in smaller cube nested in larger cube is bounded above 
  - coupon collector on plume volume (or half plume volume if near side)
  - coupon collector should (?) bound outer cube radius


You need to discuss the convex hull and how that could lead to a linear expected time
algorithm and why you didn't choose it.


> Working with the convex hull directly could yield an expected linear time algorithm.
> We've chosen to focus on the coarser but conceptually and practically simpler bounding
> cubes.
> ... the reader is encouraged to use the convex hull idea to create an alternative
> expected linear time algorithm ...
