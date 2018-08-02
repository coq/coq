# Development notes for typeclass resolution caching #

# Status #

Caching works and on our tests (compiling math-classes) shows 27%
speed up.

# Discussion #

We are caching failures of typeclass resolution. The cache is
basically a set and we check for the membership. It is invalidated by
changes in hints databases or other variables affecting typeclass
resolution mechanims.

Comparing goals is computationally heavy. Due to the nature of
comparison we could not only define equality predicate on goals, not
orderding. Additionally it is not possible to define a hash function
to use a hash set.

We need to strike a ballance between the cost of cache lookups and
number of cache hits. Both addition and lookup of the new goals to
cache are heavy operation (`O(n)`). Our initial naive implementation
("Strict match") gave us 2.49% hit rate with max cache size ~24000
entries.

Implementing more intelligent match up to unresolved evars ("Evar
match") increased the hit ratio to 14% and max cache size become more
manageable: 3995.

Our final observation was that due to the cost of cache lookup it does
not make sense to check it for goals which are the leafs in the proof
search tree. We introduced a `min_goals` parameter which controls how
many dependent goals a goal must have to be included in caching. This
slightly decreased cache size and marginally improved performance.

## Benchmarks: ##

Coq-8.7:
```
 | Experiment     | Time | Hits  | Max cache size |
 | -------------- | ---- | -- -- | -------------- |
 | Baseline       | 3:40 |     0 |              0 |
 | Strict match   | 7:43 | 2.49% |         ~24000 |
 | Evar match     | 5:41 |   14% |           3955 |
 | min_goals=3    | 4:46 |       |              ? |
 | min_goals=4    | 4:37 | 4.09% |            875 |
 | min_goals=10   | 4:47 | 1.62% |            211 |
```

Switching to Coq-8.8 master branch significantly improved cache
performance:

Coq-8.8 (master):
```
 | Experiment     | Time | Hits  | Max cache size |
 | -------------- | ---- | -- -- | -------------- |
 | Baseline       | 4:55 |     0 |              0 |
 | min_goals=4    | 3:34 |  5.4% |           1155 |
```

# Documentation #

Added vernacular commands:

* `Set Typeclasses Caching`
* `Unset Typeclasses Caching`
* `Test Typeclasses Caching`
* `Set Typeclasses Caching Mingoals n`
* `Test Typeclasses Caching Mingoals`

# Links #

* Experimental implementation for Coq-8.7
  https://github.com/vzaliva/coq/tree/typeclass-cache
* Ticket https://github.com/coq/coq/issues/6213


# TODO #
* Can try to optimize further performance of `tc_cache_compare` function
* Try to figure out why switching from 8.7 to 8.8 increased number of cache hits
* Persistently save and load the cache
* Do not cache failures due to hint cut.
* Debug command to examine the cache?
* Add test cases for caching to testsuite/output
