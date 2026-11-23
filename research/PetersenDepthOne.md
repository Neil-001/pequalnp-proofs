# A 19-gate Petersen circuit needs a negation or two AND gates on one path

Consider fan-in-two circuits whose gates are AND and OR. Suppose each input-to-output path contains at most one AND gate. The minimum size for the Petersen edge function in this class is **20**, even when a wire can feed any number of gates.

More generally, let a finite simple graph have at least one edge, no cycle of length four, $m$ edges and minimum vertex cover size $t$. Its edge function accepts an input if some edge has both endpoints set to one. The exact size in this circuit class is $m+t-1$.

## Lower bound

Remove dead gates, propagate constants, and bypass gates that reproduce an operand. The edge function is false on every singleton input. Consequently a raw input cannot reach the output along an OR-only path. Every live path therefore passes through exactly one AND. The output is the OR of the results of the live AND gates.

Each AND computes `(OR A) AND (OR B)` for two nonempty sets of input vertices. The sets are disjoint, since a vertex in both would make its singleton input accepted. Every pair in their Cartesian product must be an edge. Otherwise, activating that pair alone gives a false positive. If both sets contained two distinct vertices, the four cross edges would give a four-cycle. One set is therefore a singleton. Call its vertex the *center* of this AND and the other set its *leaves*. For a one-edge term either endpoint can serve as center. Every graph edge must occur in some such term, since the input consisting of just that edge is accepted.

Write $r$ for the number of live AND gates. The centers form a vertex cover, so $r \ge t$. For each distinct center $v$, let $r_v$ be its number of terms and $d_v$ the number of distinct leaves in those terms. Edge coverage gives $\sum_v d_v \ge m$.

To supply the $r_v$ leaf wires for center $v$, their combined input cones must contain at least $d_v-r_v$ OR gates. Start at the designated wires and trace the cones backwards. Expanding one distinct binary gate replaces one wire by at most two, so the number of distinct source inputs is at most the number of starting wires plus the number of expanded gates. This also counts leaf wires that are raw inputs.

These OR gates cannot be shared by different centers. A useful OR gate in a leaf cone has at least two distinct input vertices in its support, and both must be neighbors of the center. Sharing it across centers would give the centers two distinct common neighbors and hence a four-cycle. The total number of OR gates below the AND gates is therefore at least $\sum_v(d_v-r_v) \ge m-r$. Combining all $r$ AND outputs requires at least $r-1$ further binary OR gates by the same cone count. Adding the three counts gives at least $m-r+r+(r-1) \ge m+t-1$ gates.

## Construction

Choose a minimum vertex cover and assign every edge to one of its endpoints in that cover. Each cover vertex has a neighbor outside the cover by minimality, so each receives at least one edge. For each center, OR its assigned leaves and AND their result with the center input. OR the resulting $t$ terms. This uses $m-t$ leaf ORs, $t$ ANDs and $t-1$ output ORs.

## Petersen specialization

In the project’s vertex order from 0 through 9, label the vertices 12, 34, 15, 23, 45, 35, 25, 24, 14, 13. Each label denotes a two-element subset of a five-element set. Adjacency means disjointness. There are 15 edges. Two distinct vertices have at most one common neighbor, because the complement of their union has at most two elements. An independent set is a pairwise-intersecting family of pairs. If the pairs all share an element, there are at most four. Otherwise, two intersecting pairs and a third that misses their common element form a triangle on three elements, and those three pairs are the only ones that intersect all three. A four-pair star attains the independence bound, so a minimum vertex cover has $10-4=6$ vertices. Substitution gives $15+6-1=20$.

This counting argument is a written proof. The companion Lean file checks the unrestricted 15-gate lower bound and an explicit 20-gate circuit. It leaves unrestricted sizes 15 through 19 open.
