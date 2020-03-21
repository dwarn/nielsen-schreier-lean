A formal proof of the Nielsen-Schreier theorem: If H is a subgroup of a free group G, then H is isomorphic to a free group. There is also the "categorified" Schreier index formula relating the rank and index of H. (Although we don't seem to know that "rank" is well defined.)

The theorem itself is in main.lean, but almost all of the work is in action.lean, where we just assume G is acting transitively on some set with a specified element r, and prove the theorem for stabilizer G r. The general theorem follows by considering the coset space G/H.

The proof makes no mention of topology. It's essentially about groupoids but does not explicitly mention them; everything is done from scratch. We implicitly prove that every connected graph has a spanning tree, but at the moment it's all "non-modular".
