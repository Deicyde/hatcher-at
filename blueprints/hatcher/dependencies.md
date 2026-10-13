---
kind: graph
---

# Dependency graph

303 nodes · 565 dependencies. Arrows point from a prerequisite to what depends on it; a dashed
arrow marks a prerequisite that only the proof needs. Select a node to open it.

```mermaid
graph LR
  n0["Appendix<br/><small>5 items · 5 fully proved</small>"]:::scope_complete
  n1["Classical CW bridge support<br/><small>3 items · 3 fully proved</small>"]:::scope_complete
  n2["Classical and standard cells have isomorphic attaching arrows"]:::fully_proved
  n3("Compact subsets lie in a bounded skeleton"):::fully_proved
  n4("A successor classical skeleton has the cell-attachment quotient topology"):::fully_proved
  n5["Classical skeleton inclusions are abstract cell attachments"]:::fully_proved
  n6("Compact subsets lie in finite subcomplexes"):::fully_proved
  n7["Cohomology<br/><small>3 items · 3 not ready</small>"]:::scope
  n8("Cohomology groups"):::not_ready
  n9("Cup product"):::not_ready
  n10("Poincaré duality"):::not_ready
  n11["The fundamental group<br/><small>118 items · 8 in mathlib · 110 fully proved</small>"]:::scope_complete
  n12["Basic constructions<br/><small>22 items · 4 in mathlib · 18 fully proved</small>"]:::scope_complete
  n13["Straight-line homotopy between paths"]:::fully_proved
  n14("Borsuk–Ulam for the two-sphere"):::fully_proved
  n15("Brouwer's fixed point theorem for the disc"):::fully_proved
  n16["A path induces change of basepoint"]:::mathlib
  n17("The real line covers the circle"):::fully_proved
  n18("Convex sets have trivial fundamental group"):::mathlib
  n19("Euclidean two-space is distinguished by dimension"):::fully_proved
  n20("The fundamental group of the circle"):::fully_proved
  n21("Path concatenation gives the fundamental-group law"):::fully_proved
  n22("The fundamental theorem of algebra"):::fully_proved
  n23("Homotopic maps differ by basepoint change"):::fully_proved
  n24["A homotopy equivalence induces a fundamental-group isomorphism"]:::fully_proved
  n25("A loop splits across an open cover"):::fully_proved
  n26("The circle is not a retract of the disc"):::fully_proved
  n27("Path homotopy is an equivalence relation"):::mathlib
  n28["The fundamental group of a product"]:::fully_proved
  n29("Retractions and deformation retracts on the fundamental group"):::fully_proved
  n30("Simply connected spaces have unique path-homotopy classes"):::mathlib
  n31("Higher spheres are simply connected"):::fully_proved
  n32("Three closed sets covering the sphere contain an antipodal pair"):::fully_proved
  n33["The fundamental group of the torus"]:::fully_proved
  n34["Winding number of a loop in the circle"]:::fully_proved
  n35["Covering spaces<br/><small>32 items · 4 in mathlib · 28 fully proved</small>"]:::scope_complete
  n36["Pointed connected covering spaces"]:::fully_proved
  n37("The induced subgroup consists of loops with closed lifts"):::fully_proved
  n38("Changing the lifted basepoint conjugates the image subgroup"):::fully_proved
  n39("Covering maps inject path-homotopy classes"):::mathlib
  n40["Deck transformations and quotient actions<br/><small>8 items · 1 in mathlib · 7 fully proved</small>"]:::scope_complete
  n41("Covering-space actions give quotient coverings"):::fully_proved
  n42["The deck group is the normalizer quotient"]:::fully_proved
  n43("A deck transformation is determined by one lifted point"):::fully_proved
  n44["Deck transformations and normal covers"]:::mathlib
  n45["The normalizer acts by deck transformations"]:::fully_proved
  n46("The normalizer map is surjective with kernel the covering subgroup"):::fully_proved
  n47["Orbit quotients are normal and have the expected deck group"]:::fully_proved
  n48["The orbit-quotient fundamental group recovers the acting group"]:::fully_proved
  n49("Homotopies lift uniquely through a covering map"):::fully_proved
  n50("A map lifts exactly when its fundamental group lands in the covering subgroup"):::fully_proved
  n51("Local path-connectedness ascends along a covering"):::fully_proved
  n52["The fundamental group acts on a covering fiber"]:::mathlib
  n53["Pointed connected covers are classified by subgroups"]:::fully_proved
  n54("Equal image subgroups characterize pointed cover isomorphism"):::fully_proved
  n55["Sheets are cosets of the induced subgroup"]:::fully_proved
  n56("The subgroup cover realizes the chosen subgroup"):::fully_proved
  n57("The subgroup projection is a path-connected covering"):::fully_proved
  n58["The covering space associated to a subgroup"]:::fully_proved
  n59("A lift is determined by one point"):::mathlib
  n60["The path-class universal cover<br/><small>7 items · 7 fully proved</small>"]:::scope_complete
  n61("A simply-connected cover maps uniquely to every pointed connected cover"):::fully_proved
  n62("Small nullhomotopy neighborhoods form a basis"):::fully_proved
  n63["Semilocally simply-connected spaces"]:::fully_proved
  n64("The sets U[γ] form the universal-cover basis"):::fully_proved
  n65("The endpoint map is a covering"):::fully_proved
  n66["The path-class cover is path-connected"]:::fully_proved
  n67["The path-class universal-cover space"]:::fully_proved
  n68("The path-class cover is simply-connected"):::fully_proved
  n69["Connected covers are classified by conjugacy classes"]:::fully_proved
  n70["Van Kampen's theorem<br/><small>64 items · 64 fully proved</small>"]:::scope_complete
  n71["Attaching higher cells preserves the fundamental group"]:::fully_proved
  n72["Attaching 2-cells adds the attaching relations"]:::fully_proved
  n73("The attaching-sphere pieces generate the intersection group"):::fully_proved
  n74["Binary van Kampen is a group pushout"]:::fully_proved
  n75("An open-cover model for attached cells"):::fully_proved
  n76["Cell-attachment support<br/><small>29 items · 29 fully proved</small>"]:::scope_complete
  n77["Every abstract cell attachment has an indexed cone model"]:::fully_proved
  n78["Hatcher's auxiliary cell-attachment cover<br/><small>9 items · 9 fully proved</small>"]:::scope_complete
  n79["The strip enlargement retracts onto the attached space"]:::fully_proved
  n80["The base-side auxiliary cover retracts onto the original space"]:::fully_proved
  n81("Hatcher's binary cover of the strip enlargement"):::fully_proved
  n82["The strip-enlarged cell-attachment space"]:::fully_proved
  n83["The auxiliary cover basepoint transports to the original basepoint"]:::fully_proved
  n84("Overlap meridians recover the attaching loops"):::fully_proved
  n85("The auxiliary overlap has an indexed open cover"):::fully_proved
  n86["Each overlap piece has the homotopy type of its attaching sphere"]:::fully_proved
  n87("The strip-connected upper cover is contractible"):::fully_proved
  n88["A binary cover with a contractible second piece"]:::fully_proved
  n89["A binary cover with a trivial second fundamental group"]:::fully_proved
  n90("The degree-n circle map sends the generator to the degree-n loop"):::fully_proved
  n91("The circle is well-pointed at one"):::fully_proved
  n92["The cone on a disk boundary is the disk"]:::fully_proved
  n93["The degree-n circle relation gives the cyclic group"]:::fully_proved
  n94["The boundary of the two-disk is the circle"]:::fully_proved
  n95["An attachment with no cells is an isomorphism"]:::fully_proved
  n96("Higher-cell attachments preserve path components"):::fully_proved
  n97["An indexed cone attachment is a standard cell attachment"]:::fully_proved
  n98("An indexed family of cones has a two-set open cover"):::fully_proved
  n99("An indexed family of cone attachments is a topological pushout"):::fully_proved
  n100("The 2-skeleton of a path-connected CW complex is path-connected"):::fully_proved
  n101["A single cone attachment is a standard cell attachment"]:::fully_proved
  n102["The base-side cone cover retracts onto the original space"]:::fully_proved
  n103["The single-cone cover intersection has the homotopy type of its boundary"]:::fully_proved
  n104("A single cone attachment has a two-set open cover"):::fully_proved
  n105("A single cone attachment is a topological pushout"):::fully_proved
  n106("The cone-side cover member is contractible"):::fully_proved
  n107["Cover factorizations of a loop"]:::fully_proved
  n108["The group presentation associated to an open cover"]:::fully_proved
  n109("Overlap relations vanish under the cover map"):::fully_proved
  n110("Every group is a fundamental group"):::fully_proved
  n111("Every group admits a generators-and-relations presentation"):::fully_proved
  n112("Elementary factorization moves preserve the quotient class"):::fully_proved
  n113["Finite skeleta above dimension two have the same fundamental group"]:::fully_proved
  n114("Homotopic factorizations have the same quotient class"):::fully_proved
  n115("A homotopy admits a threefold-incidence cover decomposition"):::fully_proved
  n116["The pointed wedge of a family of spaces"]:::fully_proved
  n117["Presentation-complex support<br/><small>13 items · 13 fully proved</small>"]:::scope_complete
  n118["Collapsing the boundary of a one-disk gives the circle"]:::fully_proved
  n119["The cyclic presentation complex"]:::fully_proved
  n120["Every fundamental-group element has a based disk-boundary representative"]:::fully_proved
  n121["The identity attaches an empty family of cells"]:::fully_proved
  n122["Eventually constant cell sequences form abstract CW complexes"]:::fully_proved
  n123["A point is one standard zero-cell"]:::fully_proved
  n124["Pointed wedges of path-connected spaces are path-connected"]:::fully_proved
  n125["Continuous maps out of a pointed wedge"]:::fully_proved
  n126["The presentation complex is an abstract two-dimensional CW complex"]:::fully_proved
  n127["The presentation complex has the presented fundamental group"]:::fully_proved
  n128("Presented groups have two-dimensional presentation complexes"):::fully_proved
  n129["Free-group relators form a standard two-cell attachment"]:::fully_proved
  n130["A wedge of circles is an indexed one-cell attachment"]:::fully_proved
  n131["The 2-skeleton determines the fundamental group"]:::fully_proved
  n132("The kernel is generated by overlap relations"):::fully_proved
  n133["Van Kampen's quotient isomorphism"]:::fully_proved
  n134("The van Kampen cover map is surjective"):::fully_proved
  n135["The fundamental group of a wedge of circles"]:::fully_proved
  n136["The fundamental group of a wedge"]:::fully_proved
  n137("The standard cover of a well-pointed wedge"):::fully_proved
  n138["Homology<br/><small>146 items · 10 in mathlib · 126 fully proved · 3 ready to state · 1 not ready · 6 planned</small>"]:::scope
  n139["Computations and applications<br/><small>90 items · 81 fully proved · 3 ready to state · 6 planned</small>"]:::scope
  n140["Degree foundations and applications<br/><small>16 items · 16 fully proved</small>"]:::scope_complete
  n141("The antipodal map has degree determined by dimension"):::fully_proved
  n142("The formal properties of degree"):::fully_proved
  n143("A sphere reflection has degree minus one"):::fully_proved
  n144("Swapping the double simplex negates its fundamental class"):::fully_proved
  n145("A fixed-point-free sphere map has antipodal degree"):::fully_proved
  n146("Only the antipodal group acts freely on an even sphere"):::fully_proved
  n147["The ordered class orients ordinary sphere homology"]:::fully_proved
  n148("A nonsurjective sphere map has degree zero"):::fully_proved
  n149("A sphere has a nonvanishing tangent field exactly in odd dimension"):::fully_proved
  n150["Odd spheres have a nonvanishing tangent field"]:::fully_proved
  n151["A punctured sphere is Euclidean space"]:::fully_proved
  n152["Degree gives a character of a sphere action"]:::fully_proved
  n153("Coordinate sign changes on the sphere"):::fully_proved
  n154("Degree is the multiplier of the ordered sphere class"):::fully_proved
  n155("A nonvanishing tangent field forces odd dimension"):::fully_proved
  n156["Tangent vector fields and normalization"]:::fully_proved
  n157["Local degree and the sum over a finite fiber<br/><small>20 items · 11 fully proved · 3 ready to state · 6 planned</small>"]:::scope
  n158("Degree is the sum of the local degrees"):::planned
  n159("Deleted-pair homology is local on an open neighborhood"):::fully_proved
  n160["A disjoint open family is homeomorphic to its sigma type"]:::fully_proved
  n161["Disjoint punctured neighborhoods form the deleted union pair"]:::fully_proved
  n162("The finite-fiber pair map acts by the local degrees"):::planned
  n163["A finite sphere-map fiber has disjoint isolated neighborhoods"]:::fully_proved
  n164["Finite-puncture homology is the coproduct of the local groups"]:::planned
  n165("The finite-puncture class is the sum of the local classes"):::planned
  n166("The disjoint local pairs excise to the finite-puncture pair"):::can_state
  n167("Finite-puncture projections have the diagonal matrix"):::planned
  n168("The finite-fiber pair map carries the global degree"):::fully_proved
  n169("A local homeomorphism has local degree plus or minus one"):::can_state
  n170["An isolated preimage gives a map of punctured pairs"]:::fully_proved
  n171("Local degree is unchanged when the neighborhood shrinks"):::fully_proved
  n172("Local degree is independent of its neighborhood"):::fully_proved
  n173("Local degree on a chosen isolated neighborhood"):::fully_proved
  n174["Relative chains commute with coproducts of arbitrary pairs"]:::can_state
  n175["Relative homology commutes with coproducts of arbitrary pairs"]:::planned
  n176["The coproduct of a family of topological pairs"]:::fully_proved
  n177["The ordered sphere class orients local homology"]:::fully_proved
  n178["Local homology and invariance of dimension<br/><small>4 items · 4 fully proved</small>"]:::scope_complete
  n179["Relative homology in a contractible ambient space"]:::fully_proved
  n180("Homeomorphic nonempty Euclidean open sets have equal dimension"):::fully_proved
  n181("Local homology is unchanged on an open neighborhood"):::fully_proved
  n182("Local homology of positive-dimensional Euclidean space"):::fully_proved
  n183["Mayer–Vietoris sequences<br/><small>6 items · 6 fully proved</small>"]:::scope_complete
  n184("Augmented binary-cover chains form a short exact sequence"):::fully_proved
  n185["The binary-cover Mayer–Vietoris chain complex"]:::fully_proved
  n186("Binary-cover chains form a short exact sequence"):::fully_proved
  n187("The binary-cover Mayer–Vietoris sequence"):::fully_proved
  n188("The reduced binary-cover Mayer–Vietoris sequence"):::fully_proved
  n189["Small augmented chains include by a chain-homotopy equivalence"]:::fully_proved
  n190["Post-excision applications<br/><small>28 items · 28 fully proved</small>"]:::scope_complete
  n191["A contractible subspace identifies reduced and relative homology"]:::fully_proved
  n192("Excision holds for a union of CW subcomplexes"):::fully_proved
  n193["CW-subcomplex regular neighborhoods<br/><small>5 items · 5 fully proved</small>"]:::scope_complete
  n194["The radial collar of a cell boundary"]:::fully_proved
  n195["A regular neighborhood strongly deformation retracts onto its subcomplex"]:::fully_proved
  n196["A common regular-neighborhood system for subcomplexes"]:::fully_proved
  n197["Intersections of CW subcomplexes"]:::fully_proved
  n198("Subcomplex decompositions admit compatible neighborhoods"):::fully_proved
  n199("The double-simplex difference generates reduced homology"):::fully_proved
  n200["The ordered difference of the two simplices is a cycle"]:::fully_proved
  n201("The first simplex computes homology relative to the second"):::fully_proved
  n202["The double simplex is a sphere"]:::fully_proved
  n203["The mapping-cone cover has the relative homology of the original pair"]:::fully_proved
  n204["The mapping cone of a topological pair"]:::fully_proved
  n205["Relative homology is reduced homology of the mapping cone"]:::fully_proved
  n206["The pointed wedge is the point quotient of the sigma pair"]:::fully_proved
  n207["Relative homology commutes with exact coproducts"]:::fully_proved
  n208("The identity simplex generates relative simplex homology"):::fully_proved
  n209("A nonempty coproduct of pointed good pairs is good"):::fully_proved
  n210["The coproduct pair of a family of pointed spaces"]:::fully_proved
  n211["Relative singular chains commute with topological coproducts"]:::fully_proved
  n212["Standard-simplex boundary and horn pairs are good"]:::fully_proved
  n213["The boundary and zero horn of a standard topological simplex"]:::fully_proved
  n214["The standard simplex pair is homeomorphic to the disk pair"]:::fully_proved
  n215["The zero face identifies the two simplex point quotients"]:::fully_proved
  n216("The zero face induces an isomorphism in relative homology"):::fully_proved
  n217["A standard simplex strongly deformation retracts onto its zero horn"]:::fully_proved
  n218("The triple connecting map sends a relative cycle to its boundary"):::fully_proved
  n219("Reduced homology of a wedge is the direct sum of the summands"):::fully_proved
  n220["Mayer–Vietoris transport, sphere homology, and Brouwer<br/><small>16 items · 16 fully proved</small>"]:::scope_complete
  n221("Brouwer's fixed-point theorem for disks"):::fully_proved
  n222["A closed ball strongly deformation retracts from Euclidean space"]:::fully_proved
  n223("Reduced homology of a contractible space vanishes"):::fully_proved
  n224("The boundary sphere is not a retract of the disk"):::fully_proved
  n225("A fixed-point-free disk map produces a boundary retraction"):::fully_proved
  n226["A homotopy equivalence induces reduced-homology isomorphisms"]:::fully_proved
  n227("The ordinary neighborhood-retract Mayer–Vietoris sequence"):::fully_proved
  n228["A sphere strongly deformation retracts from punctured Euclidean space"]:::fully_proved
  n229("Homotopic maps induce the same reduced-homology map"):::fully_proved
  n230("The reduced neighborhood-retract Mayer–Vietoris sequence"):::fully_proved
  n231["The hemispheres have compatible neighborhood deformation retractions"]:::fully_proved
  n232["Stereographic models for hemispheres and the equator"]:::fully_proved
  n233("Reduced homology of spheres"):::fully_proved
  n234("The reduced homology of spheres satisfies the suspension recurrence"):::fully_proved
  n235("Reduced homology of the zero-sphere"):::fully_proved
  n236["The zero-sphere is a two-point space"]:::fully_proved
  n237("The formal viewpoint"):::not_ready
  n238["Simplicial and singular homology<br/><small>55 items · 10 in mathlib · 45 fully proved</small>"]:::scope_complete
  n239("Chain-homotopic maps induce the same homology map"):::mathlib
  n240["A chain map induces a map on homology"]:::mathlib
  n241["A homotopy equivalence induces homology isomorphisms"]:::fully_proved
  n242("Homology of a point"):::fully_proved
  n243["Relative homology and exact sequences<br/><small>45 items · 2 in mathlib · 43 fully proved</small>"]:::scope_complete
  n244["The augmented singular chain complex"]:::fully_proved
  n245["Good pairs and quotient exact sequences<br/><small>16 items · 16 fully proved</small>"]:::scope_complete
  n246["Good pairs and neighborhood deformation retracts"]:::fully_proved
  n247["The complementary excision diagram"]:::fully_proved
  n248("Restricting the quotient to a good-pair neighborhood"):::fully_proved
  n249["Enlarging to the chosen neighborhood preserves relative homology"]:::fully_proved
  n250("The good-pair quotient exact sequence"):::fully_proved
  n251("Good-pair relative homology is reduced quotient homology"):::fully_proved
  n252("Naturality of the good-pair quotient sequence"):::fully_proved
  n253["The good-pair quotient comparison is natural"]:::fully_proved
  n254["Functorial point quotients of topological pairs"]:::fully_proved
  n255["The quotient neighborhood contracts to its point"]:::fully_proved
  n256["The neighborhood quotient map preserves relative homology"]:::fully_proved
  n257["Enlarging the quotient point preserves relative homology"]:::fully_proved
  n258["Topology of the point-quotient projection"]:::fully_proved
  n259("The pointed relative-to-reduced comparison is natural"):::fully_proved
  n260("Componentwise isomorphisms imply a relative isomorphism"):::fully_proved
  n261["Strong deformation retracts"]:::fully_proved
  n262("The long exact sequence of a pair"):::fully_proved
  n263("The pair long exact sequence is natural"):::fully_proved
  n264["Relative homology at a basepoint is reduced homology"]:::fully_proved
  n265["Zeroth homology splits into reduced homology and the coefficient object"]:::fully_proved
  n266("The reduced long exact sequence of a nonempty pair"):::fully_proved
  n267("The reduced pair long exact sequence is natural"):::fully_proved
  n268["Reduced and ordinary homology agree in positive degrees"]:::fully_proved
  n269["Reduced singular homology"]:::fully_proved
  n270("Homotopic maps of pairs induce the same relative-homology map"):::fully_proved
  n271["A homotopy of pairs gives a relative chain homotopy"]:::fully_proved
  n272["Relative singular chains and homology"]:::fully_proved
  n273("A short exact sequence gives an exact homology sequence"):::mathlib
  n274["Relative homology of a simplicial-set pair"]:::mathlib
  n275["The singular set of a topological pair"]:::fully_proved
  n276["Small chains and excision<br/><small>10 items · 10 fully proved</small>"]:::scope_complete
  n277("Affine barycentric subdivision is compatible with faces"):::fully_proved
  n278["Affine-chain subdivision is homotopic to the identity"]:::fully_proved
  n279("Barycentric subdivision contracts simplex diameter"):::fully_proved
  n280("The binary-cover excision chain map is a homotopy equivalence"):::fully_proved
  n281["Binary-cover excision induces homology isomorphisms"]:::fully_proved
  n282["Deleted-subset excision induces homology isomorphisms"]:::fully_proved
  n283("Iterated subdivision eventually makes every singular simplex small"):::fully_proved
  n284("Relative excision reduces to the union subcomplex"):::fully_proved
  n285["Singular-chain subdivision is naturally homotopic to the identity"]:::fully_proved
  n286["Small singular chains include by a chain-homotopy equivalence"]:::fully_proved
  n287["Topological triples and their maps"]:::fully_proved
  n288("Relative chains of a triple form a short exact sequence"):::fully_proved
  n289("The long exact sequence of a triple"):::fully_proved
  n290("The triple long exact sequence is natural"):::fully_proved
  n291["The singular chain complex"]:::mathlib
  n292["Singular homology"]:::mathlib
  n293("Homotopic maps induce the same singular-homology map"):::mathlib
  n294["A topological homotopy gives a singular-chain homotopy"]:::mathlib
  n295("Higher homology vanishes for totally disconnected spaces"):::mathlib
  n296["Zeroth homology is free on path components"]:::mathlib
  n297["Homotopy theory<br/><small>3 items · 3 not ready</small>"]:::scope
  n298("Connections with cohomology"):::not_ready
  n299("Elementary methods of calculation"):::not_ready
  n300("Homotopy groups"):::not_ready
  n301["Algebraic Topology (Hatcher) roadmap<br/><small>276 items · 18 in mathlib · 241 fully proved · 3 ready to state · 8 not ready · 6 planned</small>"]:::scope
  n302("Some underlying geometric notions"):::not_ready
  n6 -.-> n3
  n2 --> n4
  n2 --> n5
  n4 --> n5
  n20 --> n14
  n31 --> n14
  n26 --> n15
  n21 --> n16
  n30 -.-> n18
  n20 --> n19
  n31 --> n19
  n34 --> n20
  n17 -.-> n20
  n27 --> n21
  n20 --> n22
  n20 --> n26
  n27 --> n30
  n25 --> n31
  n14 --> n32
  n28 --> n33
  n20 --> n33
  n17 --> n34
  n52 --> n37
  n52 -.-> n38
  n37 -.-> n38
  n44 --> n41
  n59 -.-> n41
  n44 --> n42
  n36 --> n42
  n46 -.-> n42
  n52 -.-> n42
  n44 --> n43
  n36 --> n43
  n54 -.-> n43
  n59 -.-> n43
  n44 --> n45
  n36 --> n45
  n52 --> n45
  n43 -.-> n45
  n38 -.-> n45
  n45 --> n46
  n37 -.-> n46
  n43 -.-> n46
  n44 --> n47
  n41 --> n47
  n59 -.-> n47
  n41 --> n48
  n42 -.-> n48
  n47 -.-> n48
  n36 --> n53
  n63 --> n53
  n58 -.-> n53
  n56 -.-> n53
  n54 -.-> n53
  n36 --> n54
  n50 -.-> n54
  n59 -.-> n54
  n51 -.-> n54
  n52 -.-> n55
  n37 -.-> n55
  n58 --> n56
  n57 -.-> n56
  n37 -.-> n56
  n58 --> n57
  n65 -.-> n57
  n66 -.-> n57
  n64 -.-> n57
  n67 --> n58
  n36 --> n61
  n50 -.-> n61
  n59 -.-> n61
  n51 -.-> n61
  n63 --> n62
  n67 --> n64
  n62 -.-> n64
  n67 --> n65
  n64 -.-> n65
  n67 --> n66
  n64 -.-> n66
  n63 --> n67
  n67 --> n68
  n65 -.-> n68
  n66 -.-> n68
  n39 -.-> n68
  n37 -.-> n68
  n36 --> n69
  n63 --> n69
  n38 -.-> n69
  n53 -.-> n69
  n75 -.-> n71
  n95 -.-> n71
  n83 -.-> n71
  n73 -.-> n71
  n88 -.-> n71
  n31 -.-> n71
  n75 --> n72
  n94 --> n72
  n95 --> n72
  n83 --> n72
  n84 --> n72
  n73 --> n72
  n89 --> n72
  n29 --> n72
  n20 --> n72
  n75 --> n73
  n134 -.-> n73
  n133 -.-> n74
  n77 --> n75
  n82 --> n75
  n79 -.-> n75
  n81 -.-> n75
  n80 -.-> n75
  n87 -.-> n75
  n83 -.-> n75
  n85 -.-> n75
  n86 -.-> n75
  n97 --> n77
  n82 --> n79
  n81 --> n80
  n102 -.-> n80
  n82 --> n81
  n98 --> n82
  n81 --> n83
  n80 --> n83
  n77 --> n84
  n83 --> n84
  n86 --> n84
  n94 --> n84
  n20 -.-> n84
  n81 --> n85
  n85 --> n86
  n103 -.-> n86
  n81 --> n87
  n106 -.-> n87
  n74 -.-> n88
  n29 -.-> n88
  n74 -.-> n89
  n20 --> n90
  n104 --> n92
  n20 --> n93
  n20 --> n94
  n77 --> n95
  n98 --> n95
  n98 -.-> n96
  n77 -.-> n96
  n80 -.-> n96
  n95 -.-> n96
  n99 --> n97
  n92 --> n97
  n104 --> n98
  n98 --> n99
  n3 -.-> n100
  n5 -.-> n100
  n96 -.-> n100
  n92 --> n101
  n105 --> n101
  n104 --> n102
  n104 --> n103
  n104 --> n105
  n104 --> n106
  n108 --> n107
  n108 --> n109
  n111 -.-> n110
  n128 -.-> n110
  n107 --> n112
  n108 --> n112
  n5 -.-> n113
  n100 -.-> n113
  n71 -.-> n113
  n96 -.-> n113
  n107 --> n114
  n108 --> n114
  n112 -.-> n114
  n115 -.-> n114
  n104 --> n118
  n92 --> n118
  n98 --> n119
  n94 --> n119
  n90 --> n119
  n97 --> n119
  n72 --> n119
  n93 --> n119
  n94 --> n120
  n97 --> n123
  n116 --> n124
  n116 --> n125
  n123 --> n126
  n130 --> n126
  n129 --> n126
  n121 --> n126
  n122 --> n126
  n129 --> n127
  n124 --> n127
  n135 --> n127
  n72 --> n127
  n127 -.-> n128
  n126 -.-> n128
  n120 --> n129
  n135 --> n129
  n97 --> n129
  n72 --> n129
  n116 --> n130
  n125 --> n130
  n118 --> n130
  n97 --> n130
  n113 -.-> n131
  n3 -.-> n131
  n108 --> n132
  n109 -.-> n132
  n114 -.-> n132
  n109 --> n133
  n134 -.-> n133
  n132 -.-> n133
  n108 --> n134
  n25 -.-> n134
  n136 --> n135
  n91 --> n135
  n20 --> n135
  n116 --> n136
  n137 --> n136
  n133 -.-> n136
  n116 --> n137
  n153 --> n141
  n142 -.-> n141
  n143 -.-> n141
  n154 --> n142
  n154 --> n143
  n153 --> n143
  n142 -.-> n143
  n200 --> n144
  n199 --> n144
  n154 --> n145
  n142 -.-> n145
  n141 -.-> n145
  n153 --> n146
  n152 --> n146
  n145 -.-> n146
  n202 --> n147
  n268 --> n147
  n154 --> n148
  n151 -.-> n148
  n223 -.-> n148
  n156 --> n149
  n155 -.-> n149
  n150 -.-> n149
  n156 --> n150
  n232 -.-> n151
  n142 --> n152
  n144 --> n153
  n202 --> n153
  n147 --> n154
  n156 --> n155
  n142 -.-> n155
  n141 -.-> n155
  n165 --> n158
  n162 --> n158
  n168 --> n158
  n272 --> n159
  n181 --> n159
  n281 -.-> n159
  n176 --> n161
  n160 --> n161
  n181 --> n161
  n172 --> n162
  n166 --> n162
  n170 --> n163
  n175 --> n164
  n166 --> n164
  n177 --> n165
  n167 --> n165
  n168 --> n165
  n159 --> n166
  n161 --> n166
  n163 --> n166
  n164 --> n167
  n177 --> n168
  n163 --> n168
  n154 --> n168
  n172 --> n169
  n142 --> n169
  n181 --> n170
  n173 --> n171
  n171 --> n172
  n177 --> n173
  n170 --> n173
  n176 --> n174
  n272 --> n174
  n211 -.-> n174
  n174 --> n175
  n207 --> n175
  n210 --> n176
  n147 --> n177
  n151 --> n177
  n191 --> n177
  n266 --> n179
  n223 -.-> n179
  n181 -.-> n180
  n182 -.-> n180
  n272 --> n181
  n282 -.-> n181
  n181 --> n182
  n179 -.-> n182
  n228 -.-> n182
  n226 -.-> n182
  n233 -.-> n182
  n185 --> n184
  n189 --> n184
  n244 --> n184
  n186 -.-> n184
  n291 --> n185
  n283 --> n185
  n185 --> n186
  n186 --> n187
  n280 --> n187
  n286 -.-> n187
  n273 -.-> n187
  n184 --> n188
  n269 --> n188
  n189 -.-> n188
  n273 -.-> n188
  n244 --> n189
  n286 --> n189
  n272 --> n191
  n269 --> n191
  n259 --> n191
  n266 -.-> n191
  n223 -.-> n191
  n272 --> n192
  n198 -.-> n192
  n281 -.-> n192
  n260 -.-> n192
  n241 -.-> n192
  n196 --> n195
  n261 --> n195
  n197 --> n196
  n194 --> n196
  n197 --> n198
  n196 --> n198
  n195 --> n198
  n200 --> n199
  n208 -.-> n199
  n201 -.-> n199
  n191 -.-> n199
  n259 -.-> n199
  n213 --> n200
  n269 --> n200
  n200 --> n201
  n212 -.-> n201
  n215 -.-> n201
  n216 -.-> n201
  n251 -.-> n201
  n253 -.-> n201
  n214 --> n202
  n200 --> n202
  n199 --> n202
  n204 --> n203
  n272 --> n203
  n102 -.-> n203
  n103 -.-> n203
  n241 -.-> n203
  n260 -.-> n203
  n104 --> n204
  n280 --> n204
  n105 -.-> n204
  n204 --> n205
  n191 --> n205
  n203 --> n205
  n272 --> n205
  n269 --> n205
  n281 -.-> n205
  n106 -.-> n205
  n210 --> n206
  n116 --> n206
  n254 --> n206
  n125 -.-> n206
  n211 --> n207
  n213 --> n208
  n217 -.-> n208
  n216 -.-> n208
  n218 -.-> n208
  n289 -.-> n208
  n270 -.-> n208
  n242 -.-> n208
  n210 --> n209
  n246 --> n209
  n261 --> n209
  n264 --> n210
  n210 --> n211
  n272 --> n211
  n213 --> n212
  n246 --> n212
  n287 --> n213
  n272 --> n213
  n213 --> n214
  n213 --> n215
  n254 --> n215
  n213 --> n216
  n212 -.-> n216
  n215 -.-> n216
  n251 -.-> n216
  n253 -.-> n216
  n281 -.-> n216
  n213 --> n217
  n261 --> n217
  n288 --> n218
  n289 -.-> n218
  n207 --> n219
  n209 --> n219
  n206 --> n219
  n264 --> n219
  n259 -.-> n219
  n253 -.-> n219
  n223 -.-> n219
  n137 -.-> n219
  n224 -.-> n221
  n225 -.-> n221
  n227 --> n222
  n269 --> n223
  n226 -.-> n223
  n264 -.-> n223
  n223 -.-> n224
  n233 -.-> n224
  n269 --> n226
  n229 -.-> n226
  n187 --> n227
  n137 --> n227
  n261 --> n227
  n241 -.-> n227
  n227 --> n228
  n269 --> n229
  n294 -.-> n229
  n239 -.-> n229
  n227 --> n230
  n188 --> n230
  n226 -.-> n230
  n227 --> n231
  n232 --> n231
  n222 -.-> n231
  n228 -.-> n231
  n269 --> n233
  n234 -.-> n233
  n235 -.-> n233
  n269 --> n234
  n223 -.-> n234
  n230 -.-> n234
  n232 -.-> n234
  n231 -.-> n234
  n269 --> n235
  n236 -.-> n235
  n296 -.-> n235
  n265 -.-> n235
  n295 -.-> n235
  n268 -.-> n235
  n240 --> n239
  n292 --> n241
  n240 -.-> n241
  n293 -.-> n241
  n292 --> n242
  n296 -.-> n242
  n295 -.-> n242
  n291 --> n244
  n261 --> n246
  n258 --> n247
  n248 --> n247
  n249 --> n247
  n282 --> n247
  n246 --> n248
  n258 --> n248
  n246 --> n249
  n260 -.-> n249
  n241 -.-> n249
  n253 --> n250
  n266 --> n250
  n246 --> n251
  n254 --> n251
  n264 --> n251
  n247 -.-> n251
  n249 -.-> n251
  n257 -.-> n251
  n256 -.-> n251
  n250 --> n252
  n259 -.-> n252
  n253 -.-> n252
  n267 -.-> n252
  n246 --> n253
  n254 --> n253
  n251 --> n253
  n259 --> n253
  n248 --> n255
  n247 --> n256
  n282 -.-> n256
  n248 --> n257
  n255 -.-> n257
  n260 -.-> n257
  n241 -.-> n257
  n254 --> n258
  n264 --> n259
  n267 -.-> n259
  n272 --> n260
  n262 -.-> n260
  n272 --> n262
  n292 --> n262
  n274 -.-> n262
  n273 -.-> n262
  n262 --> n263
  n272 --> n263
  n273 -.-> n263
  n272 --> n264
  n269 --> n264
  n266 -.-> n264
  n242 -.-> n264
  n269 --> n265
  n262 --> n266
  n268 --> n266
  n265 --> n266
  n266 --> n267
  n263 -.-> n267
  n244 -.-> n267
  n273 -.-> n267
  n269 --> n268
  n292 --> n268
  n244 --> n269
  n272 --> n270
  n271 -.-> n270
  n239 -.-> n270
  n272 --> n271
  n294 -.-> n271
  n275 --> n272
  n292 --> n272
  n240 --> n273
  n240 --> n274
  n274 --> n275
  n277 --> n278
  n277 --> n279
  n272 --> n280
  n286 -.-> n280
  n284 -.-> n280
  n280 --> n281
  n272 --> n281
  n239 -.-> n281
  n272 --> n282
  n281 -.-> n282
  n285 --> n283
  n279 -.-> n283
  n274 --> n284
  n291 --> n285
  n277 --> n285
  n278 -.-> n285
  n283 --> n286
  n285 -.-> n286
  n287 --> n288
  n272 --> n288
  n274 -.-> n288
  n288 --> n289
  n273 -.-> n289
  n289 --> n290
  n273 -.-> n290
  n291 --> n292
  n291 --> n293
  n240 --> n293
  n239 -.-> n293
  n294 -.-> n293
  n291 --> n294
  n292 --> n295
  n292 --> n296
  click n0 "roadmap/appendix/README.md" "Appendix — 5 items · 5 fully proved"
  click n1 "roadmap/appendix/classical-cw-bridge/README.md" "Classical CW bridge support — 3 items · 3 fully proved"
  click n2 "roadmap/appendix/classical-cw-bridge/classical-cell-arrow-iso.md" "Classical and standard cells have isomorphic attaching arrows — fully proved"
  click n3 "roadmap/appendix/classical-cw-bridge/compact-subset-bounded-skeleton.md" "Compact subsets lie in a bounded skeleton — fully proved"
  click n4 "roadmap/appendix/classical-cw-bridge/successor-skeleton-quotient.md" "A successor classical skeleton has the cell-attachment quotient topology — fully proved"
  click n5 "roadmap/appendix/classical-skeleton-cell-attachment.md" "Classical skeleton inclusions are abstract cell attachments — fully proved"
  click n6 "roadmap/appendix/compact-subspace-finite-subcomplex.md" "Compact subsets lie in finite subcomplexes — fully proved"
  click n7 "roadmap/cohomology/README.md" "Cohomology — 3 items · 3 not ready"
  click n8 "roadmap/cohomology/cohomology-groups/README.md" "Cohomology groups — not ready"
  click n9 "roadmap/cohomology/cup-product/README.md" "Cup product — not ready"
  click n10 "roadmap/cohomology/poincare-duality/README.md" "Poincaré duality — not ready"
  click n11 "roadmap/fundamental-group/README.md" "The fundamental group — 118 items · 8 in mathlib · 110 fully proved"
  click n12 "roadmap/fundamental-group/basic-constructions/README.md" "Basic constructions — 22 items · 4 in mathlib · 18 fully proved"
  click n13 "roadmap/fundamental-group/basic-constructions/affine-path-homotopy.md" "Straight-line homotopy between paths — fully proved"
  click n14 "roadmap/fundamental-group/basic-constructions/borsuk-ulam-sphere.md" "Borsuk–Ulam for the two-sphere — fully proved"
  click n15 "roadmap/fundamental-group/basic-constructions/brouwer-disc.md" "Brouwer's fixed point theorem for the disc — fully proved"
  click n16 "roadmap/fundamental-group/basic-constructions/change-of-basepoint.md" "A path induces change of basepoint — in mathlib"
  click n17 "roadmap/fundamental-group/basic-constructions/circle-covering.md" "The real line covers the circle — fully proved"
  click n18 "roadmap/fundamental-group/basic-constructions/convex-trivial-fundamental-group.md" "Convex sets have trivial fundamental group — in mathlib"
  click n19 "roadmap/fundamental-group/basic-constructions/euclidean-two-not-homeomorphic.md" "Euclidean two-space is distinguished by dimension — fully proved"
  click n20 "roadmap/fundamental-group/basic-constructions/fundamental-group-circle.md" "The fundamental group of the circle — fully proved"
  click n21 "roadmap/fundamental-group/basic-constructions/fundamental-group-law.md" "Path concatenation gives the fundamental-group law — fully proved"
  click n22 "roadmap/fundamental-group/basic-constructions/fundamental-theorem-algebra.md" "The fundamental theorem of algebra — fully proved"
  click n23 "roadmap/fundamental-group/basic-constructions/homotopic-maps-fundamental-group.md" "Homotopic maps differ by basepoint change — fully proved"
  click n24 "roadmap/fundamental-group/basic-constructions/homotopy-equivalence-fundamental-group.md" "A homotopy equivalence induces a fundamental-group isomorphism — fully proved"
  click n25 "roadmap/fundamental-group/basic-constructions/loop-in-open-cover.md" "A loop splits across an open cover — fully proved"
  click n26 "roadmap/fundamental-group/basic-constructions/no-retraction-disc.md" "The circle is not a retract of the disc — fully proved"
  click n27 "roadmap/fundamental-group/basic-constructions/path-homotopy-equivalence.md" "Path homotopy is an equivalence relation — in mathlib"
  click n28 "roadmap/fundamental-group/basic-constructions/product-fundamental-group.md" "The fundamental group of a product — fully proved"
  click n29 "roadmap/fundamental-group/basic-constructions/retractions-fundamental-group.md" "Retractions and deformation retracts on the fundamental group — fully proved"
  click n30 "roadmap/fundamental-group/basic-constructions/simply-connected-unique-path-classes.md" "Simply connected spaces have unique path-homotopy classes — in mathlib"
  click n31 "roadmap/fundamental-group/basic-constructions/sphere-simply-connected.md" "Higher spheres are simply connected — fully proved"
  click n32 "roadmap/fundamental-group/basic-constructions/three-closed-sets-antipodal.md" "Three closed sets covering the sphere contain an antipodal pair — fully proved"
  click n33 "roadmap/fundamental-group/basic-constructions/torus-fundamental-group.md" "The fundamental group of the torus — fully proved"
  click n34 "roadmap/fundamental-group/basic-constructions/winding-number.md" "Winding number of a loop in the circle — fully proved"
  click n35 "roadmap/fundamental-group/covering-spaces/README.md" "Covering spaces — 32 items · 4 in mathlib · 28 fully proved"
  click n36 "roadmap/fundamental-group/covering-spaces/based-connected-cover.md" "Pointed connected covering spaces — fully proved"
  click n37 "roadmap/fundamental-group/covering-spaces/closed-lift-image.md" "The induced subgroup consists of loops with closed lifts — fully proved"
  click n38 "roadmap/fundamental-group/covering-spaces/cover-basepoint-conjugacy.md" "Changing the lifted basepoint conjugates the image subgroup — fully proved"
  click n39 "roadmap/fundamental-group/covering-spaces/covering-injective-path-classes.md" "Covering maps inject path-homotopy classes — in mathlib"
  click n40 "roadmap/fundamental-group/covering-spaces/deck-transformations/README.md" "Deck transformations and quotient actions — 8 items · 1 in mathlib · 7 fully proved"
  click n41 "roadmap/fundamental-group/covering-spaces/deck-transformations/covering-space-action.md" "Covering-space actions give quotient coverings — fully proved"
  click n42 "roadmap/fundamental-group/covering-spaces/deck-transformations/deck-group-calculation.md" "The deck group is the normalizer quotient — fully proved"
  click n43 "roadmap/fundamental-group/covering-spaces/deck-transformations/deck-realization.md" "A deck transformation is determined by one lifted point — fully proved"
  click n44 "roadmap/fundamental-group/covering-spaces/deck-transformations/deck-transformation-group.md" "Deck transformations and normal covers — in mathlib"
  click n45 "roadmap/fundamental-group/covering-spaces/deck-transformations/normalizer-to-deck.md" "The normalizer acts by deck transformations — fully proved"
  click n46 "roadmap/fundamental-group/covering-spaces/deck-transformations/normalizer-to-deck-exactness.md" "The normalizer map is surjective with kernel the covering subgroup — fully proved"
  click n47 "roadmap/fundamental-group/covering-spaces/deck-transformations/orbit-quotient-deck-group.md" "Orbit quotients are normal and have the expected deck group — fully proved"
  click n48 "roadmap/fundamental-group/covering-spaces/deck-transformations/orbit-quotient-fundamental-group.md" "The orbit-quotient fundamental group recovers the acting group — fully proved"
  click n49 "roadmap/fundamental-group/covering-spaces/homotopy-lifting.md" "Homotopies lift uniquely through a covering map — fully proved"
  click n50 "roadmap/fundamental-group/covering-spaces/lifting-criterion.md" "A map lifts exactly when its fundamental group lands in the covering subgroup — fully proved"
  click n51 "roadmap/fundamental-group/covering-spaces/locally-path-connected-total-space.md" "Local path-connectedness ascends along a covering — fully proved"
  click n52 "roadmap/fundamental-group/covering-spaces/monodromy-action.md" "The fundamental group acts on a covering fiber — in mathlib"
  click n53 "roadmap/fundamental-group/covering-spaces/pointed-cover-classification.md" "Pointed connected covers are classified by subgroups — fully proved"
  click n54 "roadmap/fundamental-group/covering-spaces/pointed-cover-rigidity.md" "Equal image subgroups characterize pointed cover isomorphism — fully proved"
  click n55 "roadmap/fundamental-group/covering-spaces/sheet-index.md" "Sheets are cosets of the induced subgroup — fully proved"
  click n56 "roadmap/fundamental-group/covering-spaces/subgroup-cover-image.md" "The subgroup cover realizes the chosen subgroup — fully proved"
  click n57 "roadmap/fundamental-group/covering-spaces/subgroup-cover-is-covering.md" "The subgroup projection is a path-connected covering — fully proved"
  click n58 "roadmap/fundamental-group/covering-spaces/subgroup-cover-space.md" "The covering space associated to a subgroup — fully proved"
  click n59 "roadmap/fundamental-group/covering-spaces/unique-lifting.md" "A lift is determined by one point — in mathlib"
  click n60 "roadmap/fundamental-group/covering-spaces/universal-cover/README.md" "The path-class universal cover — 7 items · 7 fully proved"
  click n61 "roadmap/fundamental-group/covering-spaces/universal-cover-initial.md" "A simply-connected cover maps uniquely to every pointed connected cover — fully proved"
  click n62 "roadmap/fundamental-group/covering-spaces/universal-cover/nullhomotopic-open-basis.md" "Small nullhomotopy neighborhoods form a basis — fully proved"
  click n63 "roadmap/fundamental-group/covering-spaces/universal-cover/semilocally-simply-connected.md" "Semilocally simply-connected spaces — fully proved"
  click n64 "roadmap/fundamental-group/covering-spaces/universal-cover/universal-cover-basis.md" "The sets U[γ] form the universal-cover basis — fully proved"
  click n65 "roadmap/fundamental-group/covering-spaces/universal-cover/universal-cover-is-covering.md" "The endpoint map is a covering — fully proved"
  click n66 "roadmap/fundamental-group/covering-spaces/universal-cover/universal-cover-path-connected.md" "The path-class cover is path-connected — fully proved"
  click n67 "roadmap/fundamental-group/covering-spaces/universal-cover/universal-cover-path-space.md" "The path-class universal-cover space — fully proved"
  click n68 "roadmap/fundamental-group/covering-spaces/universal-cover/universal-cover-simply-connected.md" "The path-class cover is simply-connected — fully proved"
  click n69 "roadmap/fundamental-group/covering-spaces/unpointed-cover-classification.md" "Connected covers are classified by conjugacy classes — fully proved"
  click n70 "roadmap/fundamental-group/van-kampen/README.md" "Van Kampen's theorem — 64 items · 64 fully proved"
  click n71 "roadmap/fundamental-group/van-kampen/attach-higher-cells-fundamental-group.md" "Attaching higher cells preserves the fundamental group — fully proved"
  click n72 "roadmap/fundamental-group/van-kampen/attach-two-cells-fundamental-group.md" "Attaching 2-cells adds the attaching relations — fully proved"
  click n73 "roadmap/fundamental-group/van-kampen/attaching-spheres-generate-intersection.md" "The attaching-sphere pieces generate the intersection group — fully proved"
  click n74 "roadmap/fundamental-group/van-kampen/binary-van-kampen-pushout.md" "Binary van Kampen is a group pushout — fully proved"
  click n75 "roadmap/fundamental-group/van-kampen/cell-attachment-cover-model.md" "An open-cover model for attached cells — fully proved"
  click n76 "roadmap/fundamental-group/van-kampen/cell-attachment-support/README.md" "Cell-attachment support — 29 items · 29 fully proved"
  click n77 "roadmap/fundamental-group/van-kampen/cell-attachment-support/abstract-cell-attachment-indexed-model.md" "Every abstract cell attachment has an indexed cone model — fully proved"
  click n78 "roadmap/fundamental-group/van-kampen/cell-attachment-support/auxiliary/README.md" "Hatcher's auxiliary cell-attachment cover — 9 items · 9 fully proved"
  click n79 "roadmap/fundamental-group/van-kampen/cell-attachment-support/auxiliary/auxiliary-attachment-retract.md" "The strip enlargement retracts onto the attached space — fully proved"
  click n80 "roadmap/fundamental-group/van-kampen/cell-attachment-support/auxiliary/auxiliary-base-cover-retract.md" "The base-side auxiliary cover retracts onto the original space — fully proved"
  click n81 "roadmap/fundamental-group/van-kampen/cell-attachment-support/auxiliary/auxiliary-cell-attachment-open-cover.md" "Hatcher's binary cover of the strip enlargement — fully proved"
  click n82 "roadmap/fundamental-group/van-kampen/cell-attachment-support/auxiliary/auxiliary-cell-attachment-space.md" "The strip-enlarged cell-attachment space — fully proved"
  click n83 "roadmap/fundamental-group/van-kampen/cell-attachment-support/auxiliary/auxiliary-cover-basepoint-transport.md" "The auxiliary cover basepoint transports to the original basepoint — fully proved"
  click n84 "roadmap/fundamental-group/van-kampen/cell-attachment-support/auxiliary/auxiliary-overlap-attaching-map.md" "Overlap meridians recover the attaching loops — fully proved"
  click n85 "roadmap/fundamental-group/van-kampen/cell-attachment-support/auxiliary/auxiliary-overlap-open-cover.md" "The auxiliary overlap has an indexed open cover — fully proved"
  click n86 "roadmap/fundamental-group/van-kampen/cell-attachment-support/auxiliary/auxiliary-overlap-piece-sphere.md" "Each overlap piece has the homotopy type of its attaching sphere — fully proved"
  click n87 "roadmap/fundamental-group/van-kampen/cell-attachment-support/auxiliary/auxiliary-upper-cover-contractible.md" "The strip-connected upper cover is contractible — fully proved"
  click n88 "roadmap/fundamental-group/van-kampen/cell-attachment-support/binary-cover-contractible-piece.md" "A binary cover with a contractible second piece — fully proved"
  click n89 "roadmap/fundamental-group/van-kampen/cell-attachment-support/binary-cover-trivial-piece-quotient.md" "A binary cover with a trivial second fundamental group — fully proved"
  click n90 "roadmap/fundamental-group/van-kampen/cell-attachment-support/circle-degree-map.md" "The degree-n circle map sends the generator to the degree-n loop — fully proved"
  click n91 "roadmap/fundamental-group/van-kampen/cell-attachment-support/circle-well-pointed.md" "The circle is well-pointed at one — fully proved"
  click n92 "roadmap/fundamental-group/van-kampen/cell-attachment-support/cone-disk-homeomorphism.md" "The cone on a disk boundary is the disk — fully proved"
  click n93 "roadmap/fundamental-group/van-kampen/cell-attachment-support/cyclic-relation-quotient.md" "The degree-n circle relation gives the cyclic group — fully proved"
  click n94 "roadmap/fundamental-group/van-kampen/cell-attachment-support/disk-boundary-two-circle.md" "The boundary of the two-disk is the circle — fully proved"
  click n95 "roadmap/fundamental-group/van-kampen/cell-attachment-support/empty-cell-attachment-iso.md" "An attachment with no cells is an isomorphism — fully proved"
  click n96 "roadmap/fundamental-group/van-kampen/cell-attachment-support/higher-cell-attachment-path-components.md" "Higher-cell attachments preserve path components — fully proved"
  click n97 "roadmap/fundamental-group/van-kampen/cell-attachment-support/indexed-basic-cell-attachment.md" "An indexed cone attachment is a standard cell attachment — fully proved"
  click n98 "roadmap/fundamental-group/van-kampen/cell-attachment-support/indexed-cone-open-cover.md" "An indexed family of cones has a two-set open cover — fully proved"
  click n99 "roadmap/fundamental-group/van-kampen/cell-attachment-support/indexed-cone-pushout.md" "An indexed family of cone attachments is a topological pushout — fully proved"
  click n100 "roadmap/fundamental-group/van-kampen/cell-attachment-support/path-connected-two-skeleton.md" "The 2-skeleton of a path-connected CW complex is path-connected — fully proved"
  click n101 "roadmap/fundamental-group/van-kampen/cell-attachment-support/single-basic-cell-attachment.md" "A single cone attachment is a standard cell attachment — fully proved"
  click n102 "roadmap/fundamental-group/van-kampen/cell-attachment-support/single-cone-base-retract.md" "The base-side cone cover retracts onto the original space — fully proved"
  click n103 "roadmap/fundamental-group/van-kampen/cell-attachment-support/single-cone-intersection.md" "The single-cone cover intersection has the homotopy type of its boundary — fully proved"
  click n104 "roadmap/fundamental-group/van-kampen/cell-attachment-support/single-cone-open-cover.md" "A single cone attachment has a two-set open cover — fully proved"
  click n105 "roadmap/fundamental-group/van-kampen/cell-attachment-support/single-cone-pushout.md" "A single cone attachment is a topological pushout — fully proved"
  click n106 "roadmap/fundamental-group/van-kampen/cell-attachment-support/single-cone-upper-contractible.md" "The cone-side cover member is contractible — fully proved"
  click n107 "roadmap/fundamental-group/van-kampen/cover-factorization.md" "Cover factorizations of a loop — fully proved"
  click n108 "roadmap/fundamental-group/van-kampen/cover-group-presentation.md" "The group presentation associated to an open cover — fully proved"
  click n109 "roadmap/fundamental-group/van-kampen/cover-map-relations.md" "Overlap relations vanish under the cover map — fully proved"
  click n110 "roadmap/fundamental-group/van-kampen/every-group-fundamental-group.md" "Every group is a fundamental group — fully proved"
  click n111 "roadmap/fundamental-group/van-kampen/every-group-presentation.md" "Every group admits a generators-and-relations presentation — fully proved"
  click n112 "roadmap/fundamental-group/van-kampen/factorization-moves.md" "Elementary factorization moves preserve the quotient class — fully proved"
  click n113 "roadmap/fundamental-group/van-kampen/finite-skeleton-fundamental-group.md" "Finite skeleta above dimension two have the same fundamental group — fully proved"
  click n114 "roadmap/fundamental-group/van-kampen/homotopic-factorizations.md" "Homotopic factorizations have the same quotient class — fully proved"
  click n115 "roadmap/fundamental-group/van-kampen/homotopy-cover-decomposition.md" "A homotopy admits a threefold-incidence cover decomposition — fully proved"
  click n116 "roadmap/fundamental-group/van-kampen/pointed-wedge.md" "The pointed wedge of a family of spaces — fully proved"
  click n117 "roadmap/fundamental-group/van-kampen/presentation-complex/README.md" "Presentation-complex support — 13 items · 13 fully proved"
  click n118 "roadmap/fundamental-group/van-kampen/presentation-complex/circle-one-cell-quotient.md" "Collapsing the boundary of a one-disk gives the circle — fully proved"
  click n119 "roadmap/fundamental-group/van-kampen/presentation-complex/cyclic-presentation-complex.md" "The cyclic presentation complex — fully proved"
  click n120 "roadmap/fundamental-group/van-kampen/presentation-complex/disk-boundary-fundamental-group-representative.md" "Every fundamental-group element has a based disk-boundary representative — fully proved"
  click n121 "roadmap/fundamental-group/van-kampen/presentation-complex/empty-cell-attachment-constructor.md" "The identity attaches an empty family of cells — fully proved"
  click n122 "roadmap/fundamental-group/van-kampen/presentation-complex/eventually-constant-cell-sequence.md" "Eventually constant cell sequences form abstract CW complexes — fully proved"
  click n123 "roadmap/fundamental-group/van-kampen/presentation-complex/point-zero-cell-attachment.md" "A point is one standard zero-cell — fully proved"
  click n124 "roadmap/fundamental-group/van-kampen/presentation-complex/pointed-wedge-path-connected.md" "Pointed wedges of path-connected spaces are path-connected — fully proved"
  click n125 "roadmap/fundamental-group/van-kampen/presentation-complex/pointed-wedge-universal-property.md" "Continuous maps out of a pointed wedge — fully proved"
  click n126 "roadmap/fundamental-group/van-kampen/presentation-complex/presentation-complex-cw-structure.md" "The presentation complex is an abstract two-dimensional CW complex — fully proved"
  click n127 "roadmap/fundamental-group/van-kampen/presentation-complex/presentation-complex-fundamental-group.md" "The presentation complex has the presented fundamental group — fully proved"
  click n128 "roadmap/fundamental-group/van-kampen/presentation-complex/presentation-complex-realization.md" "Presented groups have two-dimensional presentation complexes — fully proved"
  click n129 "roadmap/fundamental-group/van-kampen/presentation-complex/relator-cell-attachment.md" "Free-group relators form a standard two-cell attachment — fully proved"
  click n130 "roadmap/fundamental-group/van-kampen/presentation-complex/wedge-circles-one-skeleton.md" "A wedge of circles is an indexed one-cell attachment — fully proved"
  click n131 "roadmap/fundamental-group/van-kampen/two-skeleton-fundamental-group.md" "The 2-skeleton determines the fundamental group — fully proved"
  click n132 "roadmap/fundamental-group/van-kampen/van-kampen-kernel.md" "The kernel is generated by overlap relations — fully proved"
  click n133 "roadmap/fundamental-group/van-kampen/van-kampen-quotient.md" "Van Kampen's quotient isomorphism — fully proved"
  click n134 "roadmap/fundamental-group/van-kampen/van-kampen-surjective.md" "The van Kampen cover map is surjective — fully proved"
  click n135 "roadmap/fundamental-group/van-kampen/wedge-circles-free-group.md" "The fundamental group of a wedge of circles — fully proved"
  click n136 "roadmap/fundamental-group/van-kampen/wedge-fundamental-group.md" "The fundamental group of a wedge — fully proved"
  click n137 "roadmap/fundamental-group/van-kampen/well-pointed-wedge-cover.md" "The standard cover of a well-pointed wedge — fully proved"
  click n138 "roadmap/homology/README.md" "Homology — 146 items · 10 in mathlib · 126 fully proved · 3 ready to state · 1 not ready · 6 planned"
  click n139 "roadmap/homology/computations-and-applications/README.md" "Computations and applications — 90 items · 81 fully proved · 3 ready to state · 6 planned"
  click n140 "roadmap/homology/computations-and-applications/degree/README.md" "Degree foundations and applications — 16 items · 16 fully proved"
  click n141 "roadmap/homology/computations-and-applications/degree/antipodal-degree.md" "The antipodal map has degree determined by dimension — fully proved"
  click n142 "roadmap/homology/computations-and-applications/degree/basic-degree-properties.md" "The formal properties of degree — fully proved"
  click n143 "roadmap/homology/computations-and-applications/degree/coordinate-reflection-degree.md" "A sphere reflection has degree minus one — fully proved"
  click n144 "roadmap/homology/computations-and-applications/degree/double-simplex-swap-class.md" "Swapping the double simplex negates its fundamental class — fully proved"
  click n145 "roadmap/homology/computations-and-applications/degree/fixed-point-free-degree.md" "A fixed-point-free sphere map has antipodal degree — fully proved"
  click n146 "roadmap/homology/computations-and-applications/degree/free-even-sphere-action.md" "Only the antipodal group acts freely on an even sphere — fully proved"
  click n147 "roadmap/homology/computations-and-applications/degree/integral-sphere-orientation.md" "The ordered class orients ordinary sphere homology — fully proved"
  click n148 "roadmap/homology/computations-and-applications/degree/nonsurjective-degree-zero.md" "A nonsurjective sphere map has degree zero — fully proved"
  click n149 "roadmap/homology/computations-and-applications/degree/nonzero-tangent-field-iff-odd.md" "A sphere has a nonvanishing tangent field exactly in odd dimension — fully proved"
  click n150 "roadmap/homology/computations-and-applications/degree/odd-sphere-tangent-field.md" "Odd spheres have a nonvanishing tangent field — fully proved"
  click n151 "roadmap/homology/computations-and-applications/degree/punctured-sphere-stereographic.md" "A punctured sphere is Euclidean space — fully proved"
  click n152 "roadmap/homology/computations-and-applications/degree/sphere-action-degree-character.md" "Degree gives a character of a sphere action — fully proved"
  click n153 "roadmap/homology/computations-and-applications/degree/sphere-coordinate-sign-changes.md" "Coordinate sign changes on the sphere — fully proved"
  click n154 "roadmap/homology/computations-and-applications/degree/sphere-degree-definition.md" "Degree is the multiplier of the ordered sphere class — fully proved"
  click n155 "roadmap/homology/computations-and-applications/degree/tangent-field-parity-obstruction.md" "A nonvanishing tangent field forces odd dimension — fully proved"
  click n156 "roadmap/homology/computations-and-applications/degree/tangent-vector-field-data.md" "Tangent vector fields and normalization — fully proved"
  click n157 "roadmap/homology/computations-and-applications/local-degree/README.md" "Local degree and the sum over a finite fiber — 20 items · 11 fully proved · 3 ready to state · 6 planned"
  click n158 "roadmap/homology/computations-and-applications/local-degree/degree-local-sum-formula.md" "Degree is the sum of the local degrees — planned"
  click n159 "roadmap/homology/computations-and-applications/local-degree/deleted-pair-open-neighborhood.md" "Deleted-pair homology is local on an open neighborhood — fully proved"
  click n160 "roadmap/homology/computations-and-applications/local-degree/disjoint-open-union-homeomorphism.md" "A disjoint open family is homeomorphic to its sigma type — fully proved"
  click n161 "roadmap/homology/computations-and-applications/local-degree/disjoint-punctured-pair-iso.md" "Disjoint punctured neighborhoods form the deleted union pair — fully proved"
  click n162 "roadmap/homology/computations-and-applications/local-degree/finite-fiber-local-map.md" "The finite-fiber pair map acts by the local degrees — planned"
  click n163 "roadmap/homology/computations-and-applications/local-degree/finite-fiber-neighborhoods.md" "A finite sphere-map fiber has disjoint isolated neighborhoods — fully proved"
  click n164 "roadmap/homology/computations-and-applications/local-degree/finite-puncture-homology-coproduct.md" "Finite-puncture homology is the coproduct of the local groups — planned"
  click n165 "roadmap/homology/computations-and-applications/local-degree/finite-puncture-orientation-sum.md" "The finite-puncture class is the sum of the local classes — planned"
  click n166 "roadmap/homology/computations-and-applications/local-degree/finite-puncture-pair-excision.md" "The disjoint local pairs excise to the finite-puncture pair — ready to state"
  click n167 "roadmap/homology/computations-and-applications/local-degree/finite-puncture-projection-matrix.md" "Finite-puncture projections have the diagonal matrix — planned"
  click n168 "roadmap/homology/computations-and-applications/local-degree/global-degree-fiber-square.md" "The finite-fiber pair map carries the global degree — fully proved"
  click n169 "roadmap/homology/computations-and-applications/local-degree/homeomorphism-local-degree.md" "A local homeomorphism has local degree plus or minus one — ready to state"
  click n170 "roadmap/homology/computations-and-applications/local-degree/isolated-preimage-neighborhood.md" "An isolated preimage gives a map of punctured pairs — fully proved"
  click n171 "roadmap/homology/computations-and-applications/local-degree/local-degree-shrinking.md" "Local degree is unchanged when the neighborhood shrinks — fully proved"
  click n172 "roadmap/homology/computations-and-applications/local-degree/local-degree-well-defined.md" "Local degree is independent of its neighborhood — fully proved"
  click n173 "roadmap/homology/computations-and-applications/local-degree/neighborhood-local-degree.md" "Local degree on a chosen isolated neighborhood — fully proved"
  click n174 "roadmap/homology/computations-and-applications/local-degree/relative-chains-sigma-pair.md" "Relative chains commute with coproducts of arbitrary pairs — ready to state"
  click n175 "roadmap/homology/computations-and-applications/local-degree/relative-homology-sigma-pair.md" "Relative homology commutes with coproducts of arbitrary pairs — planned"
  click n176 "roadmap/homology/computations-and-applications/local-degree/sigma-topological-pair.md" "The coproduct of a family of topological pairs — fully proved"
  click n177 "roadmap/homology/computations-and-applications/local-degree/sphere-local-orientation.md" "The ordered sphere class orients local homology — fully proved"
  click n178 "roadmap/homology/computations-and-applications/local-homology-and-dimension/README.md" "Local homology and invariance of dimension — 4 items · 4 fully proved"
  click n179 "roadmap/homology/computations-and-applications/local-homology-and-dimension/contractible-ambient-relative-homology.md" "Relative homology in a contractible ambient space — fully proved"
  click n180 "roadmap/homology/computations-and-applications/local-homology-and-dimension/invariance-of-dimension-open-sets.md" "Homeomorphic nonempty Euclidean open sets have equal dimension — fully proved"
  click n181 "roadmap/homology/computations-and-applications/local-homology-and-dimension/local-homology-open-neighborhood.md" "Local homology is unchanged on an open neighborhood — fully proved"
  click n182 "roadmap/homology/computations-and-applications/local-homology-and-dimension/punctured-euclidean-local-homology.md" "Local homology of positive-dimensional Euclidean space — fully proved"
  click n183 "roadmap/homology/computations-and-applications/mayer-vietoris/README.md" "Mayer–Vietoris sequences — 6 items · 6 fully proved"
  click n184 "roadmap/homology/computations-and-applications/mayer-vietoris/augmented-binary-cover-chain-short-exact-sequence.md" "Augmented binary-cover chains form a short exact sequence — fully proved"
  click n185 "roadmap/homology/computations-and-applications/mayer-vietoris/binary-cover-chain-complex.md" "The binary-cover Mayer–Vietoris chain complex — fully proved"
  click n186 "roadmap/homology/computations-and-applications/mayer-vietoris/binary-cover-chain-short-exact-sequence.md" "Binary-cover chains form a short exact sequence — fully proved"
  click n187 "roadmap/homology/computations-and-applications/mayer-vietoris/binary-cover-mayer-vietoris-sequence.md" "The binary-cover Mayer–Vietoris sequence — fully proved"
  click n188 "roadmap/homology/computations-and-applications/mayer-vietoris/reduced-binary-cover-mayer-vietoris-sequence.md" "The reduced binary-cover Mayer–Vietoris sequence — fully proved"
  click n189 "roadmap/homology/computations-and-applications/mayer-vietoris/small-augmented-chain-inclusion-homotopy-equivalence.md" "Small augmented chains include by a chain-homotopy equivalence — fully proved"
  click n190 "roadmap/homology/computations-and-applications/post-excision-applications/README.md" "Post-excision applications — 28 items · 28 fully proved"
  click n191 "roadmap/homology/computations-and-applications/post-excision-applications/contractible-subspace-relative-reduced-homology.md" "A contractible subspace identifies reduced and relative homology — fully proved"
  click n192 "roadmap/homology/computations-and-applications/post-excision-applications/cw-subcomplex-excision.md" "Excision holds for a union of CW subcomplexes — fully proved"
  click n193 "roadmap/homology/computations-and-applications/post-excision-applications/cw-subcomplex-neighborhood/README.md" "CW-subcomplex regular neighborhoods — 5 items · 5 fully proved"
  click n194 "roadmap/homology/computations-and-applications/post-excision-applications/cw-subcomplex-neighborhood/cell-boundary-collar.md" "The radial collar of a cell boundary — fully proved"
  click n195 "roadmap/homology/computations-and-applications/post-excision-applications/cw-subcomplex-neighborhood/regular-neighborhood-strong-deformation-retract.md" "A regular neighborhood strongly deformation retracts onto its subcomplex — fully proved"
  click n196 "roadmap/homology/computations-and-applications/post-excision-applications/cw-subcomplex-neighborhood/regular-neighborhood-system.md" "A common regular-neighborhood system for subcomplexes — fully proved"
  click n197 "roadmap/homology/computations-and-applications/post-excision-applications/cw-subcomplex-neighborhood/subcomplex-intersection.md" "Intersections of CW subcomplexes — fully proved"
  click n198 "roadmap/homology/computations-and-applications/post-excision-applications/cw-subcomplex-neighborhood/subcomplex-neighborhood-cover.md" "Subcomplex decompositions admit compatible neighborhoods — fully proved"
  click n199 "roadmap/homology/computations-and-applications/post-excision-applications/double-simplex-fundamental-class.md" "The double-simplex difference generates reduced homology — fully proved"
  click n200 "roadmap/homology/computations-and-applications/post-excision-applications/double-simplex-fundamental-cycle.md" "The ordered difference of the two simplices is a cycle — fully proved"
  click n201 "roadmap/homology/computations-and-applications/post-excision-applications/double-simplex-relative-comparison.md" "The first simplex computes homology relative to the second — fully proved"
  click n202 "roadmap/homology/computations-and-applications/post-excision-applications/double-simplex-sphere-homeomorphism.md" "The double simplex is a sphere — fully proved"
  click n203 "roadmap/homology/computations-and-applications/post-excision-applications/mapping-cone-cover-relative-homology.md" "The mapping-cone cover has the relative homology of the original pair — fully proved"
  click n204 "roadmap/homology/computations-and-applications/post-excision-applications/mapping-cone-model.md" "The mapping cone of a topological pair — fully proved"
  click n205 "roadmap/homology/computations-and-applications/post-excision-applications/mapping-cone-relative-reduced-homology.md" "Relative homology is reduced homology of the mapping cone — fully proved"
  click n206 "roadmap/homology/computations-and-applications/post-excision-applications/pointed-wedge-point-quotient.md" "The pointed wedge is the point quotient of the sigma pair — fully proved"
  click n207 "roadmap/homology/computations-and-applications/post-excision-applications/relative-homology-coproduct.md" "Relative homology commutes with exact coproducts — fully proved"
  click n208 "roadmap/homology/computations-and-applications/post-excision-applications/relative-simplex-fundamental-class.md" "The identity simplex generates relative simplex homology — fully proved"
  click n209 "roadmap/homology/computations-and-applications/post-excision-applications/sigma-good-pair.md" "A nonempty coproduct of pointed good pairs is good — fully proved"
  click n210 "roadmap/homology/computations-and-applications/post-excision-applications/sigma-pointed-pair.md" "The coproduct pair of a family of pointed spaces — fully proved"
  click n211 "roadmap/homology/computations-and-applications/post-excision-applications/singular-relative-chains-coproduct.md" "Relative singular chains commute with topological coproducts — fully proved"
  click n212 "roadmap/homology/computations-and-applications/post-excision-applications/standard-simplex-boundary-good-pairs.md" "Standard-simplex boundary and horn pairs are good — fully proved"
  click n213 "roadmap/homology/computations-and-applications/post-excision-applications/standard-simplex-boundary-horn.md" "The boundary and zero horn of a standard topological simplex — fully proved"
  click n214 "roadmap/homology/computations-and-applications/post-excision-applications/standard-simplex-disk-pair-homeomorphism.md" "The standard simplex pair is homeomorphic to the disk pair — fully proved"
  click n215 "roadmap/homology/computations-and-applications/post-excision-applications/standard-simplex-zero-face-point-quotient.md" "The zero face identifies the two simplex point quotients — fully proved"
  click n216 "roadmap/homology/computations-and-applications/post-excision-applications/standard-simplex-zero-face-relative-homology.md" "The zero face induces an isomorphism in relative homology — fully proved"
  click n217 "roadmap/homology/computations-and-applications/post-excision-applications/standard-simplex-zero-horn-retraction.md" "A standard simplex strongly deformation retracts onto its zero horn — fully proved"
  click n218 "roadmap/homology/computations-and-applications/post-excision-applications/triple-connecting-cycle-formula.md" "The triple connecting map sends a relative cycle to its boundary — fully proved"
  click n219 "roadmap/homology/computations-and-applications/post-excision-applications/wedge-reduced-homology.md" "Reduced homology of a wedge is the direct sum of the summands — fully proved"
  click n220 "roadmap/homology/computations-and-applications/sphere-homology/README.md" "Mayer–Vietoris transport, sphere homology, and Brouwer — 16 items · 16 fully proved"
  click n221 "roadmap/homology/computations-and-applications/sphere-homology/brouwer-fixed-point-disk.md" "Brouwer's fixed-point theorem for disks — fully proved"
  click n222 "roadmap/homology/computations-and-applications/sphere-homology/closed-ball-radial-deformation-retract.md" "A closed ball strongly deformation retracts from Euclidean space — fully proved"
  click n223 "roadmap/homology/computations-and-applications/sphere-homology/contractible-space-reduced-homology.md" "Reduced homology of a contractible space vanishes — fully proved"
  click n224 "roadmap/homology/computations-and-applications/sphere-homology/disk-boundary-no-retraction.md" "The boundary sphere is not a retract of the disk — fully proved"
  click n225 "roadmap/homology/computations-and-applications/sphere-homology/fixed-point-free-disk-map-retraction.md" "A fixed-point-free disk map produces a boundary retraction — fully proved"
  click n226 "roadmap/homology/computations-and-applications/sphere-homology/homotopy-equivalence-reduced-homology-iso.md" "A homotopy equivalence induces reduced-homology isomorphisms — fully proved"
  click n227 "roadmap/homology/computations-and-applications/sphere-homology/ordinary-neighborhood-mayer-vietoris.md" "The ordinary neighborhood-retract Mayer–Vietoris sequence — fully proved"
  click n228 "roadmap/homology/computations-and-applications/sphere-homology/punctured-space-radial-deformation-retract.md" "A sphere strongly deformation retracts from punctured Euclidean space — fully proved"
  click n229 "roadmap/homology/computations-and-applications/sphere-homology/reduced-homology-homotopy-invariance.md" "Homotopic maps induce the same reduced-homology map — fully proved"
  click n230 "roadmap/homology/computations-and-applications/sphere-homology/reduced-neighborhood-mayer-vietoris.md" "The reduced neighborhood-retract Mayer–Vietoris sequence — fully proved"
  click n231 "roadmap/homology/computations-and-applications/sphere-homology/sphere-hemisphere-neighborhood-cover.md" "The hemispheres have compatible neighborhood deformation retractions — fully proved"
  click n232 "roadmap/homology/computations-and-applications/sphere-homology/sphere-hemisphere-stereographic-models.md" "Stereographic models for hemispheres and the equator — fully proved"
  click n233 "roadmap/homology/computations-and-applications/sphere-homology/sphere-reduced-homology.md" "Reduced homology of spheres — fully proved"
  click n234 "roadmap/homology/computations-and-applications/sphere-homology/sphere-reduced-homology-recurrence.md" "The reduced homology of spheres satisfies the suspension recurrence — fully proved"
  click n235 "roadmap/homology/computations-and-applications/sphere-homology/zero-sphere-reduced-homology.md" "Reduced homology of the zero-sphere — fully proved"
  click n236 "roadmap/homology/computations-and-applications/sphere-homology/zero-sphere-two-point-homeomorphism.md" "The zero-sphere is a two-point space — fully proved"
  click n237 "roadmap/homology/formal-viewpoint/README.md" "The formal viewpoint — not ready"
  click n238 "roadmap/homology/simplicial-and-singular/README.md" "Simplicial and singular homology — 55 items · 10 in mathlib · 45 fully proved"
  click n239 "roadmap/homology/simplicial-and-singular/chain-homotopy-invariance.md" "Chain-homotopic maps induce the same homology map — in mathlib"
  click n240 "roadmap/homology/simplicial-and-singular/chain-map-homology.md" "A chain map induces a map on homology — in mathlib"
  click n241 "roadmap/homology/simplicial-and-singular/homotopy-equivalence-homology-iso.md" "A homotopy equivalence induces homology isomorphisms — fully proved"
  click n242 "roadmap/homology/simplicial-and-singular/point-homology.md" "Homology of a point — fully proved"
  click n243 "roadmap/homology/simplicial-and-singular/relative-homology/README.md" "Relative homology and exact sequences — 45 items · 2 in mathlib · 43 fully proved"
  click n244 "roadmap/homology/simplicial-and-singular/relative-homology/augmented-singular-chain-complex.md" "The augmented singular chain complex — fully proved"
  click n245 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/README.md" "Good pairs and quotient exact sequences — 16 items · 16 fully proved"
  click n246 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-data.md" "Good pairs and neighborhood deformation retracts — fully proved"
  click n247 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-excision-diagram.md" "The complementary excision diagram — fully proved"
  click n248 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-neighborhood-quotient.md" "Restricting the quotient to a good-pair neighborhood — fully proved"
  click n249 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-neighborhood-relative-homology.md" "Enlarging to the chosen neighborhood preserves relative homology — fully proved"
  click n250 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-point-quotient-exact-sequence.md" "The good-pair quotient exact sequence — fully proved"
  click n251 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-point-quotient-relative-homology.md" "Good-pair relative homology is reduced quotient homology — fully proved"
  click n252 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-point-quotient-sequence-naturality.md" "Naturality of the good-pair quotient sequence — fully proved"
  click n253 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-quotient-comparison-naturality.md" "The good-pair quotient comparison is natural — fully proved"
  click n254 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/point-quotient-functor.md" "Functorial point quotients of topological pairs — fully proved"
  click n255 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/point-quotient-neighborhood-contraction.md" "The quotient neighborhood contracts to its point — fully proved"
  click n256 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/point-quotient-neighborhood-excision.md" "The neighborhood quotient map preserves relative homology — fully proved"
  click n257 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/point-quotient-neighborhood-relative-homology.md" "Enlarging the quotient point preserves relative homology — fully proved"
  click n258 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/point-quotient-projection-topology.md" "Topology of the point-quotient projection — fully proved"
  click n259 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/pointed-relative-reduced-homology-naturality.md" "The pointed relative-to-reduced comparison is natural — fully proved"
  click n260 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/relative-homology-map-isomorphism-criterion.md" "Componentwise isomorphisms imply a relative isomorphism — fully proved"
  click n261 "roadmap/homology/simplicial-and-singular/relative-homology/good-pair-quotient/strong-deformation-retract.md" "Strong deformation retracts — fully proved"
  click n262 "roadmap/homology/simplicial-and-singular/relative-homology/pair-long-exact-sequence.md" "The long exact sequence of a pair — fully proved"
  click n263 "roadmap/homology/simplicial-and-singular/relative-homology/pair-long-exact-sequence-naturality.md" "The pair long exact sequence is natural — fully proved"
  click n264 "roadmap/homology/simplicial-and-singular/relative-homology/pointed-relative-reduced-homology.md" "Relative homology at a basepoint is reduced homology — fully proved"
  click n265 "roadmap/homology/simplicial-and-singular/relative-homology/pointed-zeroth-homology-splitting.md" "Zeroth homology splits into reduced homology and the coefficient object — fully proved"
  click n266 "roadmap/homology/simplicial-and-singular/relative-homology/reduced-pair-long-exact-sequence.md" "The reduced long exact sequence of a nonempty pair — fully proved"
  click n267 "roadmap/homology/simplicial-and-singular/relative-homology/reduced-pair-long-exact-sequence-naturality.md" "The reduced pair long exact sequence is natural — fully proved"
  click n268 "roadmap/homology/simplicial-and-singular/relative-homology/reduced-positive-degree-comparison.md" "Reduced and ordinary homology agree in positive degrees — fully proved"
  click n269 "roadmap/homology/simplicial-and-singular/relative-homology/reduced-singular-homology.md" "Reduced singular homology — fully proved"
  click n270 "roadmap/homology/simplicial-and-singular/relative-homology/relative-homology-homotopy-invariance.md" "Homotopic maps of pairs induce the same relative-homology map — fully proved"
  click n271 "roadmap/homology/simplicial-and-singular/relative-homology/relative-singular-chain-homotopy.md" "A homotopy of pairs gives a relative chain homotopy — fully proved"
  click n272 "roadmap/homology/simplicial-and-singular/relative-homology/relative-singular-homology.md" "Relative singular chains and homology — fully proved"
  click n273 "roadmap/homology/simplicial-and-singular/relative-homology/short-exact-homology-sequence.md" "A short exact sequence gives an exact homology sequence — in mathlib"
  click n274 "roadmap/homology/simplicial-and-singular/relative-homology/simplicial-pair-relative-homology.md" "Relative homology of a simplicial-set pair — in mathlib"
  click n275 "roadmap/homology/simplicial-and-singular/relative-homology/singular-pair-functor.md" "The singular set of a topological pair — fully proved"
  click n276 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/README.md" "Small chains and excision — 10 items · 10 fully proved"
  click n277 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/affine-barycentric-subdivision.md" "Affine barycentric subdivision is compatible with faces — fully proved"
  click n278 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/affine-chain-subdivision-homotopy.md" "Affine-chain subdivision is homotopic to the identity — fully proved"
  click n279 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/barycentric-subdivision-diameter.md" "Barycentric subdivision contracts simplex diameter — fully proved"
  click n280 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/binary-cover-excision-chain-equivalence.md" "The binary-cover excision chain map is a homotopy equivalence — fully proved"
  click n281 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/binary-cover-excision-homology-isomorphism.md" "Binary-cover excision induces homology isomorphisms — fully proved"
  click n282 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/deleted-subset-excision-homology-isomorphism.md" "Deleted-subset excision induces homology isomorphisms — fully proved"
  click n283 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/eventually-small-singular-simplices.md" "Iterated subdivision eventually makes every singular simplex small — fully proved"
  click n284 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/relative-chain-union-devissage.md" "Relative excision reduces to the union subcomplex — fully proved"
  click n285 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/singular-chain-subdivision-homotopy.md" "Singular-chain subdivision is naturally homotopic to the identity — fully proved"
  click n286 "roadmap/homology/simplicial-and-singular/relative-homology/small-chains-and-excision/small-chain-inclusion-homotopy-equivalence.md" "Small singular chains include by a chain-homotopy equivalence — fully proved"
  click n287 "roadmap/homology/simplicial-and-singular/relative-homology/topological-triple.md" "Topological triples and their maps — fully proved"
  click n288 "roadmap/homology/simplicial-and-singular/relative-homology/triple-chain-short-exact-sequence.md" "Relative chains of a triple form a short exact sequence — fully proved"
  click n289 "roadmap/homology/simplicial-and-singular/relative-homology/triple-long-exact-sequence.md" "The long exact sequence of a triple — fully proved"
  click n290 "roadmap/homology/simplicial-and-singular/relative-homology/triple-long-exact-sequence-naturality.md" "The triple long exact sequence is natural — fully proved"
  click n291 "roadmap/homology/simplicial-and-singular/singular-chain-complex.md" "The singular chain complex — in mathlib"
  click n292 "roadmap/homology/simplicial-and-singular/singular-homology.md" "Singular homology — in mathlib"
  click n293 "roadmap/homology/simplicial-and-singular/singular-homology-homotopy-invariance.md" "Homotopic maps induce the same singular-homology map — in mathlib"
  click n294 "roadmap/homology/simplicial-and-singular/topological-homotopy-chain-homotopy.md" "A topological homotopy gives a singular-chain homotopy — in mathlib"
  click n295 "roadmap/homology/simplicial-and-singular/totally-disconnected-higher-homology.md" "Higher homology vanishes for totally disconnected spaces — in mathlib"
  click n296 "roadmap/homology/simplicial-and-singular/zeroth-homology-components.md" "Zeroth homology is free on path components — in mathlib"
  click n297 "roadmap/homotopy-theory/README.md" "Homotopy theory — 3 items · 3 not ready"
  click n298 "roadmap/homotopy-theory/connections-with-cohomology/README.md" "Connections with cohomology — not ready"
  click n299 "roadmap/homotopy-theory/elementary-methods/README.md" "Elementary methods of calculation — not ready"
  click n300 "roadmap/homotopy-theory/homotopy-groups/README.md" "Homotopy groups — not ready"
  click n301 "roadmap/README.md" "Algebraic Topology (Hatcher) roadmap — 276 items · 18 in mathlib · 241 fully proved · 3 ready to state · 8 not ready · 6 planned"
  click n302 "roadmap/underlying-geometric-notions/README.md" "Some underlying geometric notions — not ready"
  classDef mathlib fill:#1C5C33,stroke:#134426,color:#FFFFFF,stroke-width:2px
  classDef fully_proved fill:#31A24C,stroke:#22773A,color:#FFFFFF,stroke-width:2px
  classDef proved fill:#8ED4A2,stroke:#22773A,color:#0B2415,stroke-width:2px
  classDef defined fill:#C3E9CE,stroke:#22773A,color:#0B2415,stroke-width:2px
  classDef conditional fill:#E9DFFC,stroke:#6B3FCF,color:#2E1065,stroke-width:2px
  classDef can_prove fill:#FFFFFF,stroke:#0064E0,color:#0064E0,stroke-width:2px
  classDef stated fill:#FFFFFF,stroke:#31A24C,color:#22773A,stroke-width:2px
  classDef can_state fill:#FFFFFF,stroke:#0082FB,color:#0B4EA2,stroke-width:2px
  classDef not_ready fill:#FFF3D6,stroke:#B77900,color:#5C3D00,stroke-width:2px
  classDef planned fill:#FFFFFF,stroke:#CED0D4,color:#65676B,stroke-width:2px
  classDef scope fill:#EBF2FE,stroke:#0064E0,color:#050505,stroke-width:2px
  classDef scope_complete fill:#31A24C,stroke:#22773A,color:#FFFFFF,stroke-width:2px
  classDef boundary fill:#FFFFFF,stroke:#8A8D91,color:#65676B,stroke-width:2px,stroke-dasharray:5 3
  classDef focus stroke:#F7B928,stroke-width:4px
```

## Legend

<div class="bp-legend-grid"><span class="bp-swatch bp-swatch-mathlib"></span><span class="bp-legend-label">in mathlib</span><span class="bp-legend-count">18</span><span class="bp-legend-meaning">Upstreamed into Mathlib.</span><span class="bp-swatch bp-swatch-fully_proved"></span><span class="bp-legend-label">fully proved</span><span class="bp-legend-count">241</span><span class="bp-legend-meaning">Proved, and every prerequisite is fully proved too.</span><span class="bp-swatch bp-swatch-can_state"></span><span class="bp-legend-label">ready to state</span><span class="bp-legend-count">3</span><span class="bp-legend-meaning">Nothing it needs is blocked, so the statement can be written in Lean.</span><span class="bp-swatch bp-swatch-not_ready"></span><span class="bp-legend-label">not ready</span><span class="bp-legend-count">8</span><span class="bp-legend-meaning">Needs more blueprint work before it can be attempted.</span><span class="bp-swatch bp-swatch-planned"></span><span class="bp-legend-label">planned</span><span class="bp-legend-count">6</span><span class="bp-legend-meaning">Described in the blueprint only.</span></div>
