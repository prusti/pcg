# PCG SVG

This crate lays out directed hypergraphs and renders standalone SVG using Rust.
It has no dependency on rustc, Graphviz, a browser, or a JavaScript runtime.

`Hypergraph` contains nodes and hyperedges with explicit source and target sets.
`Hypergraph::layout` returns node boxes, endpoint enclosures, branches, edge paths,
and label boxes. `Hypergraph::to_svg` also renders the drawing. Node identifiers
are indices into the node vector. Invalid or empty endpoints return an error.

The layout contracts nodes that occur together in an endpoint into groups and
uses `graphlay` to position and route the graph of groups. It then arranges each
group's members in a row, reducing gaps within endpoint sets. Sets may overlap,
and every node is drawn once. A rectangle is used only when it intersects exactly
its members. Otherwise, explicit branches identify those members. Edges prefer a
single straight segment between their visible endpoint boundaries. Direct routes
are checked against nodes, unrelated set outlines, and other edge routes. Detours
prefer one quadratic curve along their full length, or connected curves with
continuous tangents at joins. Where a full curve would intersect a node or set
outline, the route retains shorter bends around the obstacle. Labels sit beside
their edges, clear of node boxes, enclosures, other labels, and the final paths.
`RoutedEdge::paths` exposes the SVG path geometry and arrowheads;
`RoutedEdge::path` retains the routing waypoints between endpoint groups.

The result is deterministic for the same ordered input. PCG's adapter sorts its
input before rendering. Positions are currently computed independently for each
snapshot; preserving positions between snapshots is future work. Large groups of
overlapping sets can produce wide rows. The layout does not guarantee a minimum
number of crossings or prevent crossings between edges and set borders.

Run the independent tests on stable Rust:

```sh
cargo +stable test --manifest-path pcg-svg/Cargo.toml
```

PCG snapshot generation writes `.svg`, `.svg.json` (hover metadata), and
`.hypergraph.json` beside the existing `.dot` files. The viewer loads the SVG;
older archives without SVG continue to use DOT. MIR and auxiliary DOT views
continue to use their existing renderer.

`PCG_LEGACY_GRAPH_RENDERER=true` skips native SVG generation and removes stale
native files for rewritten snapshots. The viewer defaults to Rust SVG and offers
a Graphviz option under **Settings → PCG renderer**. Older or legacy snapshots
without SVG fall back to DOT.

To reproduce a snapshot without running the compiler:

```sh
cargo +stable run --manifest-path pcg-svg/Cargo.toml --example render -- \
  snapshot.hypergraph.json snapshot.svg
```
