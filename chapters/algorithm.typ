#import "../config/common.typ": *

= Symbolic local algorithm

// TODO: Integration of symbolic formulas with local strategy iteration
// - TODO: all successors => W0/L0/W1/L1 nodes
// - TODO: lazy edges -> changed complexity (?)

// Ideas:
// - formula pruning
//   TODO: permanently, using W0/W1 sets
//   TODO: on-the-fly, computing expected valuation

// On-the-fly pruning:
// - observation 1: the expansion of the graph can either end by reaching
//   an existing vertex or create a new cycle;
// - observation 2: when the expansion ends by reaching an existing vertex
//   then no matter which initial strategy is chosen for the just expanded
//   part, it will be:
//   - acyclic
//   - unreachable from the existing graph by following the current strategy
//   Thus its valuation can quickly be computed starting from the valuation
//   of the existing vertex it reached.
// - observation 3: in order for an expansion to be useful it has to
//   potentially improve the valuation of some already existing vertex.  
// Together these observations mean that:
// - when an expansion is trying to reach an existing vertex
// - the new valuation for the rest of the expansion can be computed
// - in particular we're interested in the valuation for the first vertex
//   in the expansion
// - and we can require this to be better than the best valuation of the
//   successors of the starting vertex from the existing graph.
// Pratically speaking:
// - when picking the existing p0 vertex from which to expand we can
//   store the valuation of its strategy successor
// - when expanding we should keep track of:
//   - the distance traveled
//   - the priorities see
// - when generating moves from formulas we can inspect each (b, i) and
//   - they could be unexplored, thus can be kept
//   - their valuation, when extended with the new distance and priorities,
//     could be worse than the one stored, in which case ignore them
//   - they valuation could be very favourable, in which case prefer them
//     (TODO: test if this is convenient or too costly)
// Note: when expanding from p1 nodes the most favourable valuation becomes
// the "smallest" one.
// TODO: maybe do something smart with nodes in the expansion too?
// TODO: this means that subsequent expansions without recomputing valuations
//       will see stale/wrong valuations unless we reached a vertex with no
//       improving successors.
