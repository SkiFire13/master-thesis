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
// - observations:
//   - expansion for p0 is useful if it improves play profiles
//   - play profiles depends only on transitive successors
//   - existing strategy cannot go out of existing graph
//   - play profiles of existing graph don't depend on expansion
//   - so play profiles of expansion can freely depend on existing graph
//     - that is, no cycles between existing graph and expansion
//   - two cases for how expansion ends:
//     - on vertex in expansion -> compute play profile of cycle
//     - on vertex in existing graph -> compute play profile of chain
//   - computed incrementally and on-the-fly to prune p0 moves
//     - require improving play profile
//     - possibly winning for p0
//   - note: once done the play profiles are no longer optimal
//     - assumption: symmetric expansion and not repeated
//     - unless non-improving expansion, then it can be re-expanded.
// Pratically speaking:
// - when picking the existing p0 vertex from which to expand we can
//   store the valuation of its strategy successor
// - when expanding we should keep track of:
//   - the distance traveled
//   - the nodes seen sorted by priority
// - when generating moves from formulas we can inspect each (b, i) and
//   - they could be unexplored, thus can be kept
//   - they could be explored, thus compute the profile for the initial
//     successor. Ignore this node if the profile is not improving.
//   (TODO: test if this is convenient or too costly)
// Note: when expanding from p1 nodes the most favourable profile
// becomes the "smallest" one.
//
// TODO: maybe do something smart with nodes in the expansion too?
// TODO: this means that subsequent expansions without recomputing
//       profiles will see stale/wrong valuations unless we reached
//       a vertex with no improving successors.
