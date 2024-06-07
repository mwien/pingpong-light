use crate::graph;
use crate::heuristic;
use crate::scc::SCC;
use std::collections::{HashSet,HashMap};
use itertools::{ Itertools, iproduct };
use bit_set::BitSet;
use highs::RowProblem;

/// Returns an ordering of the vertices such that the directed edges x -> y violating this ordering (x comes after y) form a *minimum* weight [feedback arc set] of the given graph 
/// (i.e. a topological ordering of the spanning DAG of the FAS), which is usually a strongly connected component of the input.
///
/// This function implements the [implicit hitting set] algorithm: We consider a *dynamic* set system, in which the sets are the cycles
/// of the input graph. Since there may be exponentially many such cycles, we start with a small initial subset of them. We find a
/// hitting set of these cycles and check whether it happens to hit *all* cycles of the input graph. If so, we found an optimal feedback arc set,
/// since we computed a minimum hitting set. If not, we search for cycles in the remaining graph, add them to our set system, and recompute
/// the hitting set.
///
/// # Computation of the Hitting Set
/// The hitting set is computed in each round with `hitting_set`, which currently uses the LP/ILP solver [highs].
///
/// [feedback arc set]: https://en.wikipedia.org/wiki/Feedback_arc_set
/// [implicit hitting set]: https://link.springer.com/chapter/10.1007/978-3-642-13509-5_14
/// [highs]: https://highs.dev/
pub fn solve(scc: &SCC) -> Vec<usize> {  
    let     n = scc.n; // number of nodes  
    let mut m = 0;       // number of arcs, arc ids are 0...m-1

    // computing arc ids (i.e., variables) and their weight
    let mut weights = Vec::new();
    let mut idarc = Vec::new(); 
    let mut arcs    = HashMap::<(usize,usize), usize>::new();
    iproduct!(0..n, 0..n)
	.filter(|(u,v)| scc.w[*u][*v] > 0 )
	.for_each(|(u, v)| { weights.push(scc.w[u][v]); arcs.insert((u,v), m); idarc.push((u, v)); m += 1; } );
    let arcid = |u: usize, v: usize| { *arcs.get(&(u,v)).unwrap() };
    
    // map cycles (as set of vertices) to a (sorted) set of arc ids
    let cycle2arcs = |cycle: Vec<usize>| {
	let mut c = cycle.into_iter().circular_tuple_windows::<(usize,usize)>().map(|uv| arcid(uv.0,uv.1)).collect_vec();
	c.sort(); c	
    };

    let mut cycles = graph::three_cycles(&scc.g).into_iter().map(cycle2arcs).collect_vec();

    // repeatedly find a feedback arc set (a hitting set on the cycles) and compute new (still not hit) cycles
    let mut fas;
    let mut sol;
    let mut vals;

    loop {
	// This (outer) loop is the main ILP loop. If it breaks, an optimal fas was found.
	loop {
	    // This (inner) loop finds hitting sets using an LP relaxation.
	    // If it breaks, we have a hitting set for all cycles, but it is not necessarily optimal.
	    (fas, sol) = hitting_set(&cycles, &weights, true);
	    vals = sol.columns().to_vec(); 
            
            let oldsz = cycles.len();
            new_cycles(&scc.w, &scc.g, &fas, arcid).into_iter()
                .map(cycle2arcs)
                .for_each(|c| cycles.push(c) );
	    if cycles.len() == oldsz {
                break;
            }
	}
        // compute bounds based on last LP solution and rounding
        let mut lb = 0.0;
        let mut ub = 0.0;
        for i in 0..vals.len() {
            lb += vals[i] * weights[i] as f64;
            if fas.contains(i) {
                ub += weights[i] as f64;
            }
        }
        // if bounds match by less than full integer, the rounded LP relaxation is optimal
        if ub - lb < 0.99 {
            let resfas = (0..n).flat_map( |v| std::iter::once(v).cartesian_product(scc.g[v].iter()) )
                .filter    ( |(u,v)| fas.contains(arcid(*u,**v))                                    )
                .map(|(u,v)| (u,*v)).collect_vec();
            return scc.fas_to_ordering(&resfas);
        }
        // else, solve the ILP
	(fas, _) = hitting_set(&cycles, &weights, false);
        let oldsz = cycles.len();
        new_cycles(&scc.w, &scc.g, &fas, arcid).into_iter()
            .map(cycle2arcs)
            .for_each(|c| cycles.push(c));
        if cycles.len() == oldsz {
            break;
        }
    }
    
    let resfas = (0..n).flat_map( |v| std::iter::once(v).cartesian_product(scc.g[v].iter()) )
	.filter    ( |(u,v)| fas.contains(arcid(*u,**v))                                    )
	.map(|(u,v)| (u,*v)).collect_vec();
    scc.fas_to_ordering(&resfas)
}

fn generate_new_cycles(fas: &Vec<(usize, usize)>, h: &Vec<Vec<usize>>) -> Vec<Vec<usize>> { 
    let sccs = graph::compute_sccs(h);
    let mut to_scc = vec![0; h.len()];
    for i in 0..sccs.len() {
        for v in sccs[i].iter().cloned() {
            to_scc[v] = i;
        }
    }
    let mut new_cycles: HashSet<Vec<usize>> = HashSet::new();
    for (u,v) in fas.iter().cloned() {
        if to_scc[u] != to_scc[v] {
            continue;
        }
        let k = 5;
        graph::find_more_cycles_bfs(h, &to_scc, v, u, k).into_iter().for_each(|c| {new_cycles.insert(c);}); 
    }
    new_cycles.into_iter().collect()
}

fn find_fas(g: &Vec<Vec<usize>>, w: &Vec<Vec<u64>>) -> Vec<(usize, usize)> {
    let mut fas: Vec<(usize, usize)> = Vec::new();
    let sccs = graph::compute_sccs(g);
    for scc in sccs.iter().cloned() {
        if scc.len() == 1 {
            continue;
        }
        // construct SCC 
        let mut scc_w = vec![vec![0; scc.len()]; scc.len()];
        for i in 0..scc.len() {
            for j in 0..scc.len() {
                scc_w[i][j] = w[scc[i]][scc[j]];
            }   
        }
        let scc_g = graph::get_subgraph(g, &scc);
        let scc_obj = SCC::new(scc, scc_w, scc_g);
        let scc_ordering = heuristic::kahns_heuristic(&scc_obj);
        let scc_fas = scc_obj.ordering_to_fas(&scc_ordering);
        for (u, v) in scc_fas {
            fas.push((scc_obj.labels[u], scc_obj.labels[v]));
        }
    }
    fas
}

/// Computes a set of cycles that was not hit by the given feedback arc set.
fn new_cycles(w: &Vec<Vec<u64>>, g: &Vec<Vec<usize>>, fas: &BitSet, arcid: impl Fn(usize,usize)->usize) -> Vec<Vec<usize>> {
    let mut residual: Vec<Vec<usize>> = vec![Vec::new(); g.len()];
    (0..w.len()).flat_map( |v| std::iter::once(v).cartesian_product(g[v].iter()) )
	.filter    ( |(u,v)| !fas.contains(arcid(*u,**v))                        )
	.for_each  ( |(u,v)|  residual[u].push(*v)                               );

    generate_new_cycles( 
	&find_fas(&residual, w), 
	&residual
    )
}

/// Computes an minimum weight hitting set of the given set system.
///
/// The sets should be ordered and contain elements from `0...weights.len()-1`.
/// Correspondingly, the weight of element `i` is `weights[i]`.
///
/// This function finds the hitting set with the trivial ILP formulation using the highs lp solver.
fn hitting_set(sets: &Vec<Vec<usize>>, weights: &Vec<u64>, relaxation: bool) -> (BitSet, highs::Solution) {
    let mut problem = RowProblem::new();
    let mut cols = Vec::new();
    for weight in weights {
	match relaxation {
	    false => cols.push( problem.add_integer_column(*weight as f64, 0..=1) ),
	    true  => cols.push( problem.add_column(        *weight as f64, 0..=1) ),

	};
    }

    for set in sets.iter() {
        problem.add_row(1..,  &set.iter().map(|i| (cols[*i], 1.0)).collect_vec())
    }

    let mut model = problem.optimise(highs::Sense::Minimise);
    
    model.set_option("parallel", "off");
    model.set_option("threads", 1);

    let solved_model = model.solve();
    let sol = solved_model.get_solution();
  
    let mut hs = BitSet::new();
    let cols = sol.columns().to_vec();
    if relaxation {
        for set in sets.iter() {
	    if set.iter().any(|e| hs.contains(*e)) { continue; }
	    if let Some((_,e)) = set.iter().map(|e| (cols[*e],e)).max_by(|a, b| a.0.total_cmp(&b.0)) {
		hs.insert(*e);
	    }
	} 
    } else {
	(0..weights.len()).filter(|i| cols[*i].round() as i64 == 1)
	    .for_each(|i| { hs.insert(i); } );
    }
    (hs, sol)   
}
