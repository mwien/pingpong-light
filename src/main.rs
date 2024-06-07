use pingpong_light::bipartite_graph::BipartiteGraph;
use pingpong_light::exact;

fn main() {
    // Solve the problem using the given strategy.
    let g = BipartiteGraph::new_from_stdin().expect("c Failed to read the graph!");
    let ordering: Vec<usize> = exact::wdfas(&g);
    for u in &ordering { 
        println!("{}", u); 
    }    
}
