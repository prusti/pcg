use pcg_svg::Hypergraph;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let input = args.next().ok_or("usage: render GRAPH.json GRAPH.svg")?;
    let output = args.next().ok_or("usage: render GRAPH.json GRAPH.svg")?;
    let graph: Hypergraph = serde_json::from_str(&std::fs::read_to_string(input)?)?;
    std::fs::write(output, graph.to_svg()?)?;
    Ok(())
}
