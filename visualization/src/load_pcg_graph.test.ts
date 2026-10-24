import * as Viz from "@viz-js/viz";
import { Api } from "./api";
import { loadPcgGraph } from "./load_pcg_graph";

jest.mock("@viz-js/viz");

beforeEach(() => jest.clearAllMocks());

it("displays Rust SVG and uses its hyperedge metadata without running Graphviz", async () => {
  const fetchDotFile = jest.fn().mockResolvedValue('<svg xmlns="http://www.w3.org/2000/svg"><g id="edge_0"/></svg>');
  const api = { fetchDotFile } as unknown as Api;
  const result = await loadPcgGraph(api, "data/example/state.dot");
  expect(result.svg.querySelector("#edge_0")).not.toBeNull();
  expect(result.metadataPath).toBe("data/example/state.svg.json");
  expect(result.renderer).toBe("svg");
  expect(fetchDotFile).toHaveBeenCalledTimes(1);
  expect(Viz.instance).not.toHaveBeenCalled();
});

it("uses DOT directly when Graphviz is selected, even if SVG is available", async () => {
  const fetchDotFile = jest.fn().mockResolvedValue("digraph { a -> b }");
  const renderSVGElement = jest.fn().mockReturnValue(document.createElementNS("http://www.w3.org/2000/svg", "svg"));
  (Viz.instance as jest.Mock).mockResolvedValue({ renderSVGElement });
  const result = await loadPcgGraph({ fetchDotFile } as unknown as Api, "state.dot", "dot");
  expect(fetchDotFile.mock.calls).toEqual([["state.dot"]]);
  expect(renderSVGElement).toHaveBeenCalledWith("digraph { a -> b }");
  expect(result.metadataPath).toBe("state.json");
  expect(result.renderer).toBe("dot");
});

it.each([null, "<!doctype html><html>404</html>", '<svg xmlns="http://www.w3.org/2000/svg"><g></svg>'])(
  "loads legacy DOT when the SVG is absent or invalid (%s)", async (svg) => {
    const fetchDotFile = jest.fn();
    if (svg === null) { fetchDotFile.mockRejectedValueOnce(new Error("not found")); }
    else { fetchDotFile.mockResolvedValueOnce(svg); }
    fetchDotFile.mockResolvedValueOnce("digraph { a -> b }");
    const renderSVGElement = jest.fn().mockReturnValue(document.createElementNS("http://www.w3.org/2000/svg", "svg"));
    (Viz.instance as jest.Mock).mockResolvedValue({ renderSVGElement });
    const result = await loadPcgGraph({ fetchDotFile } as unknown as Api, "state.dot");
    expect(renderSVGElement).toHaveBeenCalledWith("digraph { a -> b }");
    expect(result.metadataPath).toBe("state.json");
    expect(result.renderer).toBe("dot");
  }
);
