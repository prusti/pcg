import React, { useState } from "react";
import { fireEvent, render, screen, waitFor } from "@testing-library/react";
import * as Viz from "@viz-js/viz";
import { Api } from "../api";
import { PcgBlockVisualizationData } from "../generated_types";
import { PcgRenderer } from "../load_pcg_graph";
import { CurrentPoint, FunctionSlug } from "../types";
import PcgGraph from "./PcgGraph";
import Settings from "./Settings";

jest.mock("@viz-js/viz");
jest.mock("panzoom", () => jest.fn(() => ({ dispose: jest.fn() })));
jest.mock("./BorrowCheckerGraphs", () => () => null);
jest.mock("./LoopResults", () => () => null);

const currentPoint: CurrentPoint = {
  type: "stmt", block: 0, stmt: 0,
  navigatorPoint: { type: "iteration", name: "initial" },
};
const selectedFunction = "example" as FunctionSlug;
const pcgData = {
  statements: [{ graphs: { at_phase: [{ phase: "initial", filename: "state.dot" }] } }],
} as PcgBlockVisualizationData;
const highlight = jest.fn();

function Viewer({ api }: { api: Api }) {
  const [renderer, setRenderer] = useState<PcgRenderer>("svg");
  return <>
    <Settings showSettings onClose={jest.fn()} showActionsInCode={false}
      setShowActionsInCode={jest.fn()} showPCG setShowPCG={jest.fn()}
      showPCGNavigator setShowPCGNavigator={jest.fn()} renderer={renderer}
      setRenderer={setRenderer} currentPoint={currentPoint} selectedFunction={selectedFunction} api={api} />
    <PcgGraph renderer={renderer} showPCG navigatorReservedWidth="0px"
      currentPoint={currentPoint} selectedFunction={selectedFunction} api={api}
      pcgData={pcgData} onHighlightMirEdges={highlight} />
  </>;
}

beforeEach(() => {
  jest.clearAllMocks();
  (Viz.instance as jest.Mock).mockResolvedValue({
    renderSVGElement: jest.fn(() => {
      const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
      svg.setAttribute("data-renderer", "dot");
      return svg;
    }),
  });
});

it("switches the displayed graph and metadata between Rust SVG and Graphviz", async () => {
  const fetchDotFile = jest.fn(async (path: string) => {
    if (path.endsWith(".json")) return "{}";
    if (path.endsWith(".svg")) return '<svg xmlns="http://www.w3.org/2000/svg" data-renderer="svg"/>';
    return "digraph { a -> b }";
  });
  const { container } = render(<Viewer api={{ fetchDotFile } as unknown as Api} />);
  await waitFor(() => expect(container.querySelector('svg[data-renderer="svg"]')).not.toBeNull());
  expect(fetchDotFile).toHaveBeenCalledWith("data/example/state.svg.json");
  expect(Viz.instance).not.toHaveBeenCalled();

  fireEvent.change(screen.getByLabelText("PCG renderer"), { target: { value: "dot" } });
  await waitFor(() => expect(container.querySelector('svg[data-renderer="dot"]')).not.toBeNull());
  expect(fetchDotFile).toHaveBeenCalledWith("data/example/state.json");

  fireEvent.change(screen.getByLabelText("PCG renderer"), { target: { value: "svg" } });
  await waitFor(() => expect(container.querySelector('svg[data-renderer="svg"]')).not.toBeNull());
  expect(Viz.instance).toHaveBeenCalledTimes(1);
});

it("identifies the fallback for a snapshot generated with the legacy option", async () => {
  const fetchDotFile = jest.fn(async (path: string) => {
    if (path.endsWith(".svg")) throw new Error("not found");
    return path.endsWith(".json") ? "{}" : "digraph { a -> b }";
  });
  render(<Viewer api={{ fetchDotFile } as unknown as Api} />);
  expect(await screen.findByRole("status")).not.toBeNull();
  fireEvent.change(screen.getByLabelText("PCG renderer"), { target: { value: "dot" } });
  await waitFor(() => expect(screen.queryByRole("status")).toBeNull());
});
