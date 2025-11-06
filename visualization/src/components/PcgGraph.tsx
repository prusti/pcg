import React, { useEffect, useState } from "react";
import * as Viz from "@viz-js/viz";
import { CurrentPoint, FunctionSlug } from "../types";
import { Api, PcgBlockDotGraphs } from "../api";

interface PcgGraphProps {
  showPCG: boolean;
  navigatorReservedWidth: string;
  currentPoint: CurrentPoint;
  selectedFunction: FunctionSlug;
  iterations: PcgBlockDotGraphs;
  api: Api;
}

function getIterationActions(
  dotGraphs: PcgBlockDotGraphs,
  currentPoint: CurrentPoint
) {
  if (currentPoint.type !== "stmt" || dotGraphs.length <= currentPoint.stmt) {
    return { pre_operands: [], post_operands: [], pre_main: [], post_main: [] };
  }
  const stmt = dotGraphs[currentPoint.stmt];
  return stmt.actions;
}

function getPCGDotGraphFilename(
  currentPoint: CurrentPoint,
  selectedFunction: string,
  graphs: PcgBlockDotGraphs
): string | null {
  if (currentPoint.type !== "stmt" || graphs.length <= currentPoint.stmt) {
    return null;
  }
  if (currentPoint.navigatorPoint.type === "action") {
    if (currentPoint.navigatorPoint.phase === "successor") {
      return null;
    }
    const iterationActions = getIterationActions(graphs, currentPoint);
    const actionGraphFilenames = iterationActions[currentPoint.navigatorPoint.phase as keyof typeof iterationActions];
    return `data/${selectedFunction}/${actionGraphFilenames[currentPoint.navigatorPoint.index]}`;
  }

  const navPoint = currentPoint.navigatorPoint;
  if (navPoint.type !== "iteration") {
    return null;
  }

  const phases = graphs[currentPoint.stmt].at_phase;
  const phaseIndex = phases.findIndex((p) => p.phase === navPoint.name);

  if (phaseIndex === -1 || phases.length === 0) {
    return null;
  }

  const filename: string = phases[phaseIndex].filename;
  return `data/${selectedFunction}/${filename}`;
}

const PcgGraph: React.FC<PcgGraphProps> = ({
  showPCG,
  navigatorReservedWidth,
  currentPoint,
  selectedFunction,
  iterations,
  api
}) => {
  const [svgContent, setSvgContent] = useState<string>("");

  useEffect(() => {
    const loadGraph = async () => {
      const dotFilePath = getPCGDotGraphFilename(currentPoint, selectedFunction, iterations);

      if (!dotFilePath) {
        setSvgContent("");
        return;
      }

      const dotData = await api.fetchDotFile(dotFilePath);
      const viz = await Viz.instance();
      const svg = viz.renderSVGElement(dotData);

      svg.setAttribute("width", "100%");
      svg.setAttribute("height", "100%");
      svg.setAttribute("zoomAndPan", "magnify");

      setSvgContent(svg.outerHTML);
    };

    loadGraph();
  }, [api, currentPoint, selectedFunction, iterations]);

  return (
    <div
      id="pcg-graph"
      style={{
        flex: 1,
        overflow: "auto",
        marginRight: navigatorReservedWidth,
        display: showPCG ? "block" : "none",
      }}
      dangerouslySetInnerHTML={{ __html: svgContent }}
    />
  );
};

export default PcgGraph;

