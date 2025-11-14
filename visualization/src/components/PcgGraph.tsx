import React, { useEffect, useState, useRef } from "react";
import * as Viz from "@viz-js/viz";
import panzoom, { PanZoom } from "panzoom";
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
  const [edgeMetadata, setEdgeMetadata] = useState<Record<string, any> | null>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const panzoomInstanceRef = useRef<PanZoom | null>(null);

  useEffect(() => {
    const loadGraph = async () => {
      const dotFilePath = getPCGDotGraphFilename(currentPoint, selectedFunction, iterations);

      if (!dotFilePath) {
        setSvgContent("");
        setEdgeMetadata(null);
        return;
      }

      const dotData = await api.fetchDotFile(dotFilePath);
      const viz = await Viz.instance();
      const svg = viz.renderSVGElement(dotData);

      svg.setAttribute("width", "100%");
      svg.setAttribute("height", "100%");

      setSvgContent(svg.outerHTML);

      // Try to load corresponding JSON file
      const jsonFilePath = dotFilePath.replace(/\.dot$/, '.json');
      try {
        const jsonData = await api.fetchDotFile(jsonFilePath);
        setEdgeMetadata(JSON.parse(jsonData));
      } catch (e) {
        // JSON file doesn't exist, that's fine
        setEdgeMetadata(null);
      }
    };

    loadGraph();
  }, [api, currentPoint, selectedFunction, iterations]);

  useEffect(() => {
    if (!containerRef.current || !svgContent) return;

    const svgElement = containerRef.current.querySelector("svg");
    if (!svgElement) return;

    if (panzoomInstanceRef.current) {
      panzoomInstanceRef.current.dispose();
    }

    panzoomInstanceRef.current = panzoom(svgElement, {
      maxZoom: 10,
      minZoom: 0.1,
      bounds: true,
      boundsPadding: 0.1,
    });

    // Add hover listeners for edges if we have metadata
    if (edgeMetadata) {
      const gElements = svgElement.querySelectorAll('g[id]');
      gElements.forEach((gElement) => {
        const id = gElement.getAttribute('id');
        if (id && edgeMetadata[id]) {
          gElement.addEventListener('mouseenter', () => {
            console.log(`Edge ${id} metadata:`, edgeMetadata[id]);
          });
        }
      });
    }

    return () => {
      if (panzoomInstanceRef.current) {
        panzoomInstanceRef.current.dispose();
        panzoomInstanceRef.current = null;
      }
    };
  }, [svgContent, edgeMetadata]);

  return (
    <div
      id="pcg-graph"
      ref={containerRef}
      style={{
        flex: 1,
        overflow: "hidden",
        marginRight: navigatorReservedWidth,
        display: showPCG ? "block" : "none",
      }}
      dangerouslySetInnerHTML={{ __html: svgContent }}
    />
  );
};

export default PcgGraph;

