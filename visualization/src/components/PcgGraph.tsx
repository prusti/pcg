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
  onHighlightMirEdges: (edges: Set<string>) => void;
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
  api,
  onHighlightMirEdges
}) => {
  const [svgContent, setSvgContent] = useState<string>("");
  const [edgeMetadata, setEdgeMetadata] = useState<Record<string, any> | null>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const panzoomInstanceRef = useRef<PanZoom | null>(null);
  const currentlyHighlightedRef = useRef<{path: SVGPathElement, originalStroke: string, originalWidth: string} | null>(null);

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

    // Store event listeners for cleanup
    const eventListeners: Array<{
      element: Element;
      type: string;
      listener: EventListener;
    }> = [];

    // Add hover listeners for edges if we have metadata
    if (edgeMetadata) {
      const gElements = svgElement.querySelectorAll('g[id]');
      console.log('Found g elements with ids:', Array.from(gElements).map(g => g.getAttribute('id')));
      console.log('Available metadata keys:', Object.keys(edgeMetadata));

      gElements.forEach((gElement) => {
        const id = gElement.getAttribute('id');
        console.log('Checking g element with id:', id, 'has metadata:', id && edgeMetadata[id]);
        if (id && edgeMetadata[id]) {
          // Make the element look hoverable
          (gElement as HTMLElement).style.cursor = 'pointer';

          const pathElement = gElement.querySelector('path');
          const originalStroke = pathElement?.getAttribute('stroke');
          const originalStrokeWidth = pathElement?.getAttribute('stroke-width');

          const mouseenterHandler = () => {
            console.log(`Edge ${id} metadata:`, edgeMetadata[id]);
            console.log('gElement:', gElement);
            console.log('pathElement:', pathElement);
            console.log('All paths in gElement:', gElement.querySelectorAll('path'));

            // Clear any previously highlighted edge
            if (currentlyHighlightedRef.current) {
              const prev = currentlyHighlightedRef.current;
              prev.path.setAttribute('stroke', prev.originalStroke);
              prev.path.setAttribute('stroke-width', prev.originalWidth);
            }

            // Graphviz creates multiple path elements - highlight all paths that are part of the edge
            const allPaths = Array.from(gElement.querySelectorAll('path'));
            let pathsToHighlight = allPaths.filter(p => {
              // Skip filled paths (arrowheads) - only highlight stroked paths
              const fill = p.getAttribute('fill');
              const stroke = p.getAttribute('stroke');
              return fill === 'none' || (!fill && stroke);
            });

            console.log('All paths:', allPaths.length, 'Paths to highlight:', pathsToHighlight.length);

            if (pathsToHighlight.length === 0 && allPaths.length > 0) {
              // If no paths match our filter, just use all paths
              pathsToHighlight = allPaths;
            }

            // Store original values and highlight
            const highlightedPaths: Array<{path: SVGPathElement, originalStroke: string, originalWidth: string}> = [];
            pathsToHighlight.forEach(p => {
              const currentStroke = p.getAttribute('stroke') || 'black';
              const currentWidth = p.getAttribute('stroke-width') || '1';
              highlightedPaths.push({
                path: p as SVGPathElement,
                originalStroke: currentStroke,
                originalWidth: currentWidth
              });
              p.setAttribute('stroke', '#ff6b00');
              p.setAttribute('stroke-width', '3');
              console.log('Highlighted path with original stroke:', currentStroke, 'width:', currentWidth);
            });

            if (highlightedPaths.length > 0) {
              // Store first path for reference (we'll restore all in mouseleave)
              currentlyHighlightedRef.current = highlightedPaths[0];
              // Store all paths for restoration
              (gElement as any)._highlightedPaths = highlightedPaths;
            }

            // Extract MIR edges from branch choices
            const mirEdges = new Set<string>();
            const metadata = edgeMetadata[id];
            if (metadata.branch_choices && Array.isArray(metadata.branch_choices)) {
              metadata.branch_choices.forEach((branchChoice: any) => {
                if (branchChoice.from && branchChoice.chosen) {
                  const from = branchChoice.from.replace('bb', '');
                  if (Array.isArray(branchChoice.chosen)) {
                    branchChoice.chosen.forEach((to: string) => {
                      const toNum = to.replace('bb', '');
                      const edgeKey = `${from}-${toNum}`;
                      console.log(`Adding MIR edge key: ${edgeKey}`);
                      mirEdges.add(edgeKey);
                    });
                  }
                }
              });
            }

            console.log('Highlighting MIR edges:', Array.from(mirEdges));
            onHighlightMirEdges(mirEdges);
          };

          const mouseleaveHandler = () => {
            // Restore all highlighted paths
            const highlightedPaths = (gElement as any)._highlightedPaths as Array<{path: SVGPathElement, originalStroke: string, originalWidth: string}> | undefined;
            if (highlightedPaths) {
              highlightedPaths.forEach(({ path, originalStroke, originalWidth }) => {
                path.setAttribute('stroke', originalStroke);
                path.setAttribute('stroke-width', originalWidth);
                console.log('Restored path to stroke:', originalStroke, 'width:', originalWidth);
              });
              delete (gElement as any)._highlightedPaths;
            }

            if (currentlyHighlightedRef.current) {
              currentlyHighlightedRef.current = null;
            }

            // Clear MIR edge highlighting
            console.log('Clearing MIR edge highlighting');
            onHighlightMirEdges(new Set());
          };

          gElement.addEventListener('mouseenter', mouseenterHandler);
          gElement.addEventListener('mouseleave', mouseleaveHandler);

          eventListeners.push(
            { element: gElement, type: 'mouseenter', listener: mouseenterHandler },
            { element: gElement, type: 'mouseleave', listener: mouseleaveHandler }
          );
        }
      });
    }

    return () => {
      // Clean up event listeners
      eventListeners.forEach(({ element, type, listener }) => {
        element.removeEventListener(type, listener);

        // Restore any highlighted paths on this element
        const highlightedPaths = (element as any)._highlightedPaths as Array<{path: SVGPathElement, originalStroke: string, originalWidth: string}> | undefined;
        if (highlightedPaths) {
          highlightedPaths.forEach(({ path, originalStroke, originalWidth }) => {
            path.setAttribute('stroke', originalStroke);
            path.setAttribute('stroke-width', originalWidth);
          });
          delete (element as any)._highlightedPaths;
        }
      });

      // Clear any highlighted edges
      if (currentlyHighlightedRef.current) {
        currentlyHighlightedRef.current = null;
      }

      // Clear MIR highlighting
      onHighlightMirEdges(new Set());

      if (panzoomInstanceRef.current) {
        panzoomInstanceRef.current.dispose();
        panzoomInstanceRef.current = null;
      }
    };
  }, [svgContent, edgeMetadata, onHighlightMirEdges]);

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

