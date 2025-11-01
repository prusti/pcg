import React, {
  useState,
  useEffect,
  useCallback,
  useMemo,
  useRef,
} from "react";
import * as Viz from "@viz-js/viz";
import { fetchDotFile, openDotGraphInNewWindow } from "../dot_graph";

import {
  CurrentPoint,
  FunctionSlug,
  FunctionsMetadata,
  MirStmt,
  PathData,
  PcgProgramPointData,
  PcgStmtVisualizationData,
  SelectedAction,
  SourcePos,
} from "../types";
import SymbolicHeap from "./SymbolicHeap";
import PathConditions from "./PathConditions";
import MirGraph from "./MirGraph";
import Assertions, { Assertion } from "./Assertions";
import {
  getGraphData,
  getPcgProgramPointData,
  getPaths,
  PcgBlockDotGraphs,
} from "../api";
import {
  filterNodesAndEdges,
  layoutUnsizedNodes,
  toDagreEdges,
} from "../mir_graph";
import FunctionSelector from "./FunctionSelector";
import PCGNavigator from "./PCGNavigator";
import PathSelector from "./PathSelector";
import {
  addKeyDownListener,
  reloadPathData,
  reloadIterations,
} from "../effects";
import BorrowCheckerGraphs from "./BorrowCheckerGraphs";
import SourceCodeViewer from "./SourceCodeViewer";
import { EvalStmtData, MirEdge, MirNode } from "../generated/types";

const getActionGraphFilename = (
  selectedFunction: string,
  actionGraphFilenames: string[],
  actionIndex: number
): string | null => {
  return `data/${selectedFunction}/${actionGraphFilenames[actionIndex]}`;
};

function getPCGDotGraphFilename(
  currentPoint: CurrentPoint,
  selectedFunction: string,
  selected: number,
  graphs: PcgBlockDotGraphs
): string | null {
  if (currentPoint.type !== "stmt" || graphs.length <= currentPoint.stmt) {
    return null;
  }
  const selectedAction = getSelectedAction(currentPoint);
  if (selectedAction) {
    const iterationActions = getIterationActions(graphs, currentPoint);
    const actionGraphFilenames = iterationActions[selectedAction.phase];
    return getActionGraphFilename(
      selectedFunction,
      actionGraphFilenames,
      selectedAction.index
    );
  }

  const phases: [string, string][] = graphs[currentPoint.stmt].at_phase;

  // Handle deselection case
  if (selected < 0) {
    return null;
  }

  const filename: string =
    selected >= phases.length
      ? phases[phases.length - 1][1]
      : phases[selected][1];
  return `data/${selectedFunction}/${filename}`;
}

interface AppProps {
  initialFunction: FunctionSlug;
  initialPaths: number[][];
  initialAssertions: Assertion[];
  functions: FunctionsMetadata;
  initialPath?: number;
}

function getSelectedAction(currentPoint: CurrentPoint): SelectedAction | null {
  if (currentPoint.type !== "stmt") {
    return null;
  }
  return currentPoint.selectedAction;
}

export const App: React.FC<AppProps> = ({
  initialFunction,
  initialPaths,
  initialAssertions,
  functions,
  initialPath = 0,
}) => {
  const [iterations, setIterations] = useState<PcgBlockDotGraphs>([]);
  const [selected, setSelected] = useState<number | null>(null);
  const [pathData, setPathData] = useState<PathData | null>(null);
  const [pcgProgramPointData, setPcgProgramPointData] =
    useState<PcgProgramPointData | null>(null);
  const [currentPoint, setCurrentPoint] = useState<CurrentPoint>({
    type: "stmt",
    block: 0,
    stmt: 0,
    selectedAction: null,
  });

  const [selectedFunction, setSelectedFunction] = useState<FunctionSlug>(
    initialFunction || (Object.keys(functions)[0] as any)
  );
  const [selectedPath, setSelectedPath] = useState<number>(initialPath);
  const [paths, setPaths] = useState<number[][]>(initialPaths);
  const [assertions, setAssertions] = useState<Assertion[]>(initialAssertions);
  const [nodes, setNodes] = useState<MirNode[]>([]);
  const [edges, setEdges] = useState<MirEdge[]>([]);
  const [showPathBlocksOnly, setShowPathBlocksOnly] = useState(
    localStorage.getItem("showPathBlocksOnly") === "true"
  );
  const [showUnwindEdges, setShowUnwindEdges] = useState(false);
  const [showPCG, setShowPCG] = useState(
    localStorage.getItem("showPCG") !== "false"
  );
  const [showPCGNavigator, setShowPCGNavigator] = useState(
    localStorage.getItem("showPCGNavigator") !== "false"
  );
  const [showSettings, setShowSettings] = useState(
    localStorage.getItem("showSettings") === "true"
  );
  const [isSourceCodeMinimized, setIsSourceCodeMinimized] = useState(
    localStorage.getItem("isSourceCodeMinimized") === "true"
  );
  const [codeFontSize, setCodeFontSize] = useState<number>(
    parseInt(localStorage.getItem("codeFontSize") || "12")
  );

  // State for panel resizing
  const [leftPanelWidth, setLeftPanelWidth] = useState<string>(
    localStorage.getItem("leftPanelWidth") || "50%"
  );
  const [isDragging, setIsDragging] = useState<boolean>(false);
  const dividerRef = useRef<HTMLDivElement>(null);

  const { filteredNodes, filteredEdges } = filterNodesAndEdges(nodes, edges, {
    showUnwindEdges,
    path:
      showPathBlocksOnly && selectedPath < paths.length
        ? paths[selectedPath]
        : null,
  });

  const layoutResult = useMemo(() => {
    return layoutUnsizedNodes(filteredNodes, filteredEdges);
  }, [filteredNodes, filteredEdges]);

  const dagreNodes = layoutResult.nodes;
  const dagreEdges = useMemo(() => {
    return toDagreEdges(filteredEdges);
  }, [filteredEdges]);

  async function loadPCGDotGraph() {
    const dotGraph = document.getElementById("pcg-graph");
    if (!dotGraph) {
      console.error("Dot graph element not found");
      return;
    }
    const dotFilePath = getPCGDotGraphFilename(
      currentPoint,
      selectedFunction,
      selected,
      iterations
    );
    if (!dotFilePath) {
      dotGraph.innerHTML = "";
    } else {
      const dotData = await fetchDotFile(dotFilePath);

      Viz.instance().then(function (viz) {
        dotGraph.innerHTML = "";
        dotGraph.appendChild(viz.renderSVGElement(dotData));
      });
    }
  }

  useEffect(() => {
    const graph = document.getElementById("pcg-graph");
    if (showPCG) {
      graph.style.display = "block";
    } else {
      graph.style.display = "none";
    }
  }, [showPCG]);

  useEffect(() => {
    loadPCGDotGraph();
  }, [iterations, currentPoint, selectedFunction, selected]);

  useEffect(() => {
    if (selectedFunction) {
      (async function () {
        const mirGraph = await getGraphData(selectedFunction);
        setNodes(mirGraph.nodes);
        setEdges(mirGraph.edges);
        setPaths(await getPaths(selectedFunction));
      })();
    }
  }, [selectedFunction]);

  useEffect(() => {
    const fetchPcgStmtVisualizationData = async () => {
      try {
        const pcgStmtVisualizationData = await getPcgProgramPointData(
          selectedFunction,
          currentPoint
        );
        setPcgProgramPointData(pcgStmtVisualizationData);
      } catch (error) {
        console.error("Error fetching pcg stmt visualization data:", error);
      }
    };

    reloadPathData(
      selectedFunction,
      selectedPath,
      currentPoint,
      paths,
      setPathData
    );
    fetchPcgStmtVisualizationData();
  }, [selectedFunction, selectedPath, currentPoint, paths]);

  const currentBlock = currentPoint.type === "stmt" ? currentPoint.block : null;
  const currentStmt = currentPoint.type === "stmt" ? currentPoint.stmt : null;

  useEffect(() => {
    reloadIterations(selectedFunction, currentPoint, setIterations);
  }, [selectedFunction, currentPoint]);

  useEffect(() => {
    setSelected(null);
  }, [selectedFunction, currentBlock, currentStmt]);

  useEffect(() => {
    if (
      currentPoint.type === "stmt" &&
      iterations.length > currentPoint.stmt &&
      selected === null
    ) {
      const phases = iterations[currentPoint.stmt].at_phase;
      const postMainIndex = phases.findIndex(([name]) => name === "post_main");
      if (postMainIndex !== -1) {
        setSelected(postMainIndex);
      } else if (phases.length > 0) {
        setSelected(phases.length - 1);
      }
    }
  }, [iterations, currentPoint, selected]);

  useEffect(() => {
    return addKeyDownListener(nodes, filteredNodes, setCurrentPoint);
  }, [nodes, showPathBlocksOnly]);

  function addLocalStorageCallback(key: string, value: any) {
    useEffect(() => {
      localStorage.setItem(key, value.toString());
    }, [value]);
  }

  addLocalStorageCallback("selectedFunction", selectedFunction);
  addLocalStorageCallback("selectedPath", selectedPath);
  addLocalStorageCallback("showPathBlocksOnly", showPathBlocksOnly);
  addLocalStorageCallback("showPCG", showPCG);
  addLocalStorageCallback("showPCGNavigator", showPCGNavigator);
  addLocalStorageCallback("showSettings", showSettings);
  addLocalStorageCallback("isSourceCodeMinimized", isSourceCodeMinimized);
  addLocalStorageCallback("codeFontSize", codeFontSize);
  addLocalStorageCallback("leftPanelWidth", leftPanelWidth);

  const isBlockOnSelectedPath = useCallback(
    (block: number) => {
      if (paths.length === 0 || selectedPath >= paths.length) return false;
      return paths[selectedPath].includes(block);
    },
    [paths, selectedPath]
  );

  const highlightSpan = useMemo(() => {
    const selectedStmt = getSelectedStmt(nodes, currentPoint);
    if (!selectedStmt) {
      return null;
    }
    return calculateRelativeSpan(
      selectedStmt,
      functions[selectedFunction].start
    );
  }, [nodes, currentPoint, selectedFunction, functions]);

  // Divider drag handlers
  const handleMouseDown = (e: React.MouseEvent) => {
    setIsDragging(true);
    e.preventDefault();
  };

  const handleMouseUp = useCallback(() => {
    setIsDragging(false);
  }, []);

  const handleMouseMove = useCallback(
    (e: MouseEvent) => {
      if (!isDragging) return;

      const rootElement = document.getElementById("root");
      if (!rootElement) return;

      const rootRect = rootElement.getBoundingClientRect();
      const newLeftWidth = ((e.clientX - rootRect.left) / rootRect.width) * 100;

      // Enforce min/max constraints (e.g., 20% - 80%)
      const clampedWidth = Math.min(Math.max(newLeftWidth, 20), 80);
      setLeftPanelWidth(`${clampedWidth}%`);
    },
    [isDragging]
  );

  // Add and remove event listeners for dragging
  useEffect(() => {
    document.addEventListener("mousemove", handleMouseMove);
    document.addEventListener("mouseup", handleMouseUp);

    return () => {
      document.removeEventListener("mousemove", handleMouseMove);
      document.removeEventListener("mouseup", handleMouseUp);
    };
  }, [handleMouseMove, handleMouseUp]);

  return (
    <div style={{ display: "flex", width: "100%" }}>
      <div
        style={{
          position: "relative",
          minHeight: "100vh",
          flex: "none",
          width: leftPanelWidth,
          overflow: "auto",
        }}
      >
        <div
          style={{
            position: "sticky",
            top: 0,
            backgroundColor: "white",
            zIndex: 100,
            paddingBottom: "10px",
          }}
        >
          <FunctionSelector
            functions={functions}
            selectedFunction={selectedFunction}
            onChange={setSelectedFunction}
          />
          <button
            onClick={() => setShowSettings(!showSettings)}
            style={{
              margin: "10px",
              padding: "8px 16px",
              cursor: "pointer",
              backgroundColor: "#4CAF50",
              color: "white",
              border: "none",
              borderRadius: "4px",
            }}
          >
            {showSettings ? "Hide Settings" : "Show Settings"}
          </button>
          <div style={{ position: "relative" }}>
            <div
              style={{
                position: "absolute",
                top: "10px",
                right: "10px",
                zIndex: 10,
                display: "flex",
                gap: "5px",
              }}
            >
              <button
                onClick={() => setCodeFontSize(Math.max(8, codeFontSize - 1))}
                style={{
                  cursor: "pointer",
                  backgroundColor: "#888",
                  color: "white",
                  border: "none",
                  borderRadius: "4px",
                  padding: "5px 10px",
                  fontSize: "12px",
                }}
                title="Decrease font size"
              >
                A−
              </button>
              <button
                onClick={() => setCodeFontSize(Math.min(24, codeFontSize + 1))}
                style={{
                  cursor: "pointer",
                  backgroundColor: "#888",
                  color: "white",
                  border: "none",
                  borderRadius: "4px",
                  padding: "5px 10px",
                  fontSize: "12px",
                }}
                title="Increase font size"
              >
                A+
              </button>
              <button
                onClick={() => setIsSourceCodeMinimized(!isSourceCodeMinimized)}
                style={{
                  cursor: "pointer",
                  backgroundColor: "#888",
                  color: "white",
                  border: "none",
                  borderRadius: "4px",
                  padding: "5px 10px",
                  fontSize: "12px",
                }}
                title={isSourceCodeMinimized ? "Maximize" : "Minimize"}
              >
                {isSourceCodeMinimized ? "▼" : "▲"}
              </button>
            </div>
            <SourceCodeViewer
              metadata={functions[selectedFunction]}
              highlightSpan={highlightSpan}
              minimized={isSourceCodeMinimized}
              fontSize={codeFontSize}
            />
          </div>
        </div>

        {showSettings && (
          <div
            style={{
              position: "fixed",
              right: 0,
              top: 0,
              bottom: 0,
              width: "300px",
              backgroundColor: "#f5f5f5",
              borderLeft: "2px solid #ccc",
              padding: "20px",
              overflowY: "auto",
              zIndex: 1000,
              boxShadow: "-2px 0 5px rgba(0,0,0,0.1)",
            }}
          >
            <h3 style={{ marginTop: 0 }}>Settings</h3>
            <button
              onClick={() => setShowSettings(false)}
              style={{
                position: "absolute",
                top: "10px",
                right: "10px",
                cursor: "pointer",
                backgroundColor: "#f44336",
                color: "white",
                border: "none",
                borderRadius: "4px",
                padding: "5px 10px",
              }}
            >
              ✕
            </button>

            <div style={{ marginBottom: "20px" }}>
              <PathSelector
                paths={paths}
                selectedPath={selectedPath}
                setSelectedPath={setSelectedPath}
                showPathBlocksOnly={showPathBlocksOnly}
                setShowPathBlocksOnly={setShowPathBlocksOnly}
              />
            </div>

            <div style={{ marginBottom: "20px" }}>
              <label style={{ display: "block", marginBottom: "10px" }}>
                <input
                  type="checkbox"
                  checked={showPCG}
                  onChange={(e) => setShowPCG(e.target.checked)}
                />
                {" "}Show PCG
              </label>
              <button
                style={{
                  width: "100%",
                  padding: "8px",
                  marginBottom: "10px",
                  cursor: "pointer",
                }}
                onClick={async () => {
                  const dotFilePath = getPCGDotGraphFilename(
                    currentPoint,
                    selectedFunction,
                    selected,
                    iterations
                  );
                  if (dotFilePath) {
                    openDotGraphInNewWindow(dotFilePath);
                  }
                }}
              >
                Open Current PCG in New Window
              </button>
              <label style={{ display: "block", marginBottom: "10px" }}>
                <input
                  type="checkbox"
                  checked={showPCGNavigator}
                  onChange={(e) => setShowPCGNavigator(e.target.checked)}
                />
                {" "}Show PCG Navigator
              </label>
            </div>

            <div style={{ marginBottom: "20px" }}>
              <h4>Borrow Checker</h4>
              <BorrowCheckerGraphs
                currentPoint={currentPoint}
                selectedFunction={selectedFunction}
              />
            </div>
          </div>
        )}
        <MirGraph
          nodes={dagreNodes}
          edges={dagreEdges}
          mirNodes={nodes}
          currentPoint={currentPoint}
          setCurrentPoint={setCurrentPoint}
          height={layoutResult.height}
          isBlockOnSelectedPath={isBlockOnSelectedPath}
        />
        {showPCGNavigator &&
          currentPoint.type === "stmt" &&
          iterations.length > currentPoint.stmt &&
          pcgProgramPointData &&
          !Array.isArray(pcgProgramPointData.actions) && (
            <PCGNavigator
              iterations={iterations[currentPoint.stmt]}
              pcgData={pcgProgramPointData as PcgStmtVisualizationData}
              selectedPhase={
                getSelectedAction(currentPoint) === null ? selected : null
              }
              selectedAction={getSelectedAction(currentPoint)}
              onSelectPhase={(index) => {
                if (currentPoint.type === "stmt") {
                  setCurrentPoint({
                    ...currentPoint,
                    selectedAction: null,
                  });
                  setSelected(index);
                }
              }}
              onSelectAction={(action) => {
                if (currentPoint.type === "stmt") {
                  setCurrentPoint({
                    ...currentPoint,
                    selectedAction: action,
                  });
                }
              }}
            />
          )}
        {pathData && (
          <div style={{ position: "absolute", top: "20px", right: "20px" }}>
            <SymbolicHeap heap={pathData.heap} />
            <PathConditions pcs={pathData.pcs} />
            <Assertions assertions={assertions} />
          </div>
        )}
      </div>

      {/* Draggable divider */}
      <div
        ref={dividerRef}
        style={{
          width: "10px",
          cursor: "col-resize",
          background: "#ccc",
          position: "relative",
          zIndex: 100,
          display: showPCG ? "block" : "none",
        }}
        onMouseDown={handleMouseDown}
      >
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "2px",
            width: "6px",
            height: "30px",
            background: "#999",
            borderRadius: "3px",
            transform: "translateY(-50%)",
          }}
        ></div>
      </div>

      <div id="pcg-graph" style={{ flex: 1, overflow: "auto" }}></div>
    </div>
  );
};

function getIterationActions(
  dotGraphs: PcgBlockDotGraphs,
  currentPoint: CurrentPoint
): EvalStmtData<string[]> {
  if (currentPoint.type !== "stmt" || dotGraphs.length <= currentPoint.stmt) {
    return { pre_operands: [], post_operands: [], pre_main: [], post_main: [] };
  }
  const stmt = dotGraphs[currentPoint.stmt];
  return stmt.actions;
}

function getSelectedStmt(
  nodes: MirNode[],
  currentPoint: CurrentPoint
): MirStmt | null {
  if (currentPoint.type !== "stmt") {
    return null;
  }

  const node = nodes.find((n) => n.block === currentPoint.block);
  if (!node) {
    return null;
  }

  if (currentPoint.stmt < node.stmts.length) {
    return node.stmts[currentPoint.stmt];
  } else if (currentPoint.stmt === node.stmts.length) {
    return node.terminator;
  }

  return null;
}

type RelativeSpan = {
  low: SourcePos;
  high: SourcePos;
};

function calculateRelativeSpan(
  stmt: MirStmt,
  functionStart: SourcePos
): RelativeSpan {
  return {
    low: {
      line: stmt.span.low.line - functionStart.line,
      column: stmt.span.low.column - functionStart.column,
    },
    high: {
      line: stmt.span.high.line - functionStart.line,
      column: stmt.span.high.column - functionStart.column,
    },
  };
}
