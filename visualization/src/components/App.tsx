import React, {
  useState,
  useEffect,
  useCallback,
  useMemo,
  useRef,
} from "react";
import * as Viz from "@viz-js/viz";
import { openDotGraphInNewWindow } from "../dot_graph";

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
import { Api, PcgBlockDotGraphs, ZipFileApi } from "../api";
import {
  filterNodesAndEdges,
  layoutUnsizedNodes,
  toDagreEdges,
} from "../mir_graph";
import { cacheZip } from "../zipCache";
import { storage } from "../storage";
import FunctionSelector from "./FunctionSelector";
import PCGNavigator, { NAVIGATOR_MIN_WIDTH } from "./PCGNavigator";
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
  selected: number | null,
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

  // Handle deselection case or null selection
  if (selected === null || selected < 0 || phases.length === 0) {
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
  api: Api;
  onApiChange: (newApi: Api) => void;
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
  api,
  onApiChange,
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
    initialFunction || (Object.keys(functions)[0] as FunctionSlug)
  );
  const [selectedPath, setSelectedPath] = useState<number>(initialPath);
  const [paths, setPaths] = useState<number[][]>(initialPaths);
  const [assertions] = useState<Assertion[]>(initialAssertions);
  const [nodes, setNodes] = useState<MirNode[]>([]);
  const [edges, setEdges] = useState<MirEdge[]>([]);
  const [showPathBlocksOnly, setShowPathBlocksOnly] = useState(
    storage.getBool("showPathBlocksOnly", false)
  );
  const [showUnwindEdges] = useState(false);
  const [showPCG, setShowPCG] = useState(
    storage.getBool("showPCG", true)
  );
  const [showPCGNavigator, setShowPCGNavigator] = useState(
    storage.getBool("showPCGNavigator", true)
  );
  const [showSettings, setShowSettings] = useState(
    storage.getBool("showSettings", false)
  );
  const [isSourceCodeMinimized, setIsSourceCodeMinimized] = useState(
    storage.getBool("isSourceCodeMinimized", false)
  );
  const [codeFontSize, setCodeFontSize] = useState<number>(
    parseInt(storage.getItem("codeFontSize") || "12")
  );

  // Track PCG Navigator state for layout adjustment
  const [navigatorDocked, setNavigatorDocked] = useState(
    storage.getBool("pcgNavigatorDocked", true)
  );
  const [navigatorMinimized, setNavigatorMinimized] = useState(
    storage.getBool("pcgNavigatorMinimized", false)
  );
  const [navigatorWidth, setNavigatorWidth] = useState(() => {
    const stored = storage.getItem("pcgNavigatorWidth");
    return stored ? parseInt(stored, 10) : 200;
  });

  // State for panel resizing
  const [leftPanelWidth, setLeftPanelWidth] = useState<string>(
    storage.getItem("leftPanelWidth") || "50%"
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

  const loadPCGDotGraph = useCallback(async () => {
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
      const dotData = await api.fetchDotFile(dotFilePath);

      Viz.instance().then(function (viz) {
        dotGraph.innerHTML = "";
        dotGraph.appendChild(viz.renderSVGElement(dotData));
      });
    }
  }, [api, iterations, currentPoint, selectedFunction, selected]);

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
  }, [loadPCGDotGraph]);

  useEffect(() => {
    if (selectedFunction) {
      (async function () {
        const mirGraph = await api.getGraphData(selectedFunction);
        setNodes(mirGraph.nodes);
        setEdges(mirGraph.edges);
        setPaths(await api.getPaths(selectedFunction));
      })();
    }
  }, [api, selectedFunction]);

  useEffect(() => {
    const fetchPcgStmtVisualizationData = async () => {
      try {
        const pcgStmtVisualizationData = await api.getPcgProgramPointData(
          selectedFunction,
          currentPoint
        );
        setPcgProgramPointData(pcgStmtVisualizationData);
      } catch (error) {
        console.error("Error fetching pcg stmt visualization data:", error);
      }
    };

    reloadPathData(
      api,
      selectedFunction,
      selectedPath,
      currentPoint,
      paths,
      setPathData
    );
    fetchPcgStmtVisualizationData();
  }, [api, selectedFunction, selectedPath, currentPoint, paths]);

  const currentBlock = currentPoint.type === "stmt" ? currentPoint.block : null;
  const currentStmt = currentPoint.type === "stmt" ? currentPoint.stmt : null;

  useEffect(() => {
    reloadIterations(api, selectedFunction, currentPoint, setIterations);
  }, [api, selectedFunction, currentPoint]);

  useEffect(() => {
    // Reset selected phase when changing function/block/stmt
    // eslint-disable-next-line react-hooks/set-state-in-effect
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
      // Initialize selected phase based on available phases
      if (postMainIndex !== -1) {
        // eslint-disable-next-line react-hooks/set-state-in-effect
        setSelected(postMainIndex);
      } else if (phases.length > 0) {
        setSelected(phases.length - 1);
      }
    }
  }, [iterations, currentPoint, selected]);

  useEffect(() => {
    return addKeyDownListener(nodes, filteredNodes, setCurrentPoint);
  }, [nodes, filteredNodes, showPathBlocksOnly, setCurrentPoint]);

  useEffect(() => {
    storage.setItem("selectedFunction", selectedFunction.toString());
  }, [selectedFunction]);

  useEffect(() => {
    storage.setItem("selectedPath", selectedPath.toString());
  }, [selectedPath]);

  useEffect(() => {
    storage.setItem("showPathBlocksOnly", showPathBlocksOnly.toString());
  }, [showPathBlocksOnly]);

  useEffect(() => {
    storage.setItem("showPCG", showPCG.toString());
  }, [showPCG]);

  useEffect(() => {
    storage.setItem("showPCGNavigator", showPCGNavigator.toString());
  }, [showPCGNavigator]);

  useEffect(() => {
    storage.setItem("showSettings", showSettings.toString());
  }, [showSettings]);

  useEffect(() => {
    storage.setItem("isSourceCodeMinimized", isSourceCodeMinimized.toString());
  }, [isSourceCodeMinimized]);

  useEffect(() => {
    storage.setItem("codeFontSize", codeFontSize.toString());
  }, [codeFontSize]);

  useEffect(() => {
    storage.setItem("leftPanelWidth", leftPanelWidth.toString());
  }, [leftPanelWidth]);

  const isBlockOnSelectedPath = useCallback(
    (block: number) => {
      if (paths.length === 0 || selectedPath >= paths.length) return false;
      return paths[selectedPath].includes(block);
    },
    [paths, selectedPath]
  );

  const handleNavigatorStateChange = useCallback((isDocked: boolean, isMinimized: boolean, width: number) => {
    setNavigatorDocked(isDocked);
    setNavigatorMinimized(isMinimized);
    setNavigatorWidth(width);
  }, []);

  // Calculate the width to reserve for the navigator when it's docked
  const navigatorReservedWidth = useMemo(() => {
    if (!showPCGNavigator || !navigatorDocked) {
      return "0px";
    }
    return navigatorMinimized ? NAVIGATOR_MIN_WIDTH : `${navigatorWidth}px`;
  }, [showPCGNavigator, navigatorDocked, navigatorMinimized, navigatorWidth]);

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
              zIndex: 1100,
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
              <h4 style={{ marginTop: 0, marginBottom: "10px" }}>Data Source</h4>
              <input
                type="file"
                accept=".zip"
                id="zip-file-input"
                style={{ display: "none" }}
                onChange={async (e) => {
                  const file = e.target.files?.[0];
                  if (file) {
                    const zipApi = await ZipFileApi.fromFile(file);
                    await cacheZip(zipApi);
                    onApiChange(zipApi);
                  }
                }}
              />
              <button
                style={{
                  width: "100%",
                  padding: "8px",
                  cursor: "pointer",
                  backgroundColor: "#4CAF50",
                  color: "white",
                  border: "none",
                  borderRadius: "4px",
                }}
                onClick={() => {
                  document.getElementById("zip-file-input")?.click();
                }}
              >
                Upload Zip File
              </button>
            </div>

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
                    openDotGraphInNewWindow(api, dotFilePath);
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
                api={api}
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
              onNavigatorStateChange={handleNavigatorStateChange}
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

      <div
        id="pcg-graph"
        style={{
          flex: 1,
          overflow: "auto",
          marginRight: navigatorReservedWidth,
        }}
      ></div>
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
