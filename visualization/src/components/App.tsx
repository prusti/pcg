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
  NavigatorPoint,
  PathData,
  PcgProgramPointData,
  SourcePos,
  StringOf,
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
import PCGNavigator, { NAVIGATOR_MIN_WIDTH } from "./PCGNavigator";
import PathSelector from "./PathSelector";
import {
  addKeyDownListener,
  reloadPathData,
  reloadIterations,
} from "../effects";
import BorrowCheckerGraphs from "./BorrowCheckerGraphs";
import SourceCodeViewer from "./SourceCodeViewer";
import {
  DotFileAtPhase,
  EvalStmtData,
  MirEdge,
  MirNode,
} from "../generated/types";

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
  graphs: PcgBlockDotGraphs
): string | null {
  if (currentPoint.type !== "stmt" || graphs.length <= currentPoint.stmt) {
    return null;
  }
  if (currentPoint.navigatorPoint.type === "action") {
    // Successor actions (from terminator edges) don't have PCG dot graphs
    if (currentPoint.navigatorPoint.phase === "successor") {
      return null;
    }
    const iterationActions = getIterationActions(graphs, currentPoint);
    const actionGraphFilenames = iterationActions[currentPoint.navigatorPoint.phase];
    return getActionGraphFilename(
      selectedFunction,
      actionGraphFilenames,
      currentPoint.navigatorPoint.index
    );
  }

  // For iteration type, find the phase by name
  const navPoint = currentPoint.navigatorPoint;
  if (navPoint.type !== "iteration") {
    return null;
  }

  const phases: DotFileAtPhase<StringOf<"DataflowStmtPhase">>[] =
    graphs[currentPoint.stmt].at_phase;

  // Find the phase by name
  const phaseIndex = phases.findIndex(
    (p) => p.phase === navPoint.name
  );

  if (phaseIndex === -1 || phases.length === 0) {
    return null;
  }

  const filename: string = phases[phaseIndex].filename;
  return `data/${selectedFunction}/${filename}`;
}

interface AppProps {
  initialFunction: FunctionSlug;
  functions: FunctionsMetadata;
  initialPath?: number;
  api: Api;
  onApiChange: (newApi: Api) => void;
}

export const App: React.FC<AppProps> = ({
  initialFunction,
  functions,
  initialPath = 0,
  api,
  onApiChange,
}) => {
  const [iterations, setIterations] = useState<PcgBlockDotGraphs>([]);
  const [pathData, setPathData] = useState<PathData | null>(null);
  const [pcgProgramPointData, setPcgProgramPointData] =
    useState<PcgProgramPointData | null>(null);
  const [allPcgStmtData, setAllPcgStmtData] =
    useState<Map<number, Map<number, PcgProgramPointData>>>(new Map());
  const [currentPoint, setCurrentPoint] = useState<CurrentPoint>({
    type: "stmt",
    block: 0,
    stmt: 0,
    navigatorPoint: {
      type: "iteration",
      name: "initial",
    },
  });

  const [selectedFunction, setSelectedFunction] = useState<FunctionSlug>(
    initialFunction || (Object.keys(functions)[0] as FunctionSlug)
  );
  const [selectedPath, setSelectedPath] = useState<number>(initialPath);
  const [paths] = useState<number[][]>([]);
  const [assertions] = useState<Assertion[]>([]);
  const [nodes, setNodes] = useState<MirNode[]>([]);
  const [edges, setEdges] = useState<MirEdge[]>([]);
  const [showPathBlocksOnly, setShowPathBlocksOnly] = useState(
    storage.getBool("showPathBlocksOnly", false)
  );
  const [showUnwindEdges] = useState(false);
  const [showPCG, setShowPCG] = useState(storage.getBool("showPCG", true));
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
  const [showActionsInCode, setShowActionsInCode] = useState(
    storage.getBool("showActionsInCode", false)
  );
  const [hoverPosition, setHoverPosition] = useState<SourcePos | null>(null);
  const [clickPosition, setClickPosition] = useState<SourcePos | null>(null);
  const [clickCycleIndex, setClickCycleIndex] = useState<number>(0);

  // Track PCG Navigator state for layout adjustment
  const [navigatorDocked] = useState(
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
  }, [api, iterations, currentPoint, selectedFunction]);

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

  // Load all PCG statement data for the function (for "show actions in code" feature)
  useEffect(() => {
    const fetchAllPcgStmtData = async () => {
      try {
        const allData = await api.getAllPcgStmtData(selectedFunction);
        setAllPcgStmtData(allData);
      } catch (error) {
        console.error("Error fetching all pcg stmt data:", error);
        setAllPcgStmtData(new Map());
      }
    };

    fetchAllPcgStmtData();
  }, [api, selectedFunction]);

  useEffect(() => {
    reloadIterations(api, selectedFunction, currentPoint, setIterations);
  }, [api, selectedFunction, currentPoint]);


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
    storage.setItem("showActionsInCode", showActionsInCode.toString());
  }, [showActionsInCode]);

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

  const handleNavigatorStateChange = useCallback(
    (isMinimized: boolean, width: number) => {
      setNavigatorMinimized(isMinimized);
      setNavigatorWidth(width);
    },
    []
  );

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

  const getOverlappingStmts = useCallback((position: SourcePos) => {
    const functionStart = functions[selectedFunction].start;
    const absolutePosition: SourcePos = {
      line: position.line + functionStart.line,
      column: position.column + functionStart.column,
    };

    const overlappingStmts: Array<{block: number, stmt: number, stmtId: string}> = [];
    nodes.forEach((node) => {
      const checkStmt = (stmt: MirStmt, stmtIndex: number) => {
        const span = stmt.span;

        // Only consider statements whose span is contained within a single line
        if (span.low.line !== span.high.line) {
          return;
        }

        const spanOverlaps =
          (absolutePosition.line > span.low.line ||
           (absolutePosition.line === span.low.line && absolutePosition.column >= span.low.column)) &&
          (absolutePosition.line < span.high.line ||
           (absolutePosition.line === span.high.line && absolutePosition.column < span.high.column));

        if (spanOverlaps) {
          overlappingStmts.push({
            block: node.block,
            stmt: stmtIndex,
            stmtId: `${node.block}-${stmtIndex}`
          });
        }
      };

      node.stmts.forEach((stmt, idx) => checkStmt(stmt, idx));
      checkStmt(node.terminator, node.stmts.length);
    });

    return overlappingStmts;
  }, [nodes, selectedFunction, functions]);

  const hoveredStmts = useMemo(() => {
    if (!hoverPosition) {
      return new Set<string>();
    }

    const overlapping = getOverlappingStmts(hoverPosition);
    return new Set(overlapping.map(s => s.stmtId));
  }, [hoverPosition, getOverlappingStmts]);

  const selectionIndicator = useMemo(() => {
    if (!clickPosition || !highlightSpan) {
      return null;
    }

    const overlapping = getOverlappingStmts(clickPosition);
    if (overlapping.length <= 1) {
      return null;
    }

    const currentStmtId = currentPoint.type === "stmt"
      ? `${currentPoint.block}-${currentPoint.stmt}`
      : null;

    if (!currentStmtId) {
      return null;
    }

    const currentIndex = overlapping.findIndex(s => s.stmtId === currentStmtId);
    if (currentIndex === -1) {
      return null;
    }

    return {
      line: clickPosition.line,
      index: currentIndex + 1, // 1-based
      total: overlapping.length,
    };
  }, [clickPosition, highlightSpan, getOverlappingStmts, currentPoint]);

  const handleClickPosition = useCallback((position: SourcePos) => {
    // Check if clicking at the same position
    const isSamePosition = clickPosition &&
      clickPosition.line === position.line &&
      clickPosition.column === position.column;

    if (isSamePosition) {
      // Increment cycle index
      const overlapping = getOverlappingStmts(position);
      if (overlapping.length > 0) {
        const nextIndex = (clickCycleIndex + 1) % overlapping.length;
        setClickCycleIndex(nextIndex);

        const selected = overlapping[nextIndex];
        setCurrentPoint({
          type: "stmt",
          block: selected.block,
          stmt: selected.stmt,
          navigatorPoint: { type: "iteration", name: "post_main" },
        });
      }
    } else {
      // New position - select first overlapping statement
      setClickPosition(position);
      setClickCycleIndex(0);

      const overlapping = getOverlappingStmts(position);
      if (overlapping.length > 0) {
        const selected = overlapping[0];
        setCurrentPoint({
          type: "stmt",
          block: selected.block,
          stmt: selected.stmt,
          navigatorPoint: { type: "iteration", name: "post_main" },
        });
      }
    }
  }, [clickPosition, clickCycleIndex, getOverlappingStmts]);

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
          <SourceCodeViewer
            metadata={functions[selectedFunction]}
            functions={functions}
            selectedFunction={selectedFunction}
            onFunctionChange={setSelectedFunction}
            highlightSpan={highlightSpan}
            minimized={isSourceCodeMinimized}
            fontSize={codeFontSize}
            onHoverPositionChange={setHoverPosition}
            onClickPosition={handleClickPosition}
            selectionIndicator={selectionIndicator}
            showSettings={showSettings}
            onToggleSettings={() => setShowSettings(!showSettings)}
            onFontSizeChange={setCodeFontSize}
            onToggleMinimized={() => setIsSourceCodeMinimized(!isSourceCodeMinimized)}
            showActionsInCode={showActionsInCode}
            nodes={nodes}
            allPcgStmtData={allPcgStmtData}
            onActionClick={(block, stmt) => {
              setCurrentPoint({
                type: "stmt",
                block,
                stmt,
                navigatorPoint: { type: "iteration", name: "post_main" },
              });
            }}
          />
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
              <h4 style={{ marginTop: 0, marginBottom: "10px" }}>
                Data Source
              </h4>
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
                  checked={showActionsInCode}
                  onChange={(e) => setShowActionsInCode(e.target.checked)}
                />{" "}
                Show Actions in Code
              </label>
              <label style={{ display: "block", marginBottom: "10px" }}>
                <input
                  type="checkbox"
                  checked={showPCG}
                  onChange={(e) => setShowPCG(e.target.checked)}
                />{" "}
                Show PCG
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
                />{" "}
                Show PCG Navigator
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
          hoveredStmts={hoveredStmts}
        />
        {showPCGNavigator &&
          pcgProgramPointData &&
          ((currentPoint.type === "stmt" &&
            iterations.length > currentPoint.stmt &&
            !Array.isArray(pcgProgramPointData.actions)) ||
            (currentPoint.type === "terminator" &&
              Array.isArray(pcgProgramPointData.actions))) && (
            <PCGNavigator
              iterations={
                currentPoint.type === "stmt"
                  ? iterations[currentPoint.stmt]
                  : undefined
              }
              pcgData={pcgProgramPointData}
              selectedPoint={
                currentPoint.type === "stmt"
                  ? currentPoint.navigatorPoint
                  : currentPoint.navigatorPoint || null
              }
              onSelectPoint={(point: NavigatorPoint) => {
                if (currentPoint.type === "stmt") {
                  setCurrentPoint({
                    ...currentPoint,
                    navigatorPoint: point,
                  });
                } else if (currentPoint.type === "terminator") {
                  setCurrentPoint({
                    ...currentPoint,
                    navigatorPoint: point,
                  });
                }
              }}
              onNavigatorStateChange={handleNavigatorStateChange}
              onAdvanceToNextStatement={() => {
                if (currentPoint.type === "stmt") {
                  const currentNode = nodes.find(
                    (node) => node.block === currentPoint.block
                  );
                  if (currentNode) {
                    const nextStmt = currentPoint.stmt + 1;
                    if (nextStmt <= currentNode.stmts.length) {
                      setCurrentPoint({
                        ...currentPoint,
                        stmt: nextStmt,
                        navigatorPoint: { type: "iteration", name: "initial" },
                      });
                    } else {
                      // At last statement, move to next block
                      const currBlockIdx = filteredNodes.findIndex(
                        (node) => node.block === currentPoint.block
                      );
                      if (currBlockIdx !== -1) {
                        const nextBlockIdx =
                          (currBlockIdx + 1) % filteredNodes.length;
                        const nextNode = filteredNodes[nextBlockIdx];
                        setCurrentPoint({
                          type: "stmt",
                          block: nextNode.block,
                          stmt: 0,
                          navigatorPoint: { type: "iteration", name: "initial" },
                        });
                      }
                    }
                  }
                }
              }}
              onGoToPreviousStatement={() => {
                if (currentPoint.type === "stmt") {
                  let targetBlock: number;
                  let targetStmt: number;

                  if (currentPoint.stmt > 0) {
                    // Move to previous statement in same block
                    targetBlock = currentPoint.block;
                    targetStmt = currentPoint.stmt - 1;
                  } else {
                    // At first statement, move to previous block
                    const currBlockIdx = filteredNodes.findIndex(
                      (node) => node.block === currentPoint.block
                    );
                    if (currBlockIdx === -1) return;

                    const prevBlockIdx =
                      (currBlockIdx - 1 + filteredNodes.length) %
                      filteredNodes.length;
                    const prevNode = filteredNodes[prevBlockIdx];
                    targetBlock = prevNode.block;
                    targetStmt = prevNode.stmts.length;
                  }

                  // Set to post_main when going to previous statement
                  setCurrentPoint({
                    type: "stmt",
                    block: targetBlock,
                    stmt: targetStmt,
                    navigatorPoint: { type: "iteration", name: "post_main" },
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
