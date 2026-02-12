import React from "react";
import {
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
} from "react";
import { api, ApiFunctionData } from "../api";
import {
  CurrentPoint,
  FunctionSlug,
  FunctionsMetadata,
  NavigatorPoint,
  PcgProgramPointData,
  SourcePos,
} from "../types";
import {
  useLocalStorageBool,
  useLocalStorageNumber,
  useLocalStorageString,
} from "../hooks/useLocalStorageState";
import { toBasicBlock } from "../util";
import { filterNodesAndEdges } from "../mir_graph";
import { addKeyDownListener } from "../effects";
import PCGNavigator, { NAVIGATOR_MIN_WIDTH } from "./PCGNavigator";
import { MirNode } from "../generated_types/MirNode";
import { MirStmt } from "../generated_types/MirStmt";
import SourceCodeViewer from "./SourceCodeViewer";
import Settings from "./Settings";
import MirGraph from "./MirGraph";
import PcgGraph from "./PcgGraph";

interface AppInnerProps {
  apiFunctionData: ApiFunctionData;
  functions: FunctionsMetadata;
  currentPoint: CurrentPoint;
  setCurrentPoint: React.Dispatch<React.SetStateAction<CurrentPoint>>;
  selectedFunction: FunctionSlug;
  setSelectedFunction: (functionSlug: FunctionSlug) => void;
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

export const AppInner: React.FC<AppInnerProps> = ({
  apiFunctionData,
  functions,
  currentPoint,
  setCurrentPoint,
  selectedFunction,
  setSelectedFunction,
}) => {
  const [showUnwindEdges] = useState(false);
  const [showPCG, setShowPCG] = useLocalStorageBool("showPCG", true);
  const [showPCGNavigator, setShowPCGNavigator] = useLocalStorageBool(
    "showPCGNavigator",
    true
  );
  const [showSettings, setShowSettings] = useLocalStorageBool(
    "showSettings",
    false
  );
  const [isSourceCodeMinimized, setIsSourceCodeMinimized] = useLocalStorageBool(
    "isSourceCodeMinimized",
    false
  );
  const [codeFontSize, setCodeFontSize] = useLocalStorageNumber(
    "codeFontSize",
    12
  );
  const [showActionsInCode, setShowActionsInCode] = useLocalStorageBool(
    "showActionsInCode",
    false
  );
  const [hoverPosition, setHoverPosition] = useState<SourcePos | null>(null);
  const [clickPosition, setClickPosition] = useState<SourcePos | null>(null);
  const [clickCycleIndex, setClickCycleIndex] = useState<number>(0);

  // Track highlighted MIR edges based on PCG edge hover
  const [highlightedMirEdges, setHighlightedMirEdges] = useState<Set<string>>(
    new Set()
  );

  // Track PCG Navigator state for layout adjustment
  const [navigatorMinimized, setNavigatorMinimized] = useLocalStorageBool(
    "pcgNavigatorMinimized",
    false
  );
  const [navigatorWidth, setNavigatorWidth] = useLocalStorageNumber(
    "pcgNavigatorWidth",
    200
  );

  // State for panel resizing
  const [leftPanelWidth, setLeftPanelWidth] = useLocalStorageString<string>(
    "leftPanelWidth",
    "50%"
  );
  const [isDragging, setIsDragging] = useState<boolean>(false);
  const dividerRef = useRef<HTMLDivElement>(null);

  const nodes = apiFunctionData.mirGraph.nodes;
  const edges = apiFunctionData.mirGraph.edges;

  const pcgData = apiFunctionData.pcgData;

  let pcgProgramPointData: PcgProgramPointData | null = null;

  if (currentPoint.type === "stmt") {
    const blockData = pcgData[toBasicBlock(currentPoint.block)];
    if (blockData) {
      pcgProgramPointData = blockData.statements[currentPoint.stmt] || null;
    }
  } else {
    const blockData = pcgData[toBasicBlock(currentPoint.block1)];
    if (blockData) {
      pcgProgramPointData =
        blockData.successors[toBasicBlock(currentPoint.block2)] || null;
    }
  }

  const { filteredNodes } = filterNodesAndEdges(nodes, edges, {
    showUnwindEdges,
    path: null,
  });

  useEffect(() => {
    return addKeyDownListener(nodes, filteredNodes, setCurrentPoint);
  }, [nodes, filteredNodes, setCurrentPoint]);

  const handleNavigatorStateChange = useCallback(
    (isMinimized: boolean, width: number) => {
      setNavigatorMinimized(isMinimized);
      setNavigatorWidth(width);
    },
    [setNavigatorMinimized, setNavigatorWidth]
  );

  // Calculate the width to reserve for the navigator
  const navigatorReservedWidth = useMemo(() => {
    if (!showPCGNavigator) {
      return "0px";
    }
    return navigatorMinimized ? NAVIGATOR_MIN_WIDTH : `${navigatorWidth}px`;
  }, [showPCGNavigator, navigatorMinimized, navigatorWidth]);

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

  const getOverlappingStmts = useCallback(
    (position: SourcePos) => {
      const functionStart = functions[selectedFunction].start;
      const absolutePosition: SourcePos = {
        line: position.line + functionStart.line,
        column: position.column + functionStart.column,
      };

      const overlappingStmts: Array<{
        block: number;
        stmt: number;
        stmtId: string;
      }> = [];
      nodes.forEach((node) => {
        const checkStmt = (stmt: MirStmt, stmtIndex: number) => {
          const span = stmt.span;

          // Only consider statements whose span is contained within a single line
          if (span.low.line !== span.high.line) {
            return;
          }

          const spanOverlaps =
            (absolutePosition.line > span.low.line ||
              (absolutePosition.line === span.low.line &&
                absolutePosition.column >= span.low.column)) &&
            (absolutePosition.line < span.high.line ||
              (absolutePosition.line === span.high.line &&
                absolutePosition.column < span.high.column));

          if (spanOverlaps) {
            overlappingStmts.push({
              block: node.block,
              stmt: stmtIndex,
              stmtId: `${node.block}-${stmtIndex}`,
            });
          }
        };

        node.stmts.forEach((stmt, idx) => checkStmt(stmt, idx));
        checkStmt(node.terminator, node.stmts.length);
      });

      return overlappingStmts;
    },
    [nodes, selectedFunction, functions]
  );

  const hoveredStmts = useMemo(() => {
    if (!hoverPosition) {
      return new Set<string>();
    }

    const overlapping = getOverlappingStmts(hoverPosition);
    return new Set(overlapping.map((s) => s.stmtId));
  }, [hoverPosition, getOverlappingStmts]);

  const selectionIndicator = useMemo(() => {
    if (!clickPosition || !highlightSpan) {
      return null;
    }

    const overlapping = getOverlappingStmts(clickPosition);
    if (overlapping.length <= 1) {
      return null;
    }

    const currentStmtId =
      currentPoint.type === "stmt"
        ? `${currentPoint.block}-${currentPoint.stmt}`
        : null;

    if (!currentStmtId) {
      return null;
    }

    const currentIndex = overlapping.findIndex(
      (s) => s.stmtId === currentStmtId
    );
    if (currentIndex === -1) {
      return null;
    }

    return {
      line: clickPosition.line,
      index: currentIndex + 1, // 1-based
      total: overlapping.length,
    };
  }, [clickPosition, highlightSpan, getOverlappingStmts, currentPoint]);

  const handleClickPosition = useCallback(
    (position: SourcePos) => {
      // Check if clicking at the same position
      const isSamePosition =
        clickPosition &&
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
        const overlapping = getOverlappingStmts(position);
        if (overlapping.length > 0) {
          const selected = overlapping[0];
          // New position - select first overlapping statement
          setClickPosition(position);
          setClickCycleIndex(0);
          setCurrentPoint({
            type: "stmt",
            block: selected.block,
            stmt: selected.stmt,
            navigatorPoint: { type: "iteration", name: "post_main" },
          });
        }
      }
    },
    [clickPosition, clickCycleIndex, getOverlappingStmts, setCurrentPoint]
  );

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
    [isDragging, setLeftPanelWidth]
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

  const currentBlock = toBasicBlock(
    currentPoint.type === "stmt" ? currentPoint.block : currentPoint.block1
  );

  const currentBlockData = apiFunctionData?.pcgData[currentBlock];

  return (
    <div style={{ display: "flex", width: "100%", height: "100vh" }}>
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
            onToggleMinimized={() =>
              setIsSourceCodeMinimized(!isSourceCodeMinimized)
            }
          />
        </div>

        <Settings
          showSettings={showSettings}
          onClose={() => setShowSettings(false)}
          showActionsInCode={showActionsInCode}
          setShowActionsInCode={setShowActionsInCode}
          showPCG={showPCG}
          setShowPCG={setShowPCG}
          showPCGNavigator={showPCGNavigator}
          setShowPCGNavigator={setShowPCGNavigator}
          currentPoint={currentPoint}
          selectedFunction={selectedFunction}
          api={api}
        />
        <MirGraph
          edges={edges}
          mirNodes={nodes}
          currentPoint={currentPoint}
          setCurrentPoint={setCurrentPoint}
          hoveredStmts={hoveredStmts}
          showActionsInGraph={showActionsInCode}
          apiData={apiFunctionData}
          highlightedEdges={highlightedMirEdges}
        />
        {showPCGNavigator && currentBlockData && pcgProgramPointData && (
          <PCGNavigator
            pcgData={currentBlockData}
            programPointData={pcgProgramPointData}
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
            currentPoint={currentPoint}
            selectedFunction={selectedFunction}
            api={api}
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
                        navigatorPoint: {
                          type: "iteration",
                          name: "initial",
                        },
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
      {currentBlockData && (
        <PcgGraph
          pcgData={currentBlockData}
          showPCG={showPCG}
          navigatorReservedWidth={navigatorReservedWidth}
          currentPoint={currentPoint}
          selectedFunction={selectedFunction}
          api={api}
          onHighlightMirEdges={setHighlightedMirEdges}
        />
      )}
    </div>
  );
};
