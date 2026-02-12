import React, { useState, useEffect } from "react";
import {
  EvalStmtPhase,
  PcgProgramPointData,
  NavigatorPoint,
  CurrentPoint,
  FunctionSlug,
} from "../types";
import { DotFileAtPhase } from "../generated_types/DotFileAtPhase";
import {
  useLocalStorageBool,
  useLocalStorageNumber,
} from "../hooks/useLocalStorageState";
import { Api } from "../api";
import { openDotGraphInNewWindow } from "../dot_graph";
import { toBasicBlock } from "../util";
import { PcgBlockVisualizationData } from "../generated_types/PcgBlockVisualizationData";
import NavigationItemList, { NavigationItem } from "./NavigationItemList";

export const NAVIGATOR_DEFAULT_WIDTH = 200;
export const NAVIGATOR_MIN_WIDTH_NUM = 40;
export const NAVIGATOR_MAX_WIDTH = "200px";
export const NAVIGATOR_MIN_WIDTH = "40px";

const getPCGDotGraphFilename = (
  currentPoint: CurrentPoint,
  selectedFunction: string,
  graphs: PcgBlockVisualizationData
): string | null => {
  if (
    currentPoint.type !== "stmt" ||
    graphs.statements.length <= currentPoint.stmt
  ) {
    return null;
  }
  if (currentPoint.navigatorPoint.type === "action") {
    if (currentPoint.navigatorPoint.phase === "successor") {
      return null;
    }
    const stmt = graphs.statements[currentPoint.stmt];
    const iterationActions = stmt.actions;
    const actionGraphFilenames =
      iterationActions[currentPoint.navigatorPoint.phase];
    return `data/${selectedFunction}/${actionGraphFilenames[currentPoint.navigatorPoint.index]}`;
  }

  const navPoint = currentPoint.navigatorPoint;
  if (navPoint.type !== "iteration") {
    return null;
  }

  const phases = graphs.statements[currentPoint.stmt].graphs.at_phase;
  const phaseIndex = phases.findIndex((p) => p.phase === navPoint.name);

  if (phaseIndex === -1 || phases.length === 0) {
    return null;
  }

  const filename: string = phases[phaseIndex].filename;
  return `data/${selectedFunction}/${filename}`;
};

const formatCurrentPointTitle = (currentPoint: CurrentPoint): string => {
  if (currentPoint.type === "stmt") {
    const navPointName =
      currentPoint.navigatorPoint.type === "iteration"
        ? currentPoint.navigatorPoint.name
        : `${currentPoint.navigatorPoint.phase}[${currentPoint.navigatorPoint.index}]`;
    return `bb${currentPoint.block}[${currentPoint.stmt}] ${navPointName}`;
  } else {
    return `bb${currentPoint.block1} -> bb${currentPoint.block2}`;
  }
};

export default function PCGNavigator({
  selectedPoint,
  onSelectPoint,
  onNavigatorStateChange,
  onAdvanceToNextStatement,
  onGoToPreviousStatement,
  currentPoint,
  selectedFunction,
  pcgData,
  api,
}: {
  programPointData: PcgProgramPointData;
  selectedPoint: NavigatorPoint | null;
  onSelectPoint: (point: NavigatorPoint) => void;
  onNavigatorStateChange?: (isMinimized: boolean, width: number) => void;
  onAdvanceToNextStatement?: () => void;
  onGoToPreviousStatement?: () => void;
  currentPoint: CurrentPoint;
  selectedFunction: FunctionSlug;
  pcgData: PcgBlockVisualizationData;
  api: Api;
}) {
  const [isMinimized, setIsMinimized] = useLocalStorageBool(
    "pcgNavigatorMinimized",
    false
  );
  const [navigatorWidth, setNavigatorWidth] = useLocalStorageNumber(
    "pcgNavigatorWidth",
    NAVIGATOR_DEFAULT_WIDTH
  );
  const [isResizing, setIsResizing] = useState(false);

  // Notify parent of state changes
  useEffect(() => {
    if (onNavigatorStateChange) {
      onNavigatorStateChange(isMinimized, navigatorWidth);
    }
  }, [isMinimized, navigatorWidth, onNavigatorStateChange]);

  // Build navigation items list: for each iteration, render actions first then the phase
  const buildNavigationItems = (): NavigationItem[] => {
    const items: NavigationItem[] = [];

    if (currentPoint.type === "stmt") {
      const programPointData = pcgData.statements[currentPoint.stmt];
      programPointData.graphs.at_phase.forEach(
        (at_phase: DotFileAtPhase<string>) => {
          // Check if this iteration name corresponds to an EvalStmtPhase with actions
          const phase = at_phase.phase as EvalStmtPhase;
          if (phase in programPointData.graphs.actions) {
            // Add all actions for this phase first
            programPointData.actions[phase].forEach((action, index) => {
              items.push({ type: "action", phase, index, action });
            });
          }

          // Add the iteration after its actions
          items.push({
            type: "iteration",
            name: at_phase.phase,
            filename: at_phase.filename,
          });
        }
      );
    } else {
      const programPointData =
        pcgData.successors[toBasicBlock(currentPoint.block2)];
      programPointData.actions.forEach((action, index) => {
        items.push({ type: "action", phase: "successor", index, action });
      });
    }

    return items;
  };

  const navigationItems = buildNavigationItems();

  // Resize handlers
  const handleResizeStart = (event: React.MouseEvent) => {
    event.preventDefault();
    setIsResizing(true);
  };

  useEffect(() => {
    const handleResizeMove = (event: MouseEvent) => {
      if (isResizing) {
        const newWidth = window.innerWidth - event.clientX;
        const clampedWidth = Math.max(
          NAVIGATOR_MIN_WIDTH_NUM,
          Math.min(600, newWidth)
        );
        setNavigatorWidth(clampedWidth);
      }
    };

    const handleResizeEnd = () => {
      setIsResizing(false);
    };

    if (isResizing) {
      window.addEventListener("mousemove", handleResizeMove);
      window.addEventListener("mouseup", handleResizeEnd);
      return () => {
        window.removeEventListener("mousemove", handleResizeMove);
        window.removeEventListener("mouseup", handleResizeEnd);
      };
    }
  }, [isResizing, setNavigatorWidth]);

  // Keyboard navigation
  useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      if (event.key === "q" || event.key === "a") {
        event.preventDefault();

        if (navigationItems.length === 0) return;

        // Find current index
        let currentIndex = -1;
        if (selectedPoint) {
          if (selectedPoint.type === "action") {
            currentIndex = navigationItems.findIndex(
              (item) =>
                item.type === "action" &&
                item.phase === selectedPoint.phase &&
                item.index === selectedPoint.index
            );
          } else {
            currentIndex = navigationItems.findIndex(
              (item) =>
                item.type === "iteration" && item.name === selectedPoint.name
            );
          }
        }

        // Calculate new index
        let newIndex: number;
        if (currentIndex === -1) {
          newIndex = event.key === "q" ? navigationItems.length - 1 : 0;
        } else {
          if (event.key === "q") {
            // Pressing 'q' to go back
            if (currentIndex === 0) {
              // At the first step, go to previous statement instead of wrapping
              if (onGoToPreviousStatement) {
                onGoToPreviousStatement();
                return;
              }
              newIndex = navigationItems.length - 1;
            } else {
              newIndex = currentIndex - 1;
            }
          } else {
            // Pressing 'a' to advance
            if (currentIndex === navigationItems.length - 1) {
              // At the final step, advance to next statement instead of wrapping
              if (onAdvanceToNextStatement) {
                onAdvanceToNextStatement();
                return;
              }
              newIndex = 0;
            } else {
              newIndex = currentIndex + 1;
            }
          }
        }

        // Select the item
        const item = navigationItems[newIndex];
        if (item.type === "iteration") {
          onSelectPoint({ type: "iteration", name: item.name });
        } else {
          onSelectPoint({
            type: "action",
            phase: item.phase,
            index: item.index,
          });
        }
      }
    };

    window.addEventListener("keydown", handleKeyDown);
    return () => window.removeEventListener("keydown", handleKeyDown);
  }, [
    navigationItems,
    selectedPoint,
    onSelectPoint,
    onAdvanceToNextStatement,
    onGoToPreviousStatement,
  ]);

  const loopData = pcgData.loop_data;

  return (
    <div
      style={{
        position: "fixed",
        right: 0,
        top: 0,
        bottom: 0,
        width: isMinimized ? NAVIGATOR_MIN_WIDTH : `${navigatorWidth}px`,
        backgroundColor: "white",
        boxShadow: "-2px 0 5px rgba(0,0,0,0.1)",
        display: "flex",
        flexDirection: "column",
        zIndex: 1000,
      }}
    >
      {!isMinimized && (
        <div
          onMouseDown={handleResizeStart}
          style={{
            position: "absolute",
            left: 0,
            top: 0,
            bottom: 0,
            width: "5px",
            cursor: "ew-resize",
            backgroundColor: isResizing ? "#007acc" : "transparent",
            transition: "background-color 0.2s",
            zIndex: 1001,
          }}
          onMouseEnter={(e) => {
            e.currentTarget.style.backgroundColor = "#007acc";
          }}
          onMouseLeave={(e) => {
            if (!isResizing) {
              e.currentTarget.style.backgroundColor = "transparent";
            }
          }}
        />
      )}
      <div
        style={{
          display: "flex",
          alignItems: "center",
          justifyContent: "space-between",
          padding: "10px",
          borderBottom: "1px solid #ddd",
          backgroundColor: "#f5f5f5",
          flexShrink: 0,
        }}
      >
        {!isMinimized && (
          <h3 style={{ margin: 0, fontSize: "14px", fontWeight: "bold" }}>
            Navigator
          </h3>
        )}
        <div style={{ display: "flex", gap: "5px", marginLeft: "auto" }}>
          <button
            onClick={() => setIsMinimized(!isMinimized)}
            style={{
              cursor: "pointer",
              backgroundColor: "#888",
              color: "white",
              border: "none",
              borderRadius: "4px",
              padding: "5px 8px",
              fontSize: "12px",
            }}
            title={isMinimized ? "Maximize" : "Minimize"}
          >
            {isMinimized ? "▶" : "◀"}
          </button>
        </div>
      </div>
      {!isMinimized && (
        <>
          <div
            style={{
              flex: 1,
              overflowY: "auto",
              padding: "15px",
            }}
          >
            {loopData ? (
              <div>
                <b>Loop Head</b>
                {Object.keys(loopData.used_places.usages).map((k) => {
                  return (
                    <div key={k}>
                      {k}: {loopData.used_places.usages[k]}
                    </div>
                  );
                })}
              </div>
            ) : null}
            <NavigationItemList
              navigationItems={navigationItems}
              selectedPoint={selectedPoint}
              onSelectPoint={onSelectPoint}
            />
          </div>
          <button
            style={{
              margin: "10px",
              padding: "8px",
              cursor: "pointer",
              backgroundColor: "#007acc",
              color: "white",
              border: "none",
              borderRadius: "4px",
              fontSize: "12px",
            }}
            onClick={async () => {
              const dotFilePath = getPCGDotGraphFilename(
                currentPoint,
                selectedFunction,
                pcgData
              );
              if (dotFilePath) {
                const title = formatCurrentPointTitle(currentPoint);
                openDotGraphInNewWindow(api, dotFilePath, title);
              }
            }}
          >
            Open Current PCG in New Window
          </button>
          <div
            style={{
              padding: "10px",
              fontSize: "12px",
              color: "#666",
              borderTop: "1px solid #ddd",
              backgroundColor: "#f5f5f5",
              flexShrink: 0,
            }}
          >
            Press &apos;q&apos;/&apos;a&apos; to navigate between phases and
            actions
          </div>
        </>
      )}
      {isMinimized && (
        <div
          style={{
            flex: 1,
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            writingMode: "vertical-rl",
            fontSize: "12px",
            color: "#666",
          }}
        >
          Navigator
        </div>
      )}
    </div>
  );
}
