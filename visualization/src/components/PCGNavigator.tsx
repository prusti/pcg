import React, { useState, useEffect } from "react";
import {
  EvalStmtPhase,
  PcgAction,
  PcgStmtVisualizationData,
  StringOf,
  NavigatorPoint,
} from "../types";
import {
  BorrowPcgActionKindDebugRepr,
  CapabilityKind,
  RepackOp,
  StmtGraphs,
} from "../generated/types";
import { storage } from "../storage";

type NavigationItem =
  | { type: "phase"; index: number; name: string; filename: string }
  | {
      type: "action";
      phase: EvalStmtPhase;
      index: number;
      action: PcgAction;
    };

export const NAVIGATOR_DEFAULT_WIDTH = 200;
export const NAVIGATOR_MIN_WIDTH_NUM = 40;
export const NAVIGATOR_MAX_WIDTH = "200px";
export const NAVIGATOR_MIN_WIDTH = "40px";

function capabilityLetter(capability: CapabilityKind): string {
  switch (capability) {
    case "Read":
      return "R";
    case "Write":
      return "W";
    case "Exclusive":
      return "E";
    case "ShallowExclusive":
      return "e";
  }
}

function actionLine(
  action: RepackOp<string, string, string> | BorrowPcgActionKindDebugRepr
): string {
  switch (action.type) {
    case "Expand":
      return `Unpack ${action.data.from}`;
    case "Collapse":
      return `Pack ${action.data.to}`;
    case "AddEdge":
    case "RemoveEdge":
    case "Restore":
    case "Weaken":
      return String(action.data);
    case "RegainLoanedCapability":
      return `Restore capability ${capabilityLetter(action.data.capability)} to ${action.data.place}`;
    default:
      return JSON.stringify(action);
  }
}

export default function PCGNavigator({
  iterations,
  pcgData,
  selectedPoint,
  selectFirstItem,
  onSelectPoint,
  onNavigatorStateChange,
  onAdvanceToNextStatement,
  onClearSelectFirstItem,
}: {
  iterations: StmtGraphs<StringOf<"DataflowStmtPhase">>;
  pcgData: PcgStmtVisualizationData;
  selectedPoint: NavigatorPoint | null;
  selectFirstItem: boolean;
  onSelectPoint: (point: NavigatorPoint) => void;
  onNavigatorStateChange?: (isMinimized: boolean, width: number) => void;
  onAdvanceToNextStatement?: () => void;
  onClearSelectFirstItem: () => void;
}) {
  const [isMinimized, setIsMinimized] = useState(() => {
    return storage.getBool("pcgNavigatorMinimized", false);
  });
  const [navigatorWidth, setNavigatorWidth] = useState(() => {
    return storage.getNumber("pcgNavigatorWidth", NAVIGATOR_DEFAULT_WIDTH);
  });
  const [isResizing, setIsResizing] = useState(false);

  useEffect(() => {
    storage.setBool("pcgNavigatorMinimized", isMinimized);
  }, [isMinimized]);

  useEffect(() => {
    storage.setNumber("pcgNavigatorWidth", navigatorWidth);
  }, [navigatorWidth]);

  // Notify parent of state changes
  useEffect(() => {
    if (onNavigatorStateChange) {
      onNavigatorStateChange(isMinimized, navigatorWidth);
    }
  }, [isMinimized, navigatorWidth, onNavigatorStateChange]);

  // Build navigation items list with interleaving
  const buildNavigationItems = (): NavigationItem[] => {
    const items: NavigationItem[] = [];
    const phases: EvalStmtPhase[] = [
      "pre_operands",
      "post_operands",
      "pre_main",
      "post_main",
    ];

    // Map phase names to their indices in iterations.at_phase
    const phaseNameToIndex = new Map<string, number>();
    iterations.at_phase.forEach((at_phase, index) => {
      phaseNameToIndex.set(at_phase.phase, index);
    });

    // Add phases that appear before pre_operands
    let currentPhaseIdx = 0;
    while (currentPhaseIdx < iterations.at_phase.length) {
      const at_phase = iterations.at_phase[currentPhaseIdx];
      if (at_phase.phase === "pre_operands") break;
      items.push({
        type: "phase",
        index: currentPhaseIdx,
        name: at_phase.phase,
        filename: iterations.at_phase[currentPhaseIdx].filename,
      });
      currentPhaseIdx++;
    }

    // Interleave actions and phases for each eval phase
    phases.forEach((phase) => {
      // Add actions for this phase
      pcgData.actions[phase].forEach((action, index) => {
        if (
          action.data.kind.type !== "MakePlaceOld" &&
          action.data.kind.type !== "LabelLifetimeProjection"
        ) {
          items.push({ type: "action", phase, index, action });
        }
      });

      // Add the phase selector for this phase
      const phaseIdx = phaseNameToIndex.get(phase);
      if (phaseIdx !== undefined) {
        items.push({
          type: "phase",
          index: phaseIdx,
          name: phase,
          filename: iterations.at_phase[phaseIdx].filename,
        });
      }
    });

    return items;
  };

  const navigationItems = buildNavigationItems();

  // Handle selectFirstItem flag
  useEffect(() => {
    if (selectFirstItem && navigationItems.length > 0) {
      const firstItem = navigationItems[0];
      if (firstItem.type === "phase") {
        onSelectPoint({ type: "phase", index: firstItem.index });
      } else {
        onSelectPoint({
          type: "action",
          action: { phase: firstItem.phase, index: firstItem.index },
        });
      }
      onClearSelectFirstItem();
    }
  }, [selectFirstItem, navigationItems, onSelectPoint, onClearSelectFirstItem]);

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
  }, [isResizing]);

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
                item.phase === selectedPoint.action.phase &&
                item.index === selectedPoint.action.index
            );
          } else {
            currentIndex = navigationItems.findIndex(
              (item) =>
                item.type === "phase" && item.index === selectedPoint.index
            );
          }
        }

        // Calculate new index
        let newIndex: number;
        if (currentIndex === -1) {
          newIndex = event.key === "q" ? navigationItems.length - 1 : 0;
        } else {
          if (event.key === "q") {
            newIndex =
              currentIndex > 0 ? currentIndex - 1 : navigationItems.length - 1;
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
        if (item.type === "phase") {
          onSelectPoint({ type: "phase", index: item.index });
        } else {
          onSelectPoint({
            type: "action",
            action: { phase: item.phase, index: item.index },
          });
        }
      }
    };

    window.addEventListener("keydown", handleKeyDown);
    return () => window.removeEventListener("keydown", handleKeyDown);
  }, [navigationItems, selectedPoint, onSelectPoint, onAdvanceToNextStatement]);

  // Render navigation items in order (interleaved)
  const renderItems = () => {
    return navigationItems.map((item, idx) => {
      if (item.type === "phase") {
        const isSelected =
          selectedPoint?.type === "phase" && selectedPoint.index === item.index;
        return (
          <div
            key={`phase-${item.index}-${idx}`}
            style={{
              border: "1px solid #000",
              padding: "8px",
              marginBottom: "8px",
              backgroundColor: isSelected ? "lightgreen" : "transparent",
              cursor: "pointer",
              fontWeight: "bold",
            }}
            onClick={() => {
              onSelectPoint({ type: "phase", index: item.index });
            }}
          >
            {item.name}
          </div>
        );
      } else {
        // action
        const isSelected =
          selectedPoint?.type === "action" &&
          selectedPoint.action.phase === item.phase &&
          selectedPoint.action.index === item.index;
        return (
          <div
            key={`action-${item.phase}-${item.index}-${idx}`}
            style={{
              cursor: "pointer",
              padding: "6px 12px",
              marginBottom: "4px",
              borderRadius: "4px",
              backgroundColor: isSelected ? "#007acc" : "#f5f5f5",
              color: isSelected ? "white" : "inherit",
              border: isSelected ? "1px solid #007acc" : "1px solid #ddd",
            }}
            onClick={() => {
              onSelectPoint({
                type: "action",
                action: { phase: item.phase, index: item.index },
              });
            }}
            title={item.action.data.debug_context || undefined}
          >
            <code>{actionLine(item.action.data.kind)}</code>
          </div>
        );
      }
    });
  };

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
            {renderItems()}
          </div>
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
