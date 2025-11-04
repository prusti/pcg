import React, { useState, useEffect } from "react";
import {
  EvalStmtPhase,
  PcgAction,
  PcgStmtVisualizationData,
  SelectedAction,
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
  selectedPhase,
  selectedAction,
  onSelectPhase,
  onSelectAction,
  onNavigatorStateChange,
}: {
  iterations: StmtGraphs<string>;
  pcgData: PcgStmtVisualizationData;
  selectedPhase: number | null;
  selectedAction: SelectedAction | null;
  onSelectPhase: (index: number) => void;
  onSelectAction: (action: SelectedAction | null) => void;
  onNavigatorStateChange?: (
    isDocked: boolean,
    isMinimized: boolean,
    width: number
  ) => void;
}) {
  const [isDocked, setIsDocked] = useState(() => {
    return storage.getBool("pcgNavigatorDocked", true);
  });
  const [isMinimized, setIsMinimized] = useState(() => {
    return storage.getBool("pcgNavigatorMinimized", false);
  });
  const [isDragging, setIsDragging] = useState(false);
  const [position, setPosition] = useState({ x: 0, y: 0 });
  const [dragStart, setDragStart] = useState({ x: 0, y: 0 });
  const [initialized, setInitialized] = useState(false);
  const [navigatorWidth, setNavigatorWidth] = useState(() => {
    const stored = storage.getItem("pcgNavigatorWidth");
    return stored ? parseInt(stored, 10) : NAVIGATOR_DEFAULT_WIDTH;
  });
  const [isResizing, setIsResizing] = useState(false);

  useEffect(() => {
    storage.setItem("pcgNavigatorDocked", isDocked.toString());
  }, [isDocked]);

  useEffect(() => {
    storage.setItem("pcgNavigatorMinimized", isMinimized.toString());
  }, [isMinimized]);

  useEffect(() => {
    storage.setItem("pcgNavigatorWidth", navigatorWidth.toString());
  }, [navigatorWidth]);

  // Notify parent of state changes
  useEffect(() => {
    if (onNavigatorStateChange) {
      onNavigatorStateChange(isDocked, isMinimized, navigatorWidth);
    }
  }, [isDocked, isMinimized, navigatorWidth, onNavigatorStateChange]);

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
    iterations.at_phase.forEach(([name, _filename], index) => {
      phaseNameToIndex.set(name, index);
    });

    // Add phases that appear before pre_operands
    let currentPhaseIdx = 0;
    while (currentPhaseIdx < iterations.at_phase.length) {
      const [name] = iterations.at_phase[currentPhaseIdx];
      if (name === "pre_operands") break;
      items.push({
        type: "phase",
        index: currentPhaseIdx,
        name,
        filename: iterations.at_phase[currentPhaseIdx][1],
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
          filename: iterations.at_phase[phaseIdx][1],
        });
      }
    });

    return items;
  };

  const navigationItems = buildNavigationItems();

  // Initialize position
  useEffect(() => {
    if (!initialized) {
      // Initial position setup only on first render
      // eslint-disable-next-line react-hooks/set-state-in-effect
      setPosition({
        x: window.innerWidth - 320,
        y: window.innerHeight - 200,
      });
      setInitialized(true);
    }
  }, [initialized]);

  // Drag handlers (only for floating mode)
  const handleMouseDown = (event: React.MouseEvent) => {
    if (!isDocked) {
      setIsDragging(true);
      setDragStart({
        x: event.clientX - position.x,
        y: event.clientY - position.y,
      });
    }
  };

  useEffect(() => {
    const handleMouseMove = (event: MouseEvent) => {
      if (isDragging && !isDocked) {
        setPosition({
          x: event.clientX - dragStart.x,
          y: event.clientY - dragStart.y,
        });
      }
    };

    const handleMouseUp = () => {
      setIsDragging(false);
    };

    if (isDragging) {
      window.addEventListener("mousemove", handleMouseMove);
      window.addEventListener("mouseup", handleMouseUp);
      return () => {
        window.removeEventListener("mousemove", handleMouseMove);
        window.removeEventListener("mouseup", handleMouseUp);
      };
    }
  }, [isDragging, dragStart, isDocked]);

  // Resize handlers for docked mode
  const handleResizeStart = (event: React.MouseEvent) => {
    event.preventDefault();
    setIsResizing(true);
  };

  useEffect(() => {
    const handleResizeMove = (event: MouseEvent) => {
      if (isResizing && isDocked) {
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
  }, [isResizing, isDocked]);

  // Keyboard navigation
  useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      if (event.key === "q" || event.key === "a") {
        event.preventDefault();

        if (navigationItems.length === 0) return;

        // Find current index
        let currentIndex = -1;
        if (selectedAction) {
          currentIndex = navigationItems.findIndex(
            (item) =>
              item.type === "action" &&
              item.phase === selectedAction.phase &&
              item.index === selectedAction.index
          );
        } else if (selectedPhase !== null) {
          currentIndex = navigationItems.findIndex(
            (item) => item.type === "phase" && item.index === selectedPhase
          );
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
            newIndex =
              currentIndex < navigationItems.length - 1 ? currentIndex + 1 : 0;
          }
        }

        // Select the item
        const item = navigationItems[newIndex];
        if (item.type === "phase") {
          onSelectPhase(item.index);
          onSelectAction(null);
        } else {
          onSelectAction({ phase: item.phase, index: item.index });
        }
      }
    };

    window.addEventListener("keydown", handleKeyDown);
    return () => window.removeEventListener("keydown", handleKeyDown);
  }, [
    navigationItems,
    selectedPhase,
    selectedAction,
    onSelectPhase,
    onSelectAction,
  ]);

  // Render navigation items in order (interleaved)
  const renderItems = () => {
    return navigationItems.map((item, idx) => {
      if (item.type === "phase") {
        const isSelected =
          selectedAction === null && selectedPhase === item.index;
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
              onSelectPhase(item.index);
              onSelectAction(null);
            }}
          >
            {item.name}
          </div>
        );
      } else {
        // action
        const isSelected =
          selectedAction?.phase === item.phase &&
          selectedAction?.index === item.index;
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
              onSelectAction({ phase: item.phase, index: item.index });
            }}
            title={item.action.data.debug_context || undefined}
          >
            <code>{actionLine(item.action.data.kind)}</code>
          </div>
        );
      }
    });
  };

  if (isDocked) {
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
            <button
              onClick={() => setIsDocked(false)}
              style={{
                cursor: "pointer",
                backgroundColor: "#4CAF50",
                color: "white",
                border: "none",
                borderRadius: "4px",
                padding: "5px 8px",
                fontSize: "12px",
              }}
              title="Detach"
            >
              ⤢
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

  return (
    <div
      style={{
        position: "fixed",
        top: `${position.y}px`,
        left: `${position.x}px`,
        backgroundColor: "white",
        boxShadow: "0 0 10px rgba(0,0,0,0.1)",
        padding: "15px",
        maxWidth: NAVIGATOR_MAX_WIDTH,
        overflowY: "auto",
        maxHeight: "80vh",
        cursor: isDragging ? "grabbing" : "grab",
        userSelect: "none",
        zIndex: 1000,
      }}
      onMouseDown={handleMouseDown}
    >
      <div
        style={{
          display: "flex",
          justifyContent: "space-between",
          alignItems: "center",
          marginBottom: "10px",
          paddingBottom: "10px",
          borderBottom: "1px solid #ddd",
        }}
      >
        <h3 style={{ margin: 0, fontSize: "14px", fontWeight: "bold" }}>
          Navigator
        </h3>
        <button
          onClick={() => setIsDocked(true)}
          style={{
            cursor: "pointer",
            backgroundColor: "#4CAF50",
            color: "white",
            border: "none",
            borderRadius: "4px",
            padding: "5px 8px",
            fontSize: "12px",
          }}
          title="Dock to right"
        >
          ⤢
        </button>
      </div>
      <div style={{ marginBottom: "10px" }}>{renderItems()}</div>
      <div
        style={{
          marginTop: "10px",
          fontSize: "12px",
          color: "#666",
          borderTop: "1px solid #ddd",
          paddingTop: "10px",
        }}
      >
        Press &apos;q&apos;/&apos;a&apos; to navigate between phases and actions
      </div>
    </div>
  );
}
