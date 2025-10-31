import React, { useState, useEffect } from "react";
import {
  EvalStmtPhase,
  PcgAction,
  PcgStmtVisualizationData,
  SelectedAction,
} from "../types";
import { BorrowPcgActionKindDebugRepr, RepackOp, StmtGraphs } from "../generated/types";

type NavigationItem =
  | { type: "phase"; index: number; name: string; filename: string }
  | {
      type: "action";
      phase: EvalStmtPhase;
      index: number;
      action: PcgAction;
    };

function actionLine(action: RepackOp<string, string, string> | BorrowPcgActionKindDebugRepr) {
  switch (action.type) {
    case "Expand":
      return `unpack ${action.data.from}`;
    case "Collapse":
      return `pack ${action.data.to}`;
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
}: {
  iterations: StmtGraphs<string>;
  pcgData: PcgStmtVisualizationData;
  selectedPhase: number | null;
  selectedAction: SelectedAction | null;
  onSelectPhase: (index: number) => void;
  onSelectAction: (action: SelectedAction | null) => void;
}) {
  const [isDragging, setIsDragging] = useState(false);
  const [position, setPosition] = useState({ x: 0, y: 0 });
  const [dragStart, setDragStart] = useState({ x: 0, y: 0 });
  const [initialized, setInitialized] = useState(false);

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
    iterations.at_phase.forEach(([name, filename], index) => {
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
        if (action.data.kind.type !== "MakePlaceOld") {
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
      setPosition({
        x: window.innerWidth - 320,
        y: window.innerHeight - 200,
      });
      setInitialized(true);
    }
  }, [initialized]);

  // Drag handlers
  const handleMouseDown = (event: React.MouseEvent) => {
    setIsDragging(true);
    setDragStart({
      x: event.clientX - position.x,
      y: event.clientY - position.y,
    });
  };

  useEffect(() => {
    const handleMouseMove = (event: MouseEvent) => {
      if (isDragging) {
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
  }, [isDragging, dragStart]);

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
  }, [navigationItems, selectedPhase, selectedAction, onSelectPhase, onSelectAction]);

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
              border: isSelected
                ? "1px solid #007acc"
                : "1px solid #ddd",
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

  return (
    <div
      style={{
        position: "fixed",
        top: `${position.y}px`,
        left: `${position.x}px`,
        backgroundColor: "white",
        boxShadow: "0 0 10px rgba(0,0,0,0.1)",
        padding: "15px",
        maxWidth: "350px",
        overflowY: "auto",
        maxHeight: "80vh",
        cursor: isDragging ? "grabbing" : "grab",
        userSelect: "none",
      }}
      onMouseDown={handleMouseDown}
    >
      <div style={{ marginBottom: "10px" }}>
        {renderItems()}
      </div>
      <div style={{ marginTop: "10px", fontSize: "12px", color: "#666", borderTop: "1px solid #ddd", paddingTop: "10px" }}>
        Press 'q'/'a' to navigate between phases and actions
      </div>
    </div>
  );
}

