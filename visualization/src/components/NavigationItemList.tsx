import React from "react";
import {
  EvalStmtPhase,
  PcgAction,
  NavigatorPoint,
} from "../types";
import { AppliedAction } from "../generated_types/AppliedAction";
import { actionLine } from "../actionFormatting";

export type NavigationItem =
  | { type: "iteration"; name: string; filename: string }
  | {
      type: "action";
      phase: "successor";
      index: number;
      action: PcgAction;
    }
  | {
      type: "action";
      phase: EvalStmtPhase;
      index: number;
      action: AppliedAction;
    };

export default function NavigationItemList({
  navigationItems,
  selectedPoint,
  onSelectPoint,
}: {
  navigationItems: NavigationItem[];
  selectedPoint: NavigatorPoint | null;
  onSelectPoint: (point: NavigatorPoint) => void;
}) {
  return (
    <>
      {navigationItems.map((item, idx) => {
        try {
          console.log(item);
          if (item.type === "iteration") {
            const isSelected =
              selectedPoint?.type === "iteration" &&
              selectedPoint.name === item.name;
            return (
              <div
                key={`iteration-${item.name}-${idx}`}
                style={{
                  border: "1px solid #000",
                  padding: "8px",
                  marginBottom: "8px",
                  backgroundColor: isSelected ? "lightgreen" : "transparent",
                  cursor: "pointer",
                  fontWeight: "bold",
                }}
                onClick={() => {
                  onSelectPoint({ type: "iteration", name: item.name });
                }}
              >
                {item.name}
              </div>
            );
          } else {
            const isSelected =
              selectedPoint?.type === "action" &&
              selectedPoint.phase === item.phase &&
              selectedPoint.index === item.index;
            const action =
              item.phase === "successor" ? item.action : item.action.action;
            let hoverText = action.data.debug_info || "";
            const itemContent = actionLine(action.data.kind);
            if (item.phase !== "successor") {
              if (!hoverText) {
                hoverText = item.action.result.change_summary;
              } else {
                hoverText += " " + item.action.result.change_summary;
              }
            }
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
                    phase: item.phase,
                    index: item.index,
                  });
                }}
                title={hoverText || undefined}
              >
                <code>{itemContent}</code>
              </div>
            );
          }
        } catch (error) {
          console.error("Error rendering item %O:", item, error);
          const errorMessage =
            error instanceof Error ? error.message : String(error);
          return <div key={`error-${idx}`}>{errorMessage}</div>;
        }
      })}
    </>
  );
}
