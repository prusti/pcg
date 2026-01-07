import React from "react";
import { EdgeProps, getBezierPath, EdgeLabelRenderer } from "reactflow";
import { PcgProgramPointData } from "../types";
import { actionLine } from "../actionFormatting";

export type ReactFlowEdgeData = {
  label?: string;
  selected: boolean;
  highlighted?: boolean;
  onSelect: () => void;
  showActions?: boolean;
  terminatorActions?: PcgProgramPointData;
};

export default function ReactFlowEdge({
  id,
  sourceX,
  sourceY,
  targetX,
  targetY,
  sourcePosition,
  targetPosition,
  data,
  markerEnd,
}: EdgeProps<ReactFlowEdgeData>) {
  const [edgePath, labelX, labelY] = getBezierPath({
    sourceX,
    sourceY,
    sourcePosition,
    targetX,
    targetY,
    targetPosition,
  });

  const actions: string[] = [];
  if (
    data?.showActions &&
    data?.terminatorActions &&
    Array.isArray(data.terminatorActions.actions)
  ) {
    data.terminatorActions.actions.forEach((action) => {
      actions.push(actionLine(action.data.kind));
    });
  }

  const hasLabel = data?.label && data.label.length > 0;
  const hasActions = actions.length > 0;

  const strokeColor = data?.selected
    ? "green"
    : data?.highlighted
      ? "#ff6b00"
      : "black";
  const strokeWidth = data?.highlighted ? 4 : 2;

  return (
    <>
      <path
        id={id}
        className="react-flow__edge-path"
        d={edgePath}
        markerEnd={markerEnd}
        style={{
          stroke: strokeColor,
          strokeWidth: strokeWidth,
          cursor: "pointer",
          transition: "stroke 0.2s, stroke-width 0.2s",
        }}
        onClick={data?.onSelect}
      />
      <EdgeLabelRenderer>
        <div
          style={{
            position: "absolute",
            transform: `translate(-50%, -50%) translate(${labelX}px,${labelY}px)`,
            pointerEvents: "all",
            cursor: "pointer",
          }}
          onClick={data?.onSelect}
        >
          {hasLabel && (
            <div
              style={{
                fontSize: "12px",
                background: "white",
                padding: "2px 4px",
                borderRadius: "3px",
                textAlign: "center",
              }}
            >
              {data.label}
            </div>
          )}
          {hasActions && (
            <div
              style={{
                fontSize: "11px",
                fontStyle: "italic",
                fontFamily: "monospace",
                color: "#0066cc",
                background: "white",
                padding: "2px 4px",
                borderRadius: "3px",
                marginTop: hasLabel ? "4px" : "0",
                textAlign: "center",
              }}
            >
              {actions.map((action, idx) => (
                <React.Fragment key={idx}>
                  {idx > 0 && <br />}
                  {action}
                </React.Fragment>
              ))}
            </div>
          )}
        </div>
      </EdgeLabelRenderer>
    </>
  );
}
