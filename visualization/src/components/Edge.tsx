import React from "react";
import type { BasicBlockData, DagreEdge, DagreNode, PcgProgramPointData } from "../types";
import { PcgActionDebugRepr } from "../generated/types";
import { actionLine } from "../actionFormatting";

export default function Edge({
  edge,
  nodes,
  selected,
  onSelect,
  showActions,
  terminatorActions,
}: {
  selected: boolean;
  edge: DagreEdge;
  nodes: DagreNode<BasicBlockData>[];
  onSelect: () => void;
  showActions?: boolean;
  terminatorActions?: PcgProgramPointData;
}) {
  const sourceNode = nodes.find((n) => n.id === edge.source);
  const targetNode = nodes.find((n) => n.id === edge.target);

  if (!sourceNode || !targetNode) return null;

  const startX = sourceNode.x + sourceNode.width / 2;
  const startY = sourceNode.y + sourceNode.height / 2;
  const endX = targetNode.x + targetNode.width / 2;
  const endY = targetNode.y - targetNode.height / 2;

  const midX = (startX + endX) / 2;
  const midY = (startY + endY) / 2;

  const actions: string[] = [];
  if (showActions && terminatorActions && Array.isArray(terminatorActions.actions)) {
    terminatorActions.actions.forEach((action: PcgActionDebugRepr) => {
      if (action.data.kind.type !== "MakePlaceOld" && action.data.kind.type !== "LabelLifetimeProjection") {
        actions.push(actionLine(action.data.kind));
      }
    });
  }

  const hasLabel = edge.data.label && edge.data.label.length > 0;
  const hasActions = actions.length > 0;
  const labelY = hasActions ? midY - 10 : midY;
  const actionsY = hasLabel ? midY + 10 : midY;

  return (
    <g
      onClick={() => onSelect()}
      style={{
        pointerEvents: "auto",
        cursor: "pointer",
      }}
    >
      <line
        x1={startX}
        y1={startY}
        x2={endX}
        y2={endY}
        stroke={selected ? "green" : "black"}
        strokeWidth={2}
      />
      {hasLabel && (
        <text
          x={midX}
          y={labelY}
          textAnchor="middle"
          alignmentBaseline="middle"
          fill="black"
          fontSize="12"
        >
          {edge.data.label}
        </text>
      )}
      {hasActions && (
        <text
          x={midX}
          y={actionsY}
          textAnchor="middle"
          alignmentBaseline="middle"
          fill="#0066cc"
          fontSize="11"
          fontStyle="italic"
          fontFamily="monospace"
        >
          {actions.join(", ")}
        </text>
      )}
    </g>
  );
}
