import React from "react";
import type { BasicBlockData, DagreNode } from "../types";

export default function Edge({
  edge,
  nodes,
  selected,
  onSelect,
}: {
  selected: boolean;
  edge: any;
  nodes: DagreNode<BasicBlockData>[];
  onSelect: () => void;
}) {
  const sourceNode = nodes.find((n) => n.id === edge.source);
  const targetNode = nodes.find((n) => n.id === edge.target);

  if (!sourceNode || !targetNode) return null;

  const startX = sourceNode.x + sourceNode.width / 2;
  const startY = sourceNode.y + sourceNode.height / 2;
  const endX = targetNode.x + targetNode.width / 2;
  const endY = targetNode.y - targetNode.height / 2;

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
      {edge.data.label && (
        <text
          x={(startX + endX) / 2}
          y={(startY + endY) / 2}
          textAnchor="middle"
          alignmentBaseline="middle"
          fill="black"
          fontSize="12"
        >
          {edge.data.label}
        </text>
      )}
    </g>
  );
}
