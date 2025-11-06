import React, { useMemo } from "react";
import ReactFlow, { Background, Controls, MarkerType, PanOnScrollMode } from "reactflow";
import "reactflow/dist/style.css";
import { CurrentPoint, PcgProgramPointData } from "../types";
import { MirNode, MirEdge, PcgFunctionData } from "../generated/types";
import { toReactFlowNodes, toReactFlowEdges, PositionedLayoutNode } from "../mir_graph";
import ReactFlowBasicBlockNode from "./ReactFlowBasicBlockNode";
import ReactFlowEdge from "./ReactFlowEdge";

const nodeTypes = {
  basicBlock: ReactFlowBasicBlockNode,
};

const edgeTypes = {
  custom: ReactFlowEdge,
};

interface MirGraphProps {
  layoutNodes: PositionedLayoutNode[];
  edges: MirEdge[];
  mirNodes: MirNode[];
  currentPoint: CurrentPoint;
  setCurrentPoint: (point: CurrentPoint) => void;
  hoveredStmts?: Set<string>;
  showActionsInGraph?: boolean;
  allPcgStmtData?: Map<number, Map<number, PcgProgramPointData>>;
  pcgFunctionData?: PcgFunctionData | null;
}

const MirGraph: React.FC<MirGraphProps> = ({
  layoutNodes,
  edges,
  mirNodes,
  currentPoint,
  setCurrentPoint,
  hoveredStmts,
  showActionsInGraph = false,
  allPcgStmtData = new Map(),
  pcgFunctionData = null,
}) => {
  const reactFlowNodes = useMemo(
    () =>
      toReactFlowNodes(
        layoutNodes,
        currentPoint,
        setCurrentPoint,
        hoveredStmts,
        showActionsInGraph,
        allPcgStmtData
      ),
    [layoutNodes, currentPoint, setCurrentPoint, hoveredStmts, showActionsInGraph, allPcgStmtData]
  );

  const reactFlowEdges = useMemo(
    () =>
      toReactFlowEdges(
        edges,
        mirNodes,
        currentPoint,
        setCurrentPoint,
        showActionsInGraph,
        pcgFunctionData
      ),
    [edges, mirNodes, currentPoint, setCurrentPoint, showActionsInGraph, pcgFunctionData]
  );

  const defaultEdgeOptions = useMemo(
    () => ({
      markerEnd: {
        type: MarkerType.ArrowClosed,
        width: 20,
        height: 20,
      },
    }),
    []
  );

  return (
    <div
      className="graph-container"
      style={{ width: "100%", height: "100%" }}
    >
      <ReactFlow
        nodes={reactFlowNodes}
        edges={reactFlowEdges}
        nodeTypes={nodeTypes}
        edgeTypes={edgeTypes}
        defaultEdgeOptions={defaultEdgeOptions}
        nodesDraggable={false}
        nodesConnectable={false}
        elementsSelectable={false}
        zoomOnScroll={true}
        panOnScroll={true}
        panOnScrollMode={PanOnScrollMode.Vertical}
        preventScrolling={true}
        fitView
        fitViewOptions={{ padding: 0.2 }}
      >
        <Background />
        <Controls />
      </ReactFlow>
    </div>
  );
};

export default MirGraph;
