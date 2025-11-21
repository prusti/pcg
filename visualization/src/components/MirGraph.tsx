import React, { useMemo } from "react";
import ReactFlow, {
  Background,
  Controls,
  MarkerType,
  PanOnScrollMode,
} from "reactflow";
import "reactflow/dist/style.css";
import { CurrentPoint } from "../types";
import { MirNode, MirEdge } from "../generated/types";
import {
  toReactFlowNodes,
  toReactFlowEdges,
  filterNodesAndEdges,
  layoutNodesWithDagre,
} from "../mir_graph";
import ReactFlowBasicBlockNode from "./ReactFlowBasicBlockNode";
import ReactFlowEdge from "./ReactFlowEdge";
import { ApiFunctionData } from "../api";

const nodeTypes = {
  basicBlock: ReactFlowBasicBlockNode,
};

const edgeTypes = {
  custom: ReactFlowEdge,
};

interface MirGraphProps {
  edges: MirEdge[];
  mirNodes: MirNode[];
  currentPoint: CurrentPoint;
  setCurrentPoint: (point: CurrentPoint) => void;
  hoveredStmts?: Set<string>;
  showActionsInGraph?: boolean;
  apiData: ApiFunctionData | null;
  highlightedEdges?: Set<string>;
}

const MirGraph: React.FC<MirGraphProps> = ({
  edges,
  mirNodes,
  currentPoint,
  setCurrentPoint,
  hoveredStmts,
  showActionsInGraph = false,
  apiData = null,
  highlightedEdges = new Set(),
}) => {
  const { filteredNodes, filteredEdges } = useMemo(
    () =>
      filterNodesAndEdges(mirNodes, edges, {
        showUnwindEdges: false,
        path: null,
      }),
    [mirNodes, edges]
  );

  const layoutNodes = useMemo(() => {
    return layoutNodesWithDagre(
      filteredNodes,
      filteredEdges,
      showActionsInGraph,
      apiData
    ).nodes;
  }, [filteredNodes, filteredEdges, showActionsInGraph, apiData]);
  const reactFlowNodes = useMemo(
    () =>
      toReactFlowNodes(
        layoutNodes,
        currentPoint,
        setCurrentPoint,
        hoveredStmts,
        showActionsInGraph,
        apiData
      ),
    [
      layoutNodes,
      currentPoint,
      setCurrentPoint,
      hoveredStmts,
      showActionsInGraph,
      apiData,
    ]
  );

  const reactFlowEdges = useMemo(
    () =>
      toReactFlowEdges(
        edges,
        mirNodes,
        currentPoint,
        setCurrentPoint,
        showActionsInGraph,
        apiData,
        highlightedEdges
      ),
    [
      edges,
      mirNodes,
      currentPoint,
      setCurrentPoint,
      showActionsInGraph,
      highlightedEdges,
      apiData,
    ]
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
    <div className="graph-container" style={{ width: "100%", height: "100%" }}>
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
