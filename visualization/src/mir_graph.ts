import { MirEdge, MirNode, PcgFunctionData } from "./generated/types";
import { computeTableHeight } from "./components/BasicBlockTable";
import { BasicBlockData, CurrentPoint, PcgProgramPointData } from "./types";
import * as dagre from "@dagrejs/dagre";
import { Node as ReactFlowNode, Edge as ReactFlowEdge } from "reactflow";

export type FilterOptions = {
  showUnwindEdges: boolean;
  path: number[] | null;
};

export type LayoutNode = {
  id: string;
  width: number;
  height: number;
  data: BasicBlockData;
};

export type PositionedLayoutNode = LayoutNode & {
  x: number;
  y: number;
};

function computeReachableBlocks(
  nodes: MirNode[],
  edges: MirEdge[]
): Set<number> {
  const reachable = new Set<number>();
  const queue: string[] = [];

  const bb0Node = nodes.find((n) => n.block === 0);
  if (!bb0Node) {
    return reachable;
  }

  queue.push(bb0Node.id);
  reachable.add(0);

  const nodeIdToBlock = new Map<string, number>();
  nodes.forEach((node) => {
    nodeIdToBlock.set(node.id, node.block);
  });

  while (queue.length > 0) {
    const currentId = queue.shift()!;
    const outgoingEdges = edges.filter((e) => e.source === currentId);

    for (const edge of outgoingEdges) {
      const targetBlock = nodeIdToBlock.get(edge.target);
      if (targetBlock !== undefined && !reachable.has(targetBlock)) {
        reachable.add(targetBlock);
        queue.push(edge.target);
      }
    }
  }

  return reachable;
}

export function filterNodesAndEdges(
  nodes: MirNode[],
  edges: MirEdge[],
  options: FilterOptions
): {
  filteredNodes: MirNode[];
  filteredEdges: MirEdge[];
} {
  let filteredNodes = nodes;
  let filteredEdges = edges;
  if (!options.showUnwindEdges) {
    filteredNodes = nodes.filter((node) => node.terminator.stmt !== "resume");
    filteredEdges = edges.filter((edge) => edge.label !== "unwind");
  }
  if (options.path) {
    filteredNodes = filteredNodes.filter((node) =>
      options.path.includes(node.block)
    );
    filteredEdges = filteredEdges.filter((edge) => {
      const sourceNode = nodes.find((n) => n.id === edge.source);
      const targetNode = nodes.find((n) => n.id === edge.target);
      return (
        sourceNode &&
        targetNode &&
        options.path.includes(sourceNode.block) &&
        options.path.includes(targetNode.block)
      );
    });
  }

  const reachableBlocks = computeReachableBlocks(filteredNodes, filteredEdges);
  filteredNodes = filteredNodes.filter((node) => reachableBlocks.has(node.block));
  filteredEdges = filteredEdges.filter((edge) => {
    const sourceNode = filteredNodes.find((n) => n.id === edge.source);
    const targetNode = filteredNodes.find((n) => n.id === edge.target);
    return sourceNode && targetNode;
  });

  return { filteredNodes, filteredEdges };
}

export function layoutNodesWithDagre(
  nodes: MirNode[],
  edges: MirEdge[],
  showActionsInGraph?: boolean,
  allPcgStmtData?: Map<number, Map<number, PcgProgramPointData>>
): { nodes: PositionedLayoutNode[]; height: number | null } {
  // Create Dagre graph
  const g = new dagre.graphlib.Graph().setDefaultEdgeLabel(() => ({}));
  g.setGraph({ ranksep: 100, rankdir: "TB", marginy: 100 });

  // Prepare nodes with calculated dimensions (accounting for action display)
  const layoutNodes: LayoutNode[] = nodes.map((node) => ({
    id: node.id,
    width: 300,
    height: computeTableHeight(
      node,
      showActionsInGraph,
      allPcgStmtData?.get(node.block)
    ),
    data: {
      block: node.block,
      stmts: node.stmts,
      terminator: node.terminator,
    },
  }));

  // Add nodes and edges to Dagre
  layoutNodes.forEach((node) => g.setNode(node.id, node));
  edges.forEach((edge) => g.setEdge(edge.source, edge.target));

  // Run layout
  dagre.layout(g);

  // Extract positioned nodes
  const positionedNodes = layoutNodes.map((node) => {
    const position = g.node(node.id);
    return {
      ...node,
      x: position.x,
      y: position.y,
    };
  });

  const graphHeight = g.graph().height;
  const height = isFinite(graphHeight) ? graphHeight : null;

  return { nodes: positionedNodes, height };
}

export function toReactFlowNodes(
  layoutNodes: PositionedLayoutNode[],
  currentPoint: CurrentPoint,
  setCurrentPoint: (point: CurrentPoint) => void,
  hoveredStmts?: Set<string>,
  showActionsInGraph?: boolean,
  allPcgStmtData?: Map<number, Map<number, PcgProgramPointData>>
): ReactFlowNode[] {
  return layoutNodes.map((node) => ({
    id: node.id,
    type: "basicBlock",
    position: {
      x: node.x - node.width / 2,
      y: node.y - node.height / 2,
    },
    data: {
      ...node.data,
      currentPoint,
      setCurrentPoint,
      hoveredStmts,
      showActionsInGraph,
      pcgStmtData: allPcgStmtData?.get(node.data.block),
    },
  }));
}

export function toReactFlowEdges(
  mirEdges: MirEdge[],
  mirNodes: MirNode[],
  currentPoint: CurrentPoint,
  setCurrentPoint: (point: CurrentPoint) => void,
  showActionsInGraph: boolean,
  pcgFunctionData: PcgFunctionData | null,
  highlightedEdges?: Set<string>
): ReactFlowEdge[] {
  const nodeIdToBlock = new Map(mirNodes.map((n) => [n.id, n.block]));

  return mirEdges.map((edge, idx) => {
    const sourceBlock = nodeIdToBlock.get(edge.source);
    const targetBlock = nodeIdToBlock.get(edge.target);
    const isSelected =
      currentPoint.type === "terminator" &&
      currentPoint.block1 === sourceBlock &&
      currentPoint.block2 === targetBlock;

    // Check if this edge should be highlighted based on PCG hover
    const edgeKey = `${sourceBlock}-${targetBlock}`;
    const isHighlighted = highlightedEdges?.has(edgeKey) || false;

    if (highlightedEdges && highlightedEdges.size > 0) {
      console.log(`MIR Edge ${edgeKey}: highlighted=${isHighlighted}, available keys:`, Array.from(highlightedEdges));
    }

    const terminatorActions =
      showActionsInGraph && sourceBlock !== undefined && targetBlock !== undefined && pcgFunctionData
        ? pcgFunctionData.blocks[sourceBlock]?.successors[targetBlock]
        : undefined;

    return {
      id: `${edge.source}-${edge.target}-${idx}`,
      source: edge.source,
      target: edge.target,
      type: "custom",
      data: {
        label: edge.label,
        selected: isSelected,
        highlighted: isHighlighted,
        onSelect: () => {
          if (sourceBlock !== undefined && targetBlock !== undefined) {
            setCurrentPoint({
              type: "terminator",
              block1: sourceBlock,
              block2: targetBlock,
            });
          }
        },
        showActions: showActionsInGraph,
        terminatorActions,
      },
    };
  });
}
