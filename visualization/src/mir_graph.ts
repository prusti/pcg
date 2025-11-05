import { MirEdge, MirNode } from "./generated/types";
import { computeTableHeight } from "./components/BasicBlockTable";
import { BasicBlockData, DagreEdge, DagreInputNode, DagreNode } from "./types";
import * as dagre from "@dagrejs/dagre";

export type FilterOptions = {
  showUnwindEdges: boolean;
  path: number[] | null;
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

export function layoutSizedNodes(
  nodes: DagreInputNode<BasicBlockData>[],
  edges: DagreEdge[]
) {
  const g = new dagre.graphlib.Graph().setDefaultEdgeLabel(() => ({}));
  g.setGraph({ ranksep: 100, rankdir: "TB", marginy: 100 });

  edges.forEach((edge) => g.setEdge(edge.source, edge.target));
  nodes.forEach((node) => g.setNode(node.id, node));

  dagre.layout(g);

  let height = g.graph().height;
  if (!isFinite(height)) {
    height = null;
  }

  return {
    nodes: nodes as DagreNode<BasicBlockData>[],
    edges,
    height,
  };
}

export function layoutUnsizedNodes(
  nodes: MirNode[],
  edges: { source: string; target: string }[]
): {
  nodes: DagreNode<BasicBlockData>[];
  height: number;
} {
  const heightCalculatedNodes = nodes.map((node) => {
    return {
      id: node.id,
      data: {
        block: node.block,
        stmts: node.stmts,
        terminator: node.terminator,
      },
      height: computeTableHeight(node),
      width: 300,
    };
  });
  const g = layoutSizedNodes(heightCalculatedNodes, edges);
  return {
    nodes: g.nodes,
    height: g.height,
  };
}

export function toDagreEdges(edges: MirEdge[]): DagreEdge[] {
  return edges.map((edge, idx) => ({
    id: `${edge.source}-${edge.target}-${idx}`,
    source: edge.source,
    target: edge.target,
    data: { label: edge.label },
    type: "straight",
  }));
}
