import { MirNode } from "./generated/types";
import { CurrentPoint, MirStmt } from "./types";

export function addKeyDownListener(
  nodes: MirNode[],
  filteredNodes: MirNode[],
  setCurrentPoint: React.Dispatch<React.SetStateAction<CurrentPoint>>
) {
  const handleKeyDown = (event: KeyboardEvent) => {
    keydown(event, nodes, filteredNodes, setCurrentPoint);
  };
  window.addEventListener("keydown", handleKeyDown);
  return () => {
    window.removeEventListener("keydown", handleKeyDown);
  };
}

function keydown(
  event: KeyboardEvent,
  nodes: MirNode[],
  filteredNodes: MirNode[],
  setCurrentPoint: React.Dispatch<React.SetStateAction<CurrentPoint>>
) {
  if (
    event.key === "ArrowUp" ||
    event.key === "ArrowDown" ||
    event.key === "j" ||
    event.key === "k"
  ) {
    event.preventDefault(); // Prevent scrolling
    const direction =
      event.key === "ArrowUp" || event.key === "k" ? "up" : "down";

    setCurrentPoint((prevPoint: CurrentPoint) => {
      if (prevPoint.type === "terminator") {
        return; // TODO
      }
      const currentNode = nodes.find((node) => node.block === prevPoint.block);
      if (!currentNode) return prevPoint;

      const isSelectable = (node: { stmts: MirStmt[] }, idx: number) => {
        return idx >= 0 && idx <= node.stmts.length;
      };

      const getNextStmtIdx = (node: { stmts: MirStmt[] }, from: number) => {
        const offset = direction === "up" ? -1 : 1;
        const idx = from + offset;
        if (isSelectable(node, idx)) {
          return idx;
        } else {
          return null;
        }
      };

      const nextStmtIdx = getNextStmtIdx(currentNode, prevPoint.stmt);
      if (nextStmtIdx !== null) {
        const result = { ...prevPoint, stmt: nextStmtIdx };
        result.navigatorPoint = { type: "iteration", name: "post_main" };
        return result;
      } else {
        const currBlockIdx = filteredNodes.findIndex(
          (node) => node.block === prevPoint.block
        );
        if (direction === "down") {
          const nextBlockIdx = (currBlockIdx + 1) % filteredNodes.length;
          const data = filteredNodes[nextBlockIdx];
          return {
            type: "stmt",
            block: filteredNodes[nextBlockIdx].block,
            stmt: getNextStmtIdx(data, -1),
            navigatorPoint: { type: "iteration", name: "post_main" },
          };
        } else {
          const nextBlockIdx =
            (currBlockIdx - 1 + filteredNodes.length) % filteredNodes.length;
          const data = filteredNodes[nextBlockIdx];
          return {
            type: "stmt",
            block: data.block,
            stmt: data.stmts.length,
            navigatorPoint: { type: "iteration", name: "post_main" },
          };
        }
      }
    });
  } else if (event.key >= "0" && event.key <= "9") {
    const newBlock = parseInt(event.key);
    setCurrentPoint({
      type: "stmt",
      block: newBlock,
      stmt: 0,
      navigatorPoint: { type: "iteration", name: "post_main" },
    });
  }
}
