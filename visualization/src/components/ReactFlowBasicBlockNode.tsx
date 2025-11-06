import React from "react";
import { Handle, Position, NodeProps } from "reactflow";
import { ReactFlowNodeData } from "../types";
import BasicBlockTable from "./BasicBlockTable";

export default function ReactFlowBasicBlockNode({ data }: NodeProps<ReactFlowNodeData>) {
  return (
    <div className="nopan" style={{ pointerEvents: "all" }}>
      <BasicBlockTable
        data={{
          block: data.block,
          stmts: data.stmts,
          terminator: data.terminator,
        }}
        currentPoint={data.currentPoint}
        setCurrentPoint={data.setCurrentPoint}
        hoveredStmts={data.hoveredStmts}
        showActionsInGraph={data.showActionsInGraph}
        pcgStmtData={data.pcgStmtData}
      />
      <Handle type="target" position={Position.Top} style={{ visibility: "hidden" }} />
      <Handle type="source" position={Position.Bottom} style={{ visibility: "hidden" }} />
    </div>
  );
}

