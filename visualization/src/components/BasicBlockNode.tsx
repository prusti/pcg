import React from "react";
import { BasicBlockData, CurrentPoint, PcgProgramPointData } from "../types";
import BasicBlockTable from "./BasicBlockTable";

export default function BasicBlockNode({
  height,
  data,
  currentPoint,
  position,
  setCurrentPoint,
  isOnSelectedPath,
  hoveredStmts,
  showActionsInGraph,
  pcgStmtData,
}: {
  height: number;
  data: BasicBlockData;
  currentPoint: CurrentPoint;
  position: { x: number; y: number };
  setCurrentPoint: (point: CurrentPoint) => void;
  isOnSelectedPath: boolean;
  hoveredStmts?: Set<string>;
  showActionsInGraph?: boolean;
  pcgStmtData?: Map<number, PcgProgramPointData>;
}) {
  return (
    <div
      style={{
        position: "absolute",
        left: position.x,
        top: position.y - height / 2,
      }}
    >
      <BasicBlockTable
        data={data}
        currentPoint={currentPoint}
        setCurrentPoint={setCurrentPoint}
        isOnSelectedPath={isOnSelectedPath}
        hoveredStmts={hoveredStmts}
        showActionsInGraph={showActionsInGraph}
        pcgStmtData={pcgStmtData}
      />
    </div>
  );
}
