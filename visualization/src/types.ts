export type NavigatorPoint =
  | {
      type: "action";
      phase: EvalStmtPhase | "successor";
      index: number;
    }
  | {
      type: "iteration";
      name: string;
    };

export type CurrentPoint =
  | {
      type: "stmt";
      block: number;
      stmt: number;
      navigatorPoint: NavigatorPoint;
    }
  | {
      type: "terminator";
      block1: number;
      block2: number;
      navigatorPoint?: NavigatorPoint;
    };

export type BasicBlockData = {
  block: number;
  stmts: MirStmt[];
  terminator: MirStmt;
};

export type DagreInputNode<T = unknown> = {
  id: string;
  data?: T;
};

export type DagreEdge = {
  id: string;
  source: string;
  target: string;
  data: {
    label: string;
  };
  type: string;
};

export type DagreNode<T> = {
  id: string;
  data: T;
  x: number;
  y: number;
  width: number;
  height: number;
};

export type ReactFlowNodeData = BasicBlockData & {
  currentPoint: CurrentPoint;
  setCurrentPoint: (point: CurrentPoint) => void;
  hoveredStmts?: Set<string>;
  showActionsInGraph?: boolean;
  pcgData?: PcgBlockVisualizationData;
};

import { GenericPcgAction } from "./generated_types/GenericPcgAction";
import { ActionKindWithDebugInfo } from "./generated_types/ActionKindWithDebugInfo";
import { BorrowPcgActionKindDebugRepr } from "./generated_types/BorrowPcgActionKindDebugRepr";
import { RepackOp } from "./generated_types/RepackOp";

export type PcgAction = GenericPcgAction<
  ActionKindWithDebugInfo<BorrowPcgActionKindDebugRepr, string | null>,
  ActionKindWithDebugInfo<RepackOp, string | null>
>;

export type PcgActions = PcgAction[];

export type PathData = {
  heap: Record<string, { value: string; ty: string; old: boolean }>;
  pcs: string;
};

export type PcgProgramPointData =
  | PcgStmtVisualizationData
  | PcgSuccessorVisualizationData;

declare const tag: unique symbol;

type Branded<T, B> = T & { [tag]: B };
export type FunctionSlug = Branded<string, "FunctionSlug">;
export type FunctionName = Branded<string, "FunctionName">;

import { EvalStmtPhase } from "./generated_types/EvalStmtPhase";
import { FunctionMetadata } from "./generated_types/FunctionMetadata";
import { SourcePos } from "./generated_types/SourcePos";
import { PcgStmtVisualizationData } from "./generated_types/PcgStmtVisualizationData";
import { PcgSuccessorVisualizationData } from "./generated_types/PcgSuccessorVisualizationData";
import { MirStmt } from "./generated_types/MirStmt"
import { PcgBlockVisualizationData } from "./generated_types/PcgBlockVisualizationData";

export type {
  EvalStmtPhase,
  FunctionMetadata,
  SourcePos,
  PcgStmtVisualizationData,
  PcgSuccessorVisualizationData,
  MirStmt,
};

export type FunctionsMetadata = {
  [slug: FunctionSlug]: FunctionMetadata;
};

export type GetFunctionsResult =
  | { type: "found"; data: FunctionsMetadata }
  | { type: "not_found" };
