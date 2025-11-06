export type NavigatorPoint = {
  type: "action";
  phase: EvalStmtPhase | "successor";
  index: number;
} | {
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
  isOnSelectedPath: boolean;
  hoveredStmts?: Set<string>;
  showActionsInGraph?: boolean;
  pcgStmtData?: Map<number, PcgProgramPointData>;
};

export type PcgAction = PcgActionDebugRepr;

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

import type {
  EvalStmtPhase,
  FunctionMetadata,
  MirStmt,
  PcgActionDebugRepr,
  PcgStmtVisualizationData,
  PcgSuccessorVisualizationData,
  SourcePos,
} from "./generated/types";
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

export type StringOf<T> = string & { __brand: T };
