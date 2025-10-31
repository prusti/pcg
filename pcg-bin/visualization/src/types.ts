import { MirStmt } from "./api";

export type EvalStmtPhase =
  | "pre_operands"
  | "post_operands"
  | "pre_main"
  | "post_main";

export type SelectedAction = {
  phase: EvalStmtPhase;
  index: number;
};

export type CurrentPoint =
  | {
      type: "stmt";
      block: number;
      stmt: number;
      selectedAction: SelectedAction | null;
    }
  | {
      type: "terminator";
      block1: number;
      block2: number;
    };

export type BasicBlockData = {
  block: number;
  stmts: MirStmt[];
  terminator: MirStmt;
};

export type DagreInputNode<T> = {
  id: string;
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

export type PcgAction = ActionKindWithDebugCtxt<string>

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
  ActionKindWithDebugCtxt,
  EvalStmtData,
  FunctionMetadata,
  PcgStmtVisualizationData,
  PcgSuccessorVisualizationData,
  SourcePos,
} from "./generated/types";
export type {
  FunctionMetadata,
  SourcePos,
  PcgStmtVisualizationData,
  PcgSuccessorVisualizationData,
};

export type FunctionsMetadata = {
  [slug: FunctionSlug]: FunctionMetadata;
};
