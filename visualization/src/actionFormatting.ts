import {
  BorrowPcgActionKindDebugRepr,
  CapabilityChanges,
  CapabilityKind,
  RepackOp,
} from "./generated_types";

export function capabilityLetter(capability: CapabilityKind): string {
  switch (capability) {
    case "Read":
      return "R";
    case "Write":
      return "W";
    case "Exclusive":
      return "E";
    case "ShallowExclusive":
      return "e";
  }
}

export function capabilityChangesLine(changes: CapabilityChanges): string {
  return changes
    .map(([place, cap]) => `${place}: ${cap ? capabilityLetter(cap) : "None"}`)
    .join(", ");
}

export function actionLine(
  action: RepackOp | BorrowPcgActionKindDebugRepr
): string {
  switch (action.type) {
    case "Expand":
      return `Unpack ${action.data.from}`;
    case "Collapse":
      return `Pack ${action.data.to}`;
    case "Weaken":
    case "AddEdge":
    case "RemoveEdge":
    case "Freeze":
    case "Unfreeze":
    case "ActivateTwoPhaseBorrow":
    case "Lend":
      return typeof action.data === "string" ? action.data : JSON.stringify(action.data);
    case "LabelPlace":
      return action.data
    case "LabelLifetimeProjection":
      return action.data
    default:
      return JSON.stringify(action);
  }
}

