import { BorrowPcgActionKindDebugRepr } from "./generated_types/BorrowPcgActionKindDebugRepr";
import { CapabilityKind } from "./generated_types/CapabilityKind";
import { RepackOp } from "./generated_types/RepackOp";

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
    case "None":
      return "⦰";
  }
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
      if (typeof action.data === "string") {
        return action.data;
      }
      return `${action.data.place}: ${capabilityLetter(action.data.from)} -> ${action.data.to ? capabilityLetter(action.data.to) : "None"}`;
    case "RegainLoanedCapability":
      return `Restore capability ${capabilityLetter(action.data.capability)} to ${action.data.place}`;
    case "AddEdge":
    case "RemoveEdge":
    case "Restore":
      return typeof action.data === "string" ? action.data : JSON.stringify(action.data);
    case "LabelPlace":
      return action.data
    case "LabelLifetimeProjection":
      return action.data
    default:
      return JSON.stringify(action);
  }
}

