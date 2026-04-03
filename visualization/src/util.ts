import { BasicBlock } from "./generated_types";

export function toBasicBlock(block: number): BasicBlock {
  return `bb${block}` as BasicBlock;
}

export function assert(condition: boolean, message: string): void {
  if (!condition) {
    throw new Error(message);
  }
}
