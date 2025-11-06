import React, { useRef, useState, useMemo } from "react";
import { Highlight, themes } from "prism-react-renderer";
import {
  FunctionMetadata,
  FunctionSlug,
  FunctionsMetadata,
  SourcePos,
  PcgProgramPointData
} from "../types";
import type {
  MirNode,
  RepackOp,
  BorrowPcgActionKindDebugRepr,
  CapabilityKind
} from "../generated/types";

type RelativeSpan = {
  low: SourcePos;
  high: SourcePos;
};

interface SourceCodeViewerProps {
  metadata: FunctionMetadata;
  functions: FunctionsMetadata;
  selectedFunction: FunctionSlug;
  onFunctionChange: (selectedFunction: FunctionSlug) => void;
  highlightSpan?: RelativeSpan | null;
  minimized?: boolean;
  fontSize?: number;
  onHoverPositionChange?: (position: SourcePos | null) => void;
  onClickPosition?: (position: SourcePos) => void;
  selectionIndicator?: { line: number; index: number; total: number } | null;
  showSettings?: boolean;
  onToggleSettings?: () => void;
  onFontSizeChange?: (fontSize: number) => void;
  onToggleMinimized?: () => void;
  showActionsInCode?: boolean;
  nodes?: MirNode[];
  allPcgStmtData?: Map<number, Map<number, PcgProgramPointData>>;
  onActionClick?: (block: number, stmt: number) => void;
}

function capabilityLetter(capability: CapabilityKind): string {
  switch (capability) {
    case "Exclusive":
      return "E";
    case "ShallowExclusive":
      return "e";
  }
}

function actionLine(
  action: RepackOp<string, string, string> | BorrowPcgActionKindDebugRepr
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
      return `Weaken ${action.data.place} from ${action.data.from} to ${action.data.to}`;
    case "RegainLoanedCapability":
      return `Restore capability ${capabilityLetter(action.data.capability)} to ${action.data.place}`;
    case "AddEdge":
    case "RemoveEdge":
    case "Restore":
      return typeof action.data === "string" ? action.data : JSON.stringify(action.data);
    default:
      return JSON.stringify(action);
  }
}

const SourceCodeViewer: React.FC<SourceCodeViewerProps> = ({
  metadata,
  functions,
  selectedFunction,
  onFunctionChange,
  highlightSpan,
  minimized = false,
  fontSize = 12,
  onHoverPositionChange,
  onClickPosition,
  selectionIndicator,
  showSettings = false,
  onToggleSettings,
  onFontSizeChange,
  onToggleMinimized,
  showActionsInCode = false,
  nodes = [],
  allPcgStmtData = new Map(),
  onActionClick,
}) => {
  const containerRef = useRef<HTMLDivElement>(null);
  const [hoverPosition, setHoverPosition] = useState<SourcePos | null>(null);

  // Build a map from relative line numbers to actions for ALL statements in ALL blocks
  type ActionInfo = { text: string; block: number; stmt: number };
  const lineActions = useMemo(() => {
    const map = new Map<number, ActionInfo[]>();

    if (!showActionsInCode) {
      return map;
    }

    type ActionWithStmt = {
      action: {
        data: {
          kind: RepackOp<string, string, string> | BorrowPcgActionKindDebugRepr
        }
      };
      stmtIndex: number
    };

    // Helper to add actions for a given statement in a specific node
    const addActionsForStmt = (node: MirNode, stmtIndex: number, stmtData: PcgProgramPointData) => {
      const stmt = stmtIndex < node.stmts.length
        ? node.stmts[stmtIndex]
        : node.terminator;

      if (!stmt || stmt.span.low.line !== stmt.span.high.line) {
        return; // Only show actions for single-line statements
      }

      const absoluteLine = stmt.span.low.line;
      const relativeLine = absoluteLine - metadata.start.line;

      const allActions: ActionWithStmt[] = [];

      if (Array.isArray(stmtData.actions)) {
        // Terminator actions
        stmtData.actions.forEach((action) => {
          if (action.data.kind.type !== "MakePlaceOld" && action.data.kind.type !== "LabelLifetimeProjection") {
            allActions.push({ action, stmtIndex });
          }
        });
      } else {
        // Statement actions - iterate through all phases
        const stmtActions = stmtData.actions;
        const phases: Array<keyof typeof stmtActions> = ['pre_operands', 'post_operands', 'pre_main', 'post_main'];
        phases.forEach((phase) => {
          const phaseActions = stmtActions[phase];
          if (Array.isArray(phaseActions)) {
            phaseActions.forEach((action) => {
              if (action.data.kind.type !== "MakePlaceOld" && action.data.kind.type !== "LabelLifetimeProjection") {
                allActions.push({ action, stmtIndex });
              }
            });
          }
        });
      }

      // Add all actions for this line with block and statement info
      allActions.forEach(({ action }) => {
        const actionText = actionLine(action.data.kind);
        const existing = map.get(relativeLine) || [];
        existing.push({ text: actionText, block: node.block, stmt: stmtIndex });
        map.set(relativeLine, existing);
      });
    };

    // Process all blocks and all statements in each block
    nodes.forEach((node) => {
      const blockStmtData = allPcgStmtData.get(node.block);
      if (blockStmtData) {
        blockStmtData.forEach((stmtData: PcgProgramPointData, stmtIndex: number) => {
          addActionsForStmt(node, stmtIndex, stmtData);
        });
      }
    });

    return map;
  }, [showActionsInCode, nodes, allPcgStmtData, metadata.start.line]);

  const isSingleLineSpan = (): boolean => {
    if (!highlightSpan) return false;
    return highlightSpan.low.line === highlightSpan.high.line;
  };

  const shouldHighlightLine = (lineIndex: number): boolean => {
    if (!highlightSpan || !isSingleLineSpan()) return false;
    return lineIndex === highlightSpan.low.line;
  };

  const shouldHighlight = (lineIndex: number, charIndex: number): boolean => {
    if (!highlightSpan) return false;

    const { low, high } = highlightSpan;

    if (lineIndex < low.line || lineIndex > high.line) {
      return false;
    }

    if (lineIndex === low.line && lineIndex === high.line) {
      return charIndex >= low.column && charIndex < high.column;
    }

    if (lineIndex === low.line) {
      return charIndex >= low.column;
    }

    if (lineIndex === high.line) {
      return charIndex < high.column;
    }

    return true;
  };

  const handleCharHover = (lineIndex: number, charIndex: number) => {
    const newPosition = { line: lineIndex, column: charIndex };
    setHoverPosition(newPosition);
    onHoverPositionChange?.(newPosition);
  };

  const handleCharClick = (lineIndex: number, charIndex: number) => {
    const position = { line: lineIndex, column: charIndex };
    onClickPosition?.(position);
  };

  const handleMouseLeave = () => {
    setHoverPosition(null);
    onHoverPositionChange?.(null);
  };

  return (
    <div
      style={{
        border: "1px solid #ccc",
        borderRadius: "4px",
        marginTop: "16px",
        maxHeight: "400px",
        overflow: "auto",
      }}
      onMouseLeave={handleMouseLeave}
    >
      <div
        style={{
          backgroundColor: "#f5f5f5",
          borderBottom: minimized ? "none" : "1px solid #ccc",
          padding: "12px 16px",
          display: "flex",
          alignItems: "center",
          gap: "8px",
        }}
      >
        <label htmlFor="function-select" style={{ fontWeight: "bold", whiteSpace: "nowrap" }}>
          Function:
        </label>
        <select
          id="function-select"
          value={selectedFunction}
          onChange={(e) => {
            onFunctionChange(e.target.value as FunctionSlug);
          }}
          style={{
            flex: 1,
            padding: "4px 8px",
            fontSize: "14px",
            borderRadius: "4px",
            border: "1px solid #ccc",
            minWidth: "150px",
          }}
        >
          {Object.keys(functions)
            .sort((a, b) => functions[a as FunctionSlug].name.localeCompare(functions[b as FunctionSlug].name))
            .map((func) => (
              <option key={func} value={func}>
                {functions[func as FunctionSlug].name}
              </option>
            ))}
        </select>
        {onToggleSettings && (
          <button
            onClick={onToggleSettings}
            style={{
              padding: "5px 12px",
              cursor: "pointer",
              backgroundColor: "#4CAF50",
              color: "white",
              border: "none",
              borderRadius: "4px",
              fontSize: "12px",
              whiteSpace: "nowrap",
            }}
          >
            {showSettings ? "Hide Settings" : "Show Settings"}
          </button>
        )}
        {onFontSizeChange && (
          <>
            <button
              onClick={() => onFontSizeChange(Math.max(8, fontSize - 1))}
              style={{
                cursor: "pointer",
                backgroundColor: "#888",
                color: "white",
                border: "none",
                borderRadius: "4px",
                padding: "5px 10px",
                fontSize: "12px",
              }}
              title="Decrease font size"
            >
              A−
            </button>
            <button
              onClick={() => onFontSizeChange(Math.min(24, fontSize + 1))}
              style={{
                cursor: "pointer",
                backgroundColor: "#888",
                color: "white",
                border: "none",
                borderRadius: "4px",
                padding: "5px 10px",
                fontSize: "12px",
              }}
              title="Increase font size"
            >
              A+
            </button>
          </>
        )}
        {onToggleMinimized && (
          <button
            onClick={onToggleMinimized}
            style={{
              cursor: "pointer",
              backgroundColor: "#888",
              color: "white",
              border: "none",
              borderRadius: "4px",
              padding: "5px 10px",
              fontSize: "12px",
            }}
            title={minimized ? "Maximize" : "Minimize"}
          >
            {minimized ? "▼" : "▲"}
          </button>
        )}
      </div>
      {!minimized && (
        <div ref={containerRef}>
          <Highlight theme={themes.github} code={metadata.source} language="rust">
            {({ className, style, tokens, getLineProps, getTokenProps }) => (
              <pre
                className={className}
                style={{
                  ...style,
                  margin: 0,
                  padding: "12px",
                  fontSize: `${fontSize}px`,
                  borderRadius: "0 0 4px 4px",
                }}
              >
                {tokens.map((line, lineIndex) => {
                  let charIndex = 0;
                  const lineHighlighted = shouldHighlightLine(lineIndex);
                  const showIndicator =
                    selectionIndicator?.line === lineIndex &&
                    hoverPosition?.line === lineIndex &&
                    highlightSpan &&
                    highlightSpan.low.line === lineIndex;
                  return (
                    <div
                      key={lineIndex}
                      {...getLineProps({ line })}
                      data-line={lineIndex + 1}
                      style={{ display: "table-row" }}
                    >
                      <span
                        style={{
                          display: "table-cell",
                          textAlign: "right",
                          paddingRight: "1em",
                          userSelect: "none",
                          opacity: 0.5,
                          backgroundColor: lineHighlighted ? "#ffffcc" : "transparent",
                        }}
                      >
                        {lineIndex + 1}
                      </span>
                      <span
                        style={{
                          display: "table-cell",
                          backgroundColor: lineHighlighted ? "#ffffcc" : "transparent",
                        }}
                      >
                        {line.map((token, tokenIndex) => {
                          const tokenContent = token.content;
                          const tokenLength =
                            typeof tokenContent === "string"
                              ? tokenContent.length
                              : 0;
                          const tokenStartChar = charIndex;
                          charIndex += tokenLength;

                          const chars = [];
                          for (let i = 0; i < tokenLength; i++) {
                            const char = tokenContent[i];
                            const highlight = shouldHighlight(
                              lineIndex,
                              tokenStartChar + i
                            );
                            const isHovered =
                              !highlight &&
                              hoverPosition?.line === lineIndex &&
                              hoverPosition?.column === tokenStartChar + i;
                            chars.push(
                              <span
                                key={i}
                                style={{
                                  backgroundColor: highlight
                                    ? "#ffcc00"
                                    : isHovered
                                    ? "#e0e0e0"
                                    : "transparent",
                                  cursor: "pointer",
                                }}
                                onMouseEnter={() => handleCharHover(lineIndex, tokenStartChar + i)}
                                onClick={() => handleCharClick(lineIndex, tokenStartChar + i)}
                              >
                                {char}
                              </span>
                            );
                          }

                          return (
                            <span key={tokenIndex} {...getTokenProps({ token })}>
                              {chars.length > 0 ? chars : token.content}
                            </span>
                          );
                        })}
                        {showIndicator && (
                          <span
                            style={{
                              marginLeft: "0.5em",
                              color: "#666",
                              fontSize: "0.9em",
                              fontStyle: "italic",
                            }}
                          >
                            ({selectionIndicator.index}/{selectionIndicator.total})
                          </span>
                        )}
                        {lineActions.has(lineIndex) && (
                          <span
                            style={{
                              marginLeft: "1em",
                              fontSize: "0.85em",
                              fontStyle: "italic",
                              fontFamily: "monospace",
                            }}
                          >
                            {lineActions.get(lineIndex)!.map((actionInfo, actionIdx) => (
                              <React.Fragment key={actionIdx}>
                                {actionIdx > 0 && <span style={{ color: "#0066cc" }}>, </span>}
                                <span
                                  style={{
                                    color: "#0066cc",
                                    cursor: onActionClick ? "pointer" : "default",
                                    textDecoration: onActionClick ? "underline" : "none",
                                  }}
                                  onClick={(e) => {
                                    e.stopPropagation();
                                    if (onActionClick) {
                                      onActionClick(actionInfo.block, actionInfo.stmt);
                                    }
                                  }}
                                  title={`Block ${actionInfo.block}, Statement ${actionInfo.stmt}`}
                                >
                                  {actionInfo.text}
                                </span>
                              </React.Fragment>
                            ))}
                          </span>
                        )}
                      </span>
                    </div>
                  );
                })}
              </pre>
            )}
          </Highlight>
        </div>
      )}
    </div>
  );
};

export default SourceCodeViewer;

