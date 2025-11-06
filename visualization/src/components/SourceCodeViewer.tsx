import React, { useRef, useState } from "react";
import { Highlight, themes } from "prism-react-renderer";
import { FunctionMetadata, FunctionSlug, FunctionsMetadata, SourcePos } from "../types";

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
}) => {
  const containerRef = useRef<HTMLDivElement>(null);
  const [hoverPosition, setHoverPosition] = useState<SourcePos | null>(null);

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

