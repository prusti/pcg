import React, { useRef, useState } from "react";
import { Highlight, themes } from "prism-react-renderer";
import { FunctionMetadata, SourcePos } from "../types";

type RelativeSpan = {
  low: SourcePos;
  high: SourcePos;
};

interface SourceCodeViewerProps {
  metadata: FunctionMetadata;
  highlightSpan?: RelativeSpan | null;
  minimized?: boolean;
  fontSize?: number;
  onHoverPositionChange?: (position: SourcePos | null) => void;
  onClickPosition?: (position: SourcePos) => void;
}

const SourceCodeViewer: React.FC<SourceCodeViewerProps> = ({
  metadata,
  highlightSpan,
  minimized = false,
  fontSize = 12,
  onHoverPositionChange,
  onClickPosition,
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
      <h3
        style={{
          marginTop: 0,
          marginBottom: 0,
          padding: "12px 16px",
          backgroundColor: "#f5f5f5",
          borderBottom: minimized ? "none" : "1px solid #ccc",
        }}
      >
        {metadata.name}
      </h3>
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

