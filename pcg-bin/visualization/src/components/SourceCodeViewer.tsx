import React, { useRef, useEffect } from "react";
import { Highlight, themes } from "prism-react-renderer";
import { FunctionMetadata, SourcePos } from "../types";

type RelativeSpan = {
  low: SourcePos;
  high: SourcePos;
};

interface SourceCodeViewerProps {
  metadata: FunctionMetadata;
  highlightSpan?: RelativeSpan | null;
}

const SourceCodeViewer: React.FC<SourceCodeViewerProps> = ({
  metadata,
  highlightSpan,
}) => {
  const containerRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (!highlightSpan || !containerRef.current) {
      return;
    }

    const startLine = highlightSpan.low.line + 1;
    const container = containerRef.current;
    const lineElement = container.querySelector(
      `[data-line="${startLine}"]`
    );

    if (lineElement) {
      lineElement.scrollIntoView({ behavior: "smooth", block: "center" });
    }
  }, [highlightSpan]);

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

  return (
    <div
      ref={containerRef}
      style={{
        maxHeight: "400px",
        overflow: "auto",
      }}
    >
      <h3
        style={{
          marginTop: 0,
          marginBottom: 0,
          padding: "12px 16px",
          backgroundColor: "#f5f5f5",
          borderBottom: "1px solid #ccc",
        }}
      >
        {metadata.name}
      </h3>
      <Highlight theme={themes.github} code={metadata.source} language="rust">
        {({ className, style, tokens, getLineProps, getTokenProps }) => (
          <pre
            className={className}
            style={{
              ...style,
              margin: 0,
              padding: "12px",
              fontSize: "12px",
              borderRadius: "0 0 4px 4px",
              overflow: "auto",
            }}
          >
            {tokens.map((line, lineIndex) => {
              let charIndex = 0;
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
                    }}
                  >
                    {lineIndex + 1}
                  </span>
                  <span style={{ display: "table-cell" }}>
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
                        chars.push(
                          <span
                            key={i}
                            style={{
                              backgroundColor: highlight
                                ? "#ffff99"
                                : "transparent",
                            }}
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
  );
};

export default SourceCodeViewer;

