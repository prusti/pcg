import React, { useRef, useEffect } from "react";
import { Prism as SyntaxHighlighter } from "react-syntax-highlighter";
import { vs } from "react-syntax-highlighter/dist/esm/styles/prism";
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
      `[data-line-number="${startLine}"]`
    );

    if (lineElement) {
      lineElement.scrollIntoView({ behavior: "smooth", block: "center" });
    }
  }, [highlightSpan]);

  const customStyle = {
    margin: 0,
    fontSize: "12px",
    borderRadius: "0 0 4px 4px",
  };

  const lineProps = (lineNumber: number) => {
    const style: React.CSSProperties = {
      display: "block",
    };

    if (highlightSpan) {
      const startLine = highlightSpan.low.line;
      const endLine = highlightSpan.high.line;

      if (lineNumber >= startLine + 1 && lineNumber <= endLine + 1) {
        style.backgroundColor = "#ffff99";
      }
    }

    return {
      style,
      "data-line-number": lineNumber,
    };
  };

  return (
    <div
      ref={containerRef}
      style={{
        border: "1px solid #ccc",
        borderRadius: "4px",
        marginTop: "16px",
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
      <SyntaxHighlighter
        language="rust"
        style={vs}
        customStyle={customStyle}
        showLineNumbers={true}
        lineProps={lineProps}
      >
        {metadata.source}
      </SyntaxHighlighter>
    </div>
  );
};

export default SourceCodeViewer;

