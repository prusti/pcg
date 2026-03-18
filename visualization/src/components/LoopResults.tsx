import React, { useEffect, useState } from "react";
import { Api } from "../api";

interface LoopResultsProps {
  selectedFunction: string;
  api: Api;
}

export default function LoopResults({ selectedFunction, api }: LoopResultsProps) {
  const [loopText, setLoopText] = useState<string | null>(null);

  useEffect(() => {
    api.getLoopAnalysis(selectedFunction).then(setLoopText);
  }, [selectedFunction, api]);

  if (loopText === null) {
    return <p>No loop analysis data available.</p>;
  }

  return (
    <pre style={{ fontSize: "12px", whiteSpace: "pre", margin: 0 }}>
      {loopText}
    </pre>
  );
}
