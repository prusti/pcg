import React from "react";
import { Api, PcgBlockDotGraphs } from "../api";
import { CurrentPoint, FunctionSlug } from "../types";
import { openDotGraphInNewWindow } from "../dot_graph";
import BorrowCheckerGraphs from "./BorrowCheckerGraphs";

interface SettingsProps {
  showSettings: boolean;
  onClose: () => void;
  showActionsInCode: boolean;
  setShowActionsInCode: (value: boolean) => void;
  showPCG: boolean;
  setShowPCG: (value: boolean) => void;
  showPCGNavigator: boolean;
  setShowPCGNavigator: (value: boolean) => void;
  currentPoint: CurrentPoint;
  selectedFunction: FunctionSlug;
  iterations: PcgBlockDotGraphs;
  api: Api;
}

const getPCGDotGraphFilename = (
  currentPoint: CurrentPoint,
  selectedFunction: string,
  graphs: PcgBlockDotGraphs
): string | null => {
  if (currentPoint.type !== "stmt" || graphs.length <= currentPoint.stmt) {
    return null;
  }
  if (currentPoint.navigatorPoint.type === "action") {
    if (currentPoint.navigatorPoint.phase === "successor") {
      return null;
    }
    const stmt = graphs[currentPoint.stmt];
    const iterationActions = stmt.actions;
    const actionGraphFilenames =
      iterationActions[currentPoint.navigatorPoint.phase];
    return `data/${selectedFunction}/${actionGraphFilenames[currentPoint.navigatorPoint.index]}`;
  }

  const navPoint = currentPoint.navigatorPoint;
  if (navPoint.type !== "iteration") {
    return null;
  }

  const phases = graphs[currentPoint.stmt].at_phase;
  const phaseIndex = phases.findIndex((p) => p.phase === navPoint.name);

  if (phaseIndex === -1 || phases.length === 0) {
    return null;
  }

  const filename: string = phases[phaseIndex].filename;
  return `data/${selectedFunction}/${filename}`;
};

export default function Settings({
  showSettings,
  onClose,
  showActionsInCode,
  setShowActionsInCode,
  showPCG,
  setShowPCG,
  showPCGNavigator,
  setShowPCGNavigator,
  currentPoint,
  selectedFunction,
  iterations,
  api,
}: SettingsProps) {
  if (!showSettings) {
    return null;
  }

  return (
    <div
      style={{
        position: "fixed",
        right: 0,
        top: 0,
        bottom: 0,
        width: "300px",
        backgroundColor: "#f5f5f5",
        borderLeft: "2px solid #ccc",
        padding: "20px",
        overflowY: "auto",
        zIndex: 1100,
        boxShadow: "-2px 0 5px rgba(0,0,0,0.1)",
      }}
    >
      <h3 style={{ marginTop: 0 }}>Settings</h3>
      <button
        onClick={onClose}
        style={{
          position: "absolute",
          top: "10px",
          right: "10px",
          cursor: "pointer",
          backgroundColor: "#f44336",
          color: "white",
          border: "none",
          borderRadius: "4px",
          padding: "5px 10px",
        }}
      >
        ✕
      </button>

      <div style={{ marginBottom: "20px" }}>
        <label style={{ display: "block", marginBottom: "10px" }}>
          <input
            type="checkbox"
            checked={showActionsInCode}
            onChange={(e) => setShowActionsInCode(e.target.checked)}
          />{" "}
          Show Actions in MIR Graph
        </label>
        <label style={{ display: "block", marginBottom: "10px" }}>
          <input
            type="checkbox"
            checked={showPCG}
            onChange={(e) => setShowPCG(e.target.checked)}
          />{" "}
          Show PCG
        </label>
        <button
          style={{
            width: "100%",
            padding: "8px",
            marginBottom: "10px",
            cursor: "pointer",
          }}
          onClick={async () => {
            const dotFilePath = getPCGDotGraphFilename(
              currentPoint,
              selectedFunction,
              iterations
            );
            if (dotFilePath) {
              openDotGraphInNewWindow(api, dotFilePath);
            }
          }}
        >
          Open Current PCG in New Window
        </button>
        <label style={{ display: "block", marginBottom: "10px" }}>
          <input
            type="checkbox"
            checked={showPCGNavigator}
            onChange={(e) => setShowPCGNavigator(e.target.checked)}
          />{" "}
          Show PCG Navigator
        </label>
      </div>

      <div style={{ marginBottom: "20px" }}>
        <h4>Borrow Checker</h4>
        <BorrowCheckerGraphs
          currentPoint={currentPoint}
          selectedFunction={selectedFunction}
          api={api}
        />
      </div>
    </div>
  );
}

