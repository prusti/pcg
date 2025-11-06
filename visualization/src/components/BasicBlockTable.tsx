import React from "react";
import { BasicBlockData, CurrentPoint, PcgProgramPointData } from "../types";
import ReactDOMServer from "react-dom/server";
import { MirStmt } from "../types";
import { PcgActionDebugRepr } from "../generated/types";
import { actionLine } from "../actionFormatting";

interface BasicBlockTableProps {
  data: BasicBlockData;
  currentPoint: CurrentPoint;
  setCurrentPoint: (point: CurrentPoint) => void;
  hoveredStmts?: Set<string>;
  showActionsInGraph?: boolean;
  pcgStmtData?: Map<number, PcgProgramPointData>;
}

export function isStorageStmt(stmt: string) {
  return stmt.startsWith("StorageLive") || stmt.startsWith("StorageDead");
}

type TableRowProps = {
  index: number | "T";
  stmt: MirStmt;
  selected: boolean;
  hovered: boolean;
  onClick: () => void;
  actions?: string[];
};

function TableRow({ selected, hovered, onClick, stmt, index, actions }: TableRowProps) {
  const tooltip = `Loans invalidated at start: ${stmt.loans_invalidated_start.join(", ")}\nLoans invalidated at mid: ${stmt.loans_invalidated_mid.join(", ")}\nBorrows in scope at start: ${stmt.borrows_in_scope_start.join(", ")}\nBorrows in scope at mid: ${stmt.borrows_in_scope_mid.join(", ")}`;
  return (
    <tr
      className={selected ? "highlight" : ""}
      onClick={onClick}
      title={tooltip}
      style={{
        backgroundColor: selected ? undefined : (hovered ? "#add8e6" : undefined),
      }}
    >
      <td>{index}</td>
      <td>
        <code>{stmt.stmt}</code>
        {actions && actions.length > 0 && (
          <div
            style={{
              marginTop: "4px",
              fontSize: "0.85em",
              fontStyle: "italic",
              fontFamily: "monospace",
              color: "#0066cc",
            }}
          >
            {actions.map((action, idx) => (
              <React.Fragment key={idx}>
                {idx > 0 && <br />}
                {action}
              </React.Fragment>
            ))}
          </div>
        )}
      </td>
    </tr>
  );
}

export default function BasicBlockTable({
  data,
  currentPoint,
  setCurrentPoint,
  hoveredStmts,
  showActionsInGraph,
  pcgStmtData,
}: BasicBlockTableProps) {
  const getActionsForStmt = (stmtIndex: number): string[] => {
    if (!showActionsInGraph || !pcgStmtData) {
      return [];
    }

    const stmtData = pcgStmtData.get(stmtIndex);
    if (!stmtData) {
      return [];
    }

    const actions: string[] = [];

    if (Array.isArray(stmtData.actions)) {
      stmtData.actions.forEach((action: PcgActionDebugRepr) => {
        if (action.data.kind.type !== "MakePlaceOld" && action.data.kind.type !== "LabelLifetimeProjection") {
          actions.push(actionLine(action.data.kind));
        }
      });
    } else {
      const evalStmtActions = stmtData.actions;
      const phases: Array<'pre_operands' | 'post_operands' | 'pre_main' | 'post_main'> = ['pre_operands', 'post_operands', 'pre_main', 'post_main'];
      phases.forEach((phase) => {
        const phaseActions = evalStmtActions[phase];
        if (Array.isArray(phaseActions)) {
          phaseActions.forEach((action: PcgActionDebugRepr) => {
            if (action.data.kind.type !== "MakePlaceOld" && action.data.kind.type !== "LabelLifetimeProjection") {
              actions.push(actionLine(action.data.kind));
            }
          });
        }
      });
    }

    return actions;
  };
  return (
    <table
      cellSpacing={0}
      cellPadding={4}
      style={{
        borderCollapse: "collapse",
        width: "300px",
        boxShadow: "0 0 0 1px black",
      }}
    >
      <tbody>
        <tr>
          <td>(on start)</td>
          <td>
            <b>bb{data.block}</b>
          </td>
        </tr>
        {data.stmts.map((stmt, i) => {
          const stmtId = `${data.block}-${i}`;
          return (
            <TableRow
              key={i}
              index={i}
              stmt={stmt}
              selected={
                currentPoint.type === "stmt" &&
                i === currentPoint.stmt &&
                data.block === currentPoint.block
              }
              hovered={hoveredStmts?.has(stmtId) || false}
              onClick={() =>
                setCurrentPoint({
                  type: "stmt",
                  block: data.block,
                  stmt: i,
                  navigatorPoint: { type: "iteration", name: "post_main" },
                })
              }
              actions={getActionsForStmt(i)}
            />
          );
        })}
        <TableRow
          index="T"
          stmt={data.terminator}
          selected={
            currentPoint.type === "stmt" &&
            currentPoint.stmt == data.stmts.length &&
            data.block === currentPoint.block
          }
          hovered={hoveredStmts?.has(`${data.block}-${data.stmts.length}`) || false}
          onClick={() =>
            setCurrentPoint({
              type: "stmt",
              block: data.block,
              stmt: data.stmts.length,
              navigatorPoint: { type: "iteration", name: "post_main" },
            })
          }
          actions={getActionsForStmt(data.stmts.length)}
        />
      </tbody>
    </table>
  );
}

export function computeTableHeight(
  data: BasicBlockData,
  showActionsInGraph?: boolean,
  pcgStmtData?: Map<number, PcgProgramPointData>
): number {
  const container = document.createElement("div");
  container.innerHTML = ReactDOMServer.renderToString(
    BasicBlockTable({
      currentPoint: {
        type: "stmt",
        block: 0,
        stmt: 0,
        navigatorPoint: { type: "iteration", name: "post_main" },
      },
      data: {
        block: data.block,
        stmts: data.stmts,
        terminator: data.terminator,
      },
      setCurrentPoint: () => {},
      showActionsInGraph,
      pcgStmtData,
    })
  );
  document.body.appendChild(container);
  const height = container.offsetHeight;
  container.remove();
  return height;
}
