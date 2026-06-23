import * as Viz from "@viz-js/viz";
import { Api } from "./api";

export type DotGraphSidebar = {
    title: string;
    items: string[];
};

function renderDotInPopup(dotData: string, title: string, sidebar?: DotGraphSidebar) {
    Viz.instance().then((viz) => {
      const svgElement = viz.renderSVGElement(dotData);
      const popup = window.open(
        "",
        "_blank",
        "width=800,height=600"
      );
      if (!popup) {
        console.error("Failed to open popup window");
        return;
      }
      popup.document.head.innerHTML = `
        <title>${title}</title>
        <style>
          body { margin: 0; font-family: sans-serif; }
          .dot-popup {
            display: flex;
            width: 100vw;
            height: 100vh;
            overflow: hidden;
          }
          .dot-sidebar {
            box-sizing: border-box;
            width: 360px;
            flex: 0 0 360px;
            padding: 16px;
            border-right: 1px solid #ddd;
            overflow: auto;
            background: #f8f8f8;
          }
          .dot-sidebar h2 {
            margin: 0 0 12px;
            font-size: 16px;
          }
          .dot-sidebar ol {
            margin: 0;
            padding-left: 24px;
          }
          .dot-sidebar li {
            margin-bottom: 8px;
            font-family: monospace;
            white-space: pre-wrap;
            overflow-wrap: anywhere;
          }
          .dot-graph {
            flex: 1;
            min-width: 0;
            overflow: hidden;
          }
          svg {
            width: 100%;
            height: 100%;
            display: block;
          }
        </style>
      `;
      const container = document.createElement("div");
      container.className = "dot-popup";

      if (sidebar) {
        const sidebarElement = document.createElement("div");
        sidebarElement.className = "dot-sidebar";

        const heading = document.createElement("h2");
        heading.textContent = sidebar.title;
        sidebarElement.appendChild(heading);

        if (sidebar.items.length === 0) {
          const empty = document.createElement("p");
          empty.textContent = "No actions.";
          sidebarElement.appendChild(empty);
        } else {
          const list = document.createElement("ol");
          sidebar.items.forEach((item) => {
            const listItem = document.createElement("li");
            listItem.textContent = item;
            list.appendChild(listItem);
          });
          sidebarElement.appendChild(list);
        }

        container.appendChild(sidebarElement);
      }

      const graphContainer = document.createElement("div");
      graphContainer.className = "dot-graph";
      graphContainer.appendChild(svgElement);
      container.appendChild(graphContainer);

      popup.document.body.appendChild(container);
    });
}

export async function openDotGraphInNewWindow(
    api: Api,
    filename: string,
    title?: string,
    sidebar?: DotGraphSidebar
) {
    const dotData = await api.fetchDotFile(filename);
    renderDotInPopup(dotData, title || `Dot Graph - ${filename}`, sidebar);
}

export function openDotStringInNewWindow(dotData: string, title?: string) {
    renderDotInPopup(dotData, title || "DOT Graph");
}
