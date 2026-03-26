import * as Viz from "@viz-js/viz";
import { Api } from "./api";

function renderDotInPopup(dotData: string, title: string) {
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
          body { margin: 0; }
          svg {
            width: 100vw;
            height: 100vh;
            display: block;
          }
        </style>
      `;
      popup.document.body.appendChild(svgElement);
    });
}

export async function openDotGraphInNewWindow(api: Api, filename: string, title?: string) {
    const dotData = await api.fetchDotFile(filename);
    renderDotInPopup(dotData, title || `Dot Graph - ${filename}`);
}

export function openDotStringInNewWindow(dotData: string, title?: string) {
    renderDotInPopup(dotData, title || "DOT Graph");
}
