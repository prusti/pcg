import * as Viz from "@viz-js/viz";
import { Api } from "./api";

export async function openDotGraphInNewWindow(api: Api, filename: string) {
    const dotData = await api.fetchDotFile(filename);
    Viz.instance().then((viz) => {
      const svgElement = viz.renderSVGElement(dotData);
      const popup = window.open(
        "",
        `Dot Graph - ${filename}`,
        "width=800,height=600"
      );
      if (!popup) {
        console.error("Failed to open popup window");
        return;
      }
      popup.document.head.innerHTML = `
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
