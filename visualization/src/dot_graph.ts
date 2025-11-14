import * as Viz from "@viz-js/viz";
import { Api } from "./api";

export async function openDotGraphInNewWindow(api: Api, filename: string) {
    const dotData = await api.fetchDotFile(filename);

    // Try to load corresponding JSON file
    const jsonFilename = filename.replace(/\.dot$/, '.json');
    let edgeMetadata: Record<string, any> | null = null;
    try {
      const jsonData = await api.fetchDotFile(jsonFilename);
      edgeMetadata = JSON.parse(jsonData);
    } catch (e) {
      // JSON file doesn't exist, that's fine
      console.log(`No metadata file found for ${filename}`);
    }

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

      // Add hover listeners for edges if we have metadata
      if (edgeMetadata) {
        const gElements = popup.document.querySelectorAll('g[id]');
        gElements.forEach((gElement) => {
          const id = gElement.getAttribute('id');
          if (id && edgeMetadata![id]) {
            gElement.addEventListener('mouseenter', () => {
              console.log(`Edge ${id} metadata:`, edgeMetadata![id]);
            });
          }
        });
      }
    });
}
