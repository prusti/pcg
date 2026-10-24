import * as Viz from "@viz-js/viz";
import { Api } from "./api";

export type PcgRenderer = "svg" | "dot";

async function loadDot(api: Api, dotPath: string) {
  const dot = await api.fetchDotFile(dotPath);
  const viz = await Viz.instance();
  return {
    svg: viz.renderSVGElement(dot),
    metadataPath: dotPath.replace(/\.dot$/, ".json"),
    renderer: "dot" as const,
  };
}

export async function loadPcgGraph(api: Api, dotPath: string, renderer: PcgRenderer = "svg"): Promise<{
  svg: globalThis.SVGSVGElement;
  metadataPath: string;
  renderer: PcgRenderer;
}> {
  if (renderer === "dot") return loadDot(api, dotPath);
  const svgPath = dotPath.replace(/\.dot$/, ".svg");
  try {
    const source = await api.fetchDotFile(svgPath);
    const document = new window.DOMParser().parseFromString(source, "image/svg+xml");
    const root = document.documentElement;
    if (root.localName !== "svg" || root.namespaceURI !== "http://www.w3.org/2000/svg" || document.querySelector("parsererror")) {
      throw new Error(`Invalid SVG: ${svgPath}`);
    }
    return {
      svg: root as unknown as globalThis.SVGSVGElement,
      metadataPath: svgPath + ".json",
      renderer: "svg",
    };
  } catch {
    // Older snapshot archives contain only DOT files.
    return loadDot(api, dotPath);
  }
}
