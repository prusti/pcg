import { MirGraph } from "./generated_types/MirGraph";
import { PcgVisualizationData } from "./generated_types/PcgVisualizationData";
import { FunctionsMetadata, GetFunctionsResult } from "./types";
import * as JSZip from "jszip";

export type ApiFunctionData = {
  pcgData: PcgVisualizationData;
  mirGraph: MirGraph;
};

export abstract class Api {
  protected abstract fetchJsonFile(filePath: string): Promise<unknown>;
  protected abstract fetchTextFile(filePath: string): Promise<string>;
  private pcgDataCache: Map<string, PcgVisualizationData> = new Map();

  async getApiFunctionData(functionName: string): Promise<ApiFunctionData> {
    return {
      pcgData: await this.getPcgVisualizationData(functionName),
      mirGraph: await this.getGraphData(functionName),
    };
  }

  async getGraphData(func: string): Promise<MirGraph> {
    const graphFilePath = `data/${func}/mir.json`;
    return (await this.fetchJsonFile(graphFilePath)) as Promise<MirGraph>;
  }

  async getFunctions(): Promise<GetFunctionsResult> {
    try {
      const data = (await this.fetchJsonFile(
        "data/functions.json"
      )) as FunctionsMetadata;
      return { type: "found", data };
    } catch {
      return { type: "not_found" };
    }
  }

  public async getPcgVisualizationData(
    functionName: string
  ): Promise<PcgVisualizationData> {
    if (!this.pcgDataCache.has(functionName)) {
      const data = (await this.fetchJsonFile(
        `data/${functionName}/pcg_data.json`
      )) as PcgVisualizationData;
      this.pcgDataCache.set(functionName, data);
    }
    return this.pcgDataCache.get(functionName)!;
  }

  async fetchDotFile(filePath: string): Promise<string> {
    return await this.fetchTextFile(filePath);
  }
}

class FetchApi extends Api {
  private prefix: string;

  constructor(prefix?: string) {
    super();
    if (prefix) {
      this.prefix = prefix.endsWith("/") ? prefix : `${prefix}/`;
    } else {
      this.prefix = "";
    }
  }

  protected async fetchJsonFile(filePath: string): Promise<unknown> {
    const response = await fetch(`${this.prefix}${filePath}`);
    return await response.json();
  }

  protected async fetchTextFile(filePath: string): Promise<string> {
    const response = await fetch(`${this.prefix}${filePath}`);
    return await response.text();
  }
}

export class ZipFileApi extends Api {
  private zipFile: JSZip;

  constructor(zipFile: JSZip) {
    super();
    this.zipFile = zipFile;
  }

  static async fromFile(file: Blob): Promise<ZipFileApi> {
    const zip = await JSZip.loadAsync(file);
    return new ZipFileApi(zip);
  }

  static async fromBase64(base64String: string): Promise<ZipFileApi> {
    const zip = await JSZip.loadAsync(base64String, { base64: true });
    return new ZipFileApi(zip);
  }

  static async fromUrl(url: string): Promise<ZipFileApi> {
    const response = await fetch(url);
    if (!response.ok) {
      throw new Error(
        `Failed to fetch ZIP file from ${url}: ${response.statusText}`
      );
    }
    const arrayBuffer = await response.arrayBuffer();
    const zip = await JSZip.loadAsync(arrayBuffer);
    return new ZipFileApi(zip);
  }

  async toBase64(): Promise<string> {
    return await this.zipFile.generateAsync({ type: "base64" });
  }

  protected async fetchJsonFile(filePath: string): Promise<unknown> {
    const file = this.zipFile.file(filePath);
    if (!file) {
      throw new Error(`File not found in zip: ${filePath}`);
    }
    const content = await file.async("string");
    return JSON.parse(content);
  }

  protected async fetchTextFile(filePath: string): Promise<string> {
    const file = this.zipFile.file(filePath);
    if (!file) {
      throw new Error(`File not found in zip: ${filePath}`);
    }
    return await file.async("string");
  }
}

function createDefaultApi(): Api {
  const params = new URLSearchParams(window.location.search);
  const datasrc = params.get("datasrc");

  return new FetchApi(datasrc || undefined);
}

export const api = createDefaultApi();
