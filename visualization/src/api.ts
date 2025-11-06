import { MirGraph, PcgFunctionData, StmtGraphs } from "./generated/types";
import {
  FunctionsMetadata,
  PcgProgramPointData,
  StringOf,
} from "./types";
import * as JSZip from "jszip";

export type PcgBlockDotGraphs = StmtGraphs<StringOf<"DataflowStmtPhase">>[];

export abstract class Api {
  protected abstract fetchJsonFile(filePath: string): Promise<unknown>;
  protected abstract fetchTextFile(filePath: string): Promise<string>;
  private pcgDataCache: Map<string, PcgFunctionData> = new Map();

  async getPcgIterations(functionName: string, block: number): Promise<PcgBlockDotGraphs> {
    const iterations = await this.fetchJsonFile(
      `data/${functionName}/block_${block}_iterations.json`
    );
    return iterations as PcgBlockDotGraphs;
  }

  async getGraphData(func: string): Promise<MirGraph> {
    const graphFilePath = `data/${func}/mir.json`;
    return await this.fetchJsonFile(graphFilePath) as Promise<MirGraph>;
  }

  async getFunctions(): Promise<FunctionsMetadata> {
    return await this.fetchJsonFile("data/functions.json") as Promise<FunctionsMetadata>;
  }

  public async getPcgFunctionData(functionName: string): Promise<PcgFunctionData> {
    if (!this.pcgDataCache.has(functionName)) {
      const data = await this.fetchJsonFile(`data/${functionName}/pcg_data.json`) as PcgFunctionData;
      this.pcgDataCache.set(functionName, data);
    }
    return this.pcgDataCache.get(functionName)!;
  }

  async getAllPcgStmtData(
    functionName: string
  ): Promise<Map<number, Map<number, PcgProgramPointData>>> {
    const functionData = await this.getPcgFunctionData(functionName);
    const result = new Map<number, Map<number, PcgProgramPointData>>();

    Object.entries(functionData.blocks).forEach(([blockId, blockData]) => {
      const blockNum = parseInt(blockId);
      const stmtMap = new Map<number, PcgProgramPointData>();
      blockData.statements.forEach((stmtData, stmtIndex) => {
        stmtMap.set(stmtIndex, stmtData);
      });
      result.set(blockNum, stmtMap);
    });

    return result;
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
      this.prefix = prefix.endsWith('/') ? prefix : `${prefix}/`;
    } else {
      this.prefix = '';
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
      throw new Error(`Failed to fetch ZIP file from ${url}: ${response.statusText}`);
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
  const datasrc = params.get('datasrc');

  return new FetchApi(datasrc || undefined);
}

function getDataZipUrl(): string {
  const params = new URLSearchParams(window.location.search);
  const datasrc = params.get('datasrc');

  if (datasrc) {
    const prefix = datasrc.endsWith('/') ? datasrc : `${datasrc}/`;
    return `${prefix}data.zip`;
  }

  return "data.zip";
}

export async function getDefaultApi(): Promise<Api> {
  const fetchApi = createDefaultApi();

  try {
    await fetchApi.getFunctions();
    return fetchApi;
  } catch {
    console.log("Failed to load data/functions.json, trying data.zip");
  }

  try {
    const zipUrl = getDataZipUrl();
    const zipApi = await ZipFileApi.fromUrl(zipUrl);
    return zipApi;
  } catch {
    console.log("Failed to load data.zip");
  }

  throw new Error("No data source available");
}

export const api = createDefaultApi();
