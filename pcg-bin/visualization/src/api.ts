import { Assertion } from "./components/Assertions";
import { MirGraph, StmtGraphs } from "./generated/types";
import {
  CurrentPoint,
  FunctionsMetadata,
  PcgProgramPointData,
} from "./types";
import * as JSZip from "jszip";

export type PcgBlockDotGraphs = StmtGraphs<string>[];

export abstract class Api {
  protected abstract fetchJsonFile(filePath: string): Promise<unknown>;
  protected abstract fetchTextFile(filePath: string): Promise<string>;

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

  async getPaths(functionName: string): Promise<number[][]> {
    try {
      const paths = await this.fetchJsonFile(
        `data/${functionName}/paths.json`
      );
      return paths as number[][];
    } catch (error) {
      return [];
    }
  }

  async getAssertions(functionName: string): Promise<Assertion[]> {
    try {
      const assertions = await this.fetchJsonFile(
        `data/${functionName}/assertions.json`
      );
      return assertions as Assertion[];
    } catch (error) {
      return [];
    }
  }

  async getPcgProgramPointData(
    functionName: string,
    currentPoint: CurrentPoint
  ): Promise<PcgProgramPointData> {
    const path =
      currentPoint.type === "stmt"
        ? `block_${currentPoint.block}_stmt_${currentPoint.stmt}`
        : `block_${currentPoint.block1}_term_block_${currentPoint.block2}`;

    return await this.fetchJsonFile(`data/${functionName}/${path}_pcg_data.json`) as Promise<PcgProgramPointData>;
  }

  async getPathData(
    functionName: string,
    path: number[],
    point:
      | {
          stmt: number;
        }
      | {
          terminator: number;
        }
  ) {
    const last_component =
      "stmt" in point ? `stmt_${point.stmt}` : `bb${point.terminator}_transition`;
    const endpoint = `data/${functionName}/path_${path.map((block) => `bb${block}`).join("_")}_${last_component}.json`;
    return await this.fetchJsonFile(endpoint);
  }

  async fetchDotFile(filePath: string): Promise<string> {
    return await this.fetchTextFile(filePath);
  }
}

class FetchApi extends Api {
  protected async fetchJsonFile(filePath: string): Promise<unknown> {
    const response = await fetch(filePath);
    return await response.json();
  }

  protected async fetchTextFile(filePath: string): Promise<string> {
    const response = await fetch(filePath);
    return await response.text();
  }
}

export class ZipFileApi extends Api {
  private zipFile: JSZip;

  constructor(zipFile: JSZip) {
    super();
    this.zipFile = zipFile;
  }

  static async fromFile(file: File): Promise<ZipFileApi> {
    const zip = await JSZip.loadAsync(file);
    return new ZipFileApi(zip);
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

export const api = new FetchApi();
