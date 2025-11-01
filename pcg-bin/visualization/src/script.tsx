import React, { useState } from "react";
import { createRoot } from "react-dom/client";
import * as Viz from "@viz-js/viz";

import { api, Api, ZipFileApi } from "./api";
import { App } from "./components/App";
import { FunctionSlug } from "./types";
import { loadCachedZip, cacheZip } from "./zipCache";
import { storage } from "./storage";

function getDataZipUrl(): string {
  const params = new URLSearchParams(window.location.search);
  const datasrc = params.get('datasrc');

  if (datasrc) {
    const prefix = datasrc.endsWith('/') ? datasrc : `${datasrc}/`;
    return `${prefix}data.zip`;
  }

  return "data.zip";
}

function AppWrapper() {
  const [currentApi, setCurrentApi] = useState<Api>(api);
  const [initialFunction, setInitialFunction] = useState<FunctionSlug | null>(null);
  const [initialPaths, setInitialPaths] = useState<number[][]>([]);
  const [initialAssertions, setInitialAssertions] = useState<any[]>([]);
  const [functions, setFunctions] = useState<any>(null);
  const [initialPath, setInitialPath] = useState<number>(0);
  const [dataUnavailable, setDataUnavailable] = useState<boolean>(false);
  const [isLoadingCache, setIsLoadingCache] = useState<boolean>(false);

  React.useEffect(() => {
    async function loadData() {
      try {
        const funcs = await currentApi.getFunctions();
        setFunctions(funcs);
        setDataUnavailable(false);
        setIsLoadingCache(false);

        let initFunc = storage.getItem("selectedFunction") as FunctionSlug;
        if (!initFunc || !Object.keys(funcs).includes(initFunc)) {
          initFunc = Object.keys(funcs)[0] as FunctionSlug;
        }
        setInitialFunction(initFunc);

        const paths = await currentApi.getPaths(initFunc);
        setInitialPaths(paths);

        const assertions = await currentApi.getAssertions(initFunc);
        setInitialAssertions(assertions);

        let initPath = 0;
        const initialPathStr = storage.getItem("selectedPath");
        if (initialPathStr) {
          initPath = parseInt(initialPathStr);
          if (initPath >= paths.length) {
            initPath = 0;
          }
        }
        setInitialPath(initPath);
      } catch (error) {
        if (currentApi === api) {
          try {
            const zipUrl = getDataZipUrl();
            const zipApi = await ZipFileApi.fromUrl(zipUrl);
            await cacheZip(zipApi);
            setIsLoadingCache(true);
            setCurrentApi(zipApi);
            return;
          } catch (zipError) {
            console.log("Failed to load data.zip, trying cached ZIP");
          }

          const cachedZip = await loadCachedZip();
          if (cachedZip) {
            setIsLoadingCache(true);
            setCurrentApi(cachedZip);
          } else {
            setDataUnavailable(true);
            setFunctions(null);
            setInitialFunction(null);
          }
        } else {
          setDataUnavailable(true);
          setFunctions(null);
          setInitialFunction(null);
        }
      }
    }

    loadData();
  }, [currentApi]);

  if (dataUnavailable) {
    return (
      <div
        style={{
          display: "flex",
          justifyContent: "center",
          alignItems: "center",
          height: "100vh",
          flexDirection: "column",
        }}
      >
        <input
          type="file"
          accept=".zip"
          id="zip-file-input"
          style={{ display: "none" }}
          onChange={async (e) => {
            const file = e.target.files?.[0];
            if (file) {
              const zipApi = await ZipFileApi.fromFile(file);
              await cacheZip(zipApi);
              setCurrentApi(zipApi);
            }
          }}
        />
        <button
          style={{
            padding: "16px 32px",
            cursor: "pointer",
            backgroundColor: "#4CAF50",
            color: "white",
            border: "none",
            borderRadius: "4px",
            fontSize: "18px",
          }}
          onClick={() => {
            document.getElementById("zip-file-input")?.click();
          }}
        >
          Upload ZIP File
        </button>
      </div>
    );
  }

  if (!functions || !initialFunction || isLoadingCache) {
    return <div>Loading...</div>;
  }

  return (
    <App
      initialFunction={initialFunction}
      initialPaths={initialPaths}
      initialAssertions={initialAssertions}
      functions={functions}
      initialPath={initialPath}
      api={currentApi}
      onApiChange={setCurrentApi}
    />
  );
}

async function main() {
  await Viz.instance();

  const rootElement = document.getElementById("root");
  if (rootElement) {
    const root = createRoot(rootElement);
    root.render(<AppWrapper />);
  }
}

main();
