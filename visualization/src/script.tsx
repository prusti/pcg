import React, { useState } from "react";
import { createRoot } from "react-dom/client";
import * as Viz from "@viz-js/viz";

import { getDefaultApi, Api, ZipFileApi } from "./api";
import { App } from "./components/App";
import { FunctionSlug, FunctionsMetadata } from "./types";
import { cacheZip } from "./zipCache";
import { storage } from "./storage";

function AppWrapper() {
  const [currentApi, setCurrentApi] = useState<Api | null>(null);
  const [initialFunction, setInitialFunction] = useState<FunctionSlug | null>(null);
  const [functions, setFunctions] = useState<FunctionsMetadata | null>(null);
  const [initialPath, setInitialPath] = useState<number>(0);
  const [dataUnavailable, setDataUnavailable] = useState<boolean>(false);

  React.useEffect(() => {
    async function loadData() {
      try {
        const api = await getDefaultApi();
        setCurrentApi(api);

        const funcs = await api.getFunctions();
        setFunctions(funcs);
        setDataUnavailable(false);

        let initFunc = storage.getItem("selectedFunction") as FunctionSlug;
        if (!initFunc || !Object.keys(funcs).includes(initFunc)) {
          initFunc = Object.keys(funcs)[0] as FunctionSlug;
        }
        setInitialFunction(initFunc);

        let initPath = 0;
        const initialPathStr = storage.getItem("selectedPath");
        if (initialPathStr) {
          initPath = parseInt(initialPathStr);
        }
        setInitialPath(initPath);
      } catch {
        setDataUnavailable(true);
        setFunctions(null);
        setInitialFunction(null);
      }
    }

    loadData();
  }, []);

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

  if (!functions || !initialFunction || !currentApi) {
    return <div>Loading...</div>;
  }

  return (
    <App
      initialFunction={initialFunction}
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
