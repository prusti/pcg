import React, { useState } from "react";
import { createRoot } from "react-dom/client";
import * as Viz from "@viz-js/viz";

import { api, Api } from "./api";
import { App } from "./components/App";
import { FunctionSlug } from "./types";

function AppWrapper() {
  const [currentApi, setCurrentApi] = useState<Api>(api);
  const [initialFunction, setInitialFunction] = useState<FunctionSlug | null>(null);
  const [initialPaths, setInitialPaths] = useState<number[][]>([]);
  const [initialAssertions, setInitialAssertions] = useState<any[]>([]);
  const [functions, setFunctions] = useState<any>(null);
  const [initialPath, setInitialPath] = useState<number>(0);

  React.useEffect(() => {
    async function loadData() {
      const funcs = await currentApi.getFunctions();
      setFunctions(funcs);

      let initFunc = localStorage.getItem("selectedFunction") as FunctionSlug;
      if (!initFunc || !Object.keys(funcs).includes(initFunc)) {
        initFunc = Object.keys(funcs)[0] as FunctionSlug;
      }
      setInitialFunction(initFunc);

      const paths = await currentApi.getPaths(initFunc);
      setInitialPaths(paths);

      const assertions = await currentApi.getAssertions(initFunc);
      setInitialAssertions(assertions);

      let initPath = 0;
      const initialPathStr = localStorage.getItem("selectedPath");
      if (initialPathStr) {
        initPath = parseInt(initialPathStr);
        if (initPath >= paths.length) {
          initPath = 0;
        }
      }
      setInitialPath(initPath);
    }

    loadData();
  }, [currentApi]);

  if (!functions || !initialFunction) {
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
