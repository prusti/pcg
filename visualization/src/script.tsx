import React, { useState } from "react";
import { createRoot } from "react-dom/client";
import * as Viz from "@viz-js/viz";

import { api } from "./api";
import { App } from "./components/App";
import { FunctionSlug, FunctionsMetadata } from "./types";
import { storage } from "./storage";

function AppWrapper() {
  const [functions, setFunctions] = useState<FunctionsMetadata | null>(null);
  const [dataUnavailable, setDataUnavailable] = useState<boolean>(false);

  React.useEffect(() => {
    async function loadData() {
      const result = await api.getFunctions();

      if (result.type === "not_found") {
        setDataUnavailable(true);
        return;
      }

      const functions = result.data;
      const savedSelectedFunction = storage.getItem("selectedFunction") as FunctionSlug | null;
      if (savedSelectedFunction && !Object.keys(functions).includes(savedSelectedFunction)) {
        storage.removeItem("selectedFunction");
      }
      setFunctions(functions);
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
          gap: "20px",
        }}
      >
        <p style={{ fontSize: "18px", fontWeight: "bold" }}>
          Functions data file not found
        </p>
        <p>
          Visit{" "}
          <a
            href="https://pcg.fly.dev"
            style={{ color: "#4A90E2", textDecoration: "underline" }}
            target="_blank"
            rel="noopener noreferrer"
          >
            https://pcg.fly.dev
          </a>
          to upload a new Rust file and visualize its PCG.
        </p>
      </div>
    );
  }

  if (!functions) {
    return <div>Loading...</div>;
  }

  return (
    <App
      functions={functions}
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
