import React, {
  useState,
  useEffect,
  useCallback,
  Dispatch,
  SetStateAction,
} from "react";
import {
  useLocalStorageString,
} from "../hooks/useLocalStorageState";

import {
  CurrentPoint,
  FunctionSlug,
  FunctionsMetadata,
} from "../types";
import { api, ApiFunctionData } from "../api";
import { AppInner } from "./AppInner";

interface AppProps {
  functions: FunctionsMetadata;
}

const INITIAL_POINT: CurrentPoint = {
  type: "stmt",
  block: 0,
  stmt: 0,
  navigatorPoint: {
    type: "iteration",
    name: "initial",
  },
};

export const App: React.FC<AppProps> = ({ functions }) => {
  const [apiFunctionData, setApiFunctionData] =
    useState<ApiFunctionData | null>(null);
  const [currentPoint, setCurrentPoint] = useState<CurrentPoint>(INITIAL_POINT);

  const [selectedFunction, setSelectedFunctionInternal] = useLocalStorageString(
    "selectedFunction",
    Object.keys(functions)[0] as FunctionSlug
  ) as [FunctionSlug, Dispatch<SetStateAction<FunctionSlug>>];

  const setSelectedFunction = useCallback(
    (newFunction: SetStateAction<FunctionSlug>) => {
      setSelectedFunctionInternal(newFunction);
      setCurrentPoint(INITIAL_POINT);
    },
    [setSelectedFunctionInternal, setCurrentPoint]
  );

  useEffect(() => {
    (async () => {
      const apiFunctionData = await api.getApiFunctionData(selectedFunction);
      setApiFunctionData(apiFunctionData);
    })();
  }, [selectedFunction]);

  if (!apiFunctionData) {
    return <div>Loading...</div>;
  } else {
    return (
      <AppInner
        apiFunctionData={apiFunctionData}
        functions={functions}
        currentPoint={currentPoint}
        setCurrentPoint={setCurrentPoint}
        selectedFunction={selectedFunction}
        setSelectedFunction={setSelectedFunction}
      />
    );
  }
};
