import React from "react";
import { FunctionSlug, FunctionsMetadata } from "../types";

interface FunctionSelectorProps {
  functions: FunctionsMetadata;
  selectedFunction: FunctionSlug;
  onChange: (selectedFunction: FunctionSlug) => void;
}

const FunctionSelector: React.FC<FunctionSelectorProps> = ({
  functions,
  selectedFunction,
  onChange,
}) => {
  return (
    <>
      <label htmlFor="function-select">Select Function:</label>
      <select
        id="function-select"
        value={selectedFunction}
        onChange={(e) => {
          onChange(e.target.value as FunctionSlug);
        }}
      >
        {Object.keys(functions)
          .sort((a, b) => functions[a as FunctionSlug].name.localeCompare(functions[b as FunctionSlug].name))
          .map((func) => (
            <option key={func} value={func}>
              {functions[func as FunctionSlug].name}
            </option>
          ))}
      </select>
    </>
  );
};

export default FunctionSelector;
