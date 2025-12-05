import { useState, useEffect, Dispatch, SetStateAction } from "react";
import { storage } from "../storage";

export function useLocalStorageBool(
  key: string,
  defaultValue: boolean
): [boolean, Dispatch<SetStateAction<boolean>>] {
  const [value, setValue] = useState(() => storage.getBool(key, defaultValue));

  useEffect(() => {
    storage.setBool(key, value);
  }, [key, value]);

  return [value, setValue];
}

export function useLocalStorageString<T extends string = string>(
  key: string,
  defaultValue: T
): [T, Dispatch<SetStateAction<T>>] {
  const [value, setValue] = useState<T>(
    () => (storage.getItem(key) as T) || defaultValue
  );

  useEffect(() => {
    storage.setItem(key, value);
  }, [key, value]);

  return [value, setValue];
}

export function useLocalStorageNumber(
  key: string,
  defaultValue: number
): [number, Dispatch<SetStateAction<number>>] {
  const [value, setValue] = useState(() =>
    storage.getNumber(key, defaultValue)
  );

  useEffect(() => {
    storage.setNumber(key, value);
  }, [key, value]);

  return [value, setValue];
}

