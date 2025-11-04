const LOCALSTORAGE_VERSION = "v1";

class VersionedStorage {
  private prefix: string;

  constructor(version: string) {
    this.prefix = `${version}:`;
  }

  private getKey(key: string): string {
    return `${this.prefix}${key}`;
  }

  getItem(key: string): string | null {
    return localStorage.getItem(this.getKey(key));
  }

  getNumber(key: string, defaultValue: number): number {
    const value = this.getItem(key);
    if (value === null) {
      return defaultValue;
    }
    return parseInt(value, 10);
  }

  setItem(key: string, value: string): void {
    localStorage.setItem(this.getKey(key), value);
  }

  removeItem(key: string): void {
    localStorage.removeItem(this.getKey(key));
  }

  setBool(key: string, value: boolean): void {
    this.setItem(key, value.toString());
  }

  setNumber(key: string, value: number): void {
    this.setItem(key, value.toString());
  }

  getBool(key: string, defaultValue: boolean): boolean {
    const value = this.getItem(key);
    if (value === null) {
      return defaultValue;
    }
    return value === "true";
  }

  clear(): void {
    const keys = Object.keys(localStorage);
    keys.forEach((key) => {
      if (key.startsWith(this.prefix)) {
        localStorage.removeItem(key);
      }
    });
  }
}

export const storage = new VersionedStorage(LOCALSTORAGE_VERSION);

