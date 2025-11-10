const LOCALSTORAGE_VERSION = "v3";

interface StorageEntry {
  value: string;
  lastAccessed: number;
}

class VersionedStorage {
  private prefix: string;
  private ttlMs: number;

  constructor(version: string, ttlHours: number = 3) {
    this.prefix = `${version}:`;
    this.ttlMs = ttlHours * 60 * 60 * 1000;
  }

  private getKey(key: string): string {
    return `${this.prefix}${key}`;
  }

  private isExpired(entry: StorageEntry): boolean {
    const now = Date.now();
    return now - entry.lastAccessed > this.ttlMs;
  }

  private getEntry(key: string): StorageEntry | null {
    const rawValue = localStorage.getItem(this.getKey(key));
    if (rawValue === null) {
      return null;
    }

    try {
      const entry = JSON.parse(rawValue) as StorageEntry;
      if (this.isExpired(entry)) {
        this.removeItem(key);
        return null;
      }
      return entry;
    } catch {
      return null;
    }
  }

  private setEntry(key: string, value: string): void {
    const entry: StorageEntry = {
      value,
      lastAccessed: Date.now(),
    };
    localStorage.setItem(this.getKey(key), JSON.stringify(entry));
  }

  private updateAccessTime(key: string, entry: StorageEntry): void {
    entry.lastAccessed = Date.now();
    localStorage.setItem(this.getKey(key), JSON.stringify(entry));
  }

  getItem(key: string): string | null {
    const entry = this.getEntry(key);
    if (entry === null) {
      return null;
    }
    this.updateAccessTime(key, entry);
    return entry.value;
  }

  getNumber(key: string, defaultValue: number): number {
    const value = this.getItem(key);
    if (value === null) {
      return defaultValue;
    }
    return parseInt(value, 10);
  }

  setItem(key: string, value: string): void {
    this.setEntry(key, value);
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

