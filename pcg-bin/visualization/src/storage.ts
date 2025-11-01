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

  setItem(key: string, value: string): void {
    localStorage.setItem(this.getKey(key), value);
  }

  removeItem(key: string): void {
    localStorage.removeItem(this.getKey(key));
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

