import { ZipFileApi } from "./api";
import { storage } from "./storage";

const CACHED_ZIP_KEY = "cachedZipFile";

export async function loadCachedZip(): Promise<ZipFileApi | null> {
  const cachedZip = storage.getItem(CACHED_ZIP_KEY);
  if (cachedZip) {
    try {
      return await ZipFileApi.fromBase64(cachedZip);
    } catch (error) {
      console.error("Failed to load cached ZIP file:", error);
      storage.removeItem(CACHED_ZIP_KEY);
    }
  }
  return null;
}

export async function cacheZip(zipApi: ZipFileApi): Promise<void> {
  try {
    const base64 = await zipApi.toBase64();
    storage.setItem(CACHED_ZIP_KEY, base64);
  } catch (error) {
    console.error("Failed to cache ZIP file:", error);
  }
}

