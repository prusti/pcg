use std::{fs, io, path::Path, sync::Arc};

use crate::rustc_interface::span::source_map::FileLoader;

pub struct StringLoader(pub String);

impl FileLoader for StringLoader {
    fn file_exists(&self, _: &Path) -> bool {
        true
    }

    fn read_file(&self, _: &Path) -> io::Result<String> {
        Ok(self.0.clone())
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        Ok(fs::read(path)?.into())
    }
}
