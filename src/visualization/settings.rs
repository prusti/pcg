use std::io::Write;

use crate::{
    utils::PcgSettings,
    visualization::{FunctionMetadata, FunctionSlug, FunctionsMetadata},
};

impl PcgSettings {
    pub(crate) fn write_functions_json(&self, metadata: &FunctionsMetadata) {
        let file_path = self.functions_json_path();
        let json_data =
            serde_json::to_string(metadata).expect("Failed to serialize item names to JSON");
        let mut file = std::fs::File::create(file_path).expect("Failed to create JSON file");
        file.write_all(json_data.as_bytes())
            .expect("Failed to write item names to JSON file");
    }

    pub(crate) fn read_functions_json(&self) -> FunctionsMetadata {
        let file_path = self.functions_json_path();
        if !file_path.exists() {
            return FunctionsMetadata::new();
        }
        let json_data = std::fs::read_to_string(file_path).expect("Failed to read JSON file");
        serde_json::from_str(&json_data).expect("Failed to deserialize item names from JSON")
    }

    pub(crate) fn write_new_debug_visualization_metadata(
        &self,
        slug: FunctionSlug,
        new_metadata: &FunctionMetadata,
    ) {
        let mut functions_map = self.read_functions_json();
        functions_map.insert(slug, new_metadata.clone());
        self.write_functions_json(&functions_map);
    }
}
