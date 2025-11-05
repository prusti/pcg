# PCG Server Static Files

This directory contains static assets served by the pcg-server.

## editor.bundle.js

A bundled TypeScript application containing a CodeMirror 6-based code editor with the following features:

- **Rust Syntax Highlighting**: Full syntax highlighting for Rust code using `@codemirror/lang-rust`
- **Vim Keybindings**: Complete vim emulation using `@replit/codemirror-vim`
- **Dark Theme**: One Dark theme from `@codemirror/theme-one-dark`
- **Mode Indicator**: Visual indicator showing current vim mode (NORMAL, INSERT, VISUAL)

### Features

1. **Vim Mode**: The editor starts in NORMAL mode. Use standard vim keybindings:
   - `i` to enter INSERT mode
   - `ESC` to return to NORMAL mode
   - `v` for VISUAL mode
   - All standard vim navigation and editing commands

2. **Syntax Highlighting**: Rust code is automatically highlighted with proper syntax coloring

3. **Line Wrapping**: Long lines wrap automatically for better readability

4. **Form Integration**: The editor content is automatically synced to the hidden textarea for form submission

### Building

The editor is written in TypeScript and bundled using webpack:

```bash
# Install dependencies
npm install

# Build for production
npm run build

# Watch mode for development
npm run dev
```

### Dependencies

All dependencies are bundled into `editor.bundle.js`:
- CodeMirror 6 core
- Rust language support (`@codemirror/lang-rust`)
- Vim keybindings (`@replit/codemirror-vim`)
- One Dark theme (`@codemirror/theme-one-dark`)

### Source Code

The TypeScript source is located at `src/editor.ts`.

### Browser Compatibility

The bundled JavaScript is compatible with modern browsers (ES2020+).

