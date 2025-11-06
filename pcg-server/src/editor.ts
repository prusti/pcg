import { EditorView, basicSetup } from 'codemirror';
import { rust } from '@codemirror/lang-rust';
import { vim } from '@replit/codemirror-vim';
import { keymap } from '@codemirror/view';
import { indentWithTab } from '@codemirror/commands';
import { Compartment } from '@codemirror/state';

interface VimModeChangeEvent extends CustomEvent {
    detail: {
        mode: 'normal' | 'insert' | 'visual';
    };
}

let editorInstance: EditorView | null = null;
let vimCompartment: Compartment | null = null;
let vimEnabled = false;

const VIM_MODE_STORAGE_KEY = 'pcg-server-vim-mode';

function getVimModePreference(): boolean {
    const stored = localStorage.getItem(VIM_MODE_STORAGE_KEY);
    return stored === 'true';
}

function setVimModePreference(enabled: boolean): void {
    localStorage.setItem(VIM_MODE_STORAGE_KEY, enabled.toString());
}

async function initializeCodeEditor(): Promise<void> {
    if (editorInstance) {
        return;
    }

    try {
        const textarea = document.querySelector('textarea[name="code"]') as HTMLTextAreaElement;
        if (!textarea) {
            console.error('Textarea not found');
            return;
        }

        const container = textarea.parentElement;
        if (!container) {
            console.error('Container not found');
            return;
        }

        const editorWrapper = document.createElement('div');
        editorWrapper.id = 'code-editor-wrapper';
        editorWrapper.style.cssText = `
            border: 1px solid #d1d5db;
            border-radius: 4px;
            overflow: hidden;
            background-color: #ffffff;
        `;

        const toolbar = document.createElement('div');
        toolbar.id = 'editor-toolbar';
        toolbar.style.cssText = `
            padding: 8px 10px;
            background-color: #f3f4f6;
            border-bottom: 1px solid #d1d5db;
            display: flex;
            align-items: center;
            gap: 10px;
        `;

        const vimToggleLabel = document.createElement('label');
        vimToggleLabel.style.cssText = `
            display: flex;
            align-items: center;
            gap: 6px;
            font-family: Arial, sans-serif;
            font-size: 14px;
            color: #374151;
            cursor: pointer;
        `;

        const vimToggleCheckbox = document.createElement('input');
        vimToggleCheckbox.type = 'checkbox';
        vimToggleCheckbox.id = 'vim-toggle';
        vimToggleCheckbox.checked = getVimModePreference();
        vimToggleCheckbox.style.cursor = 'pointer';

        const vimToggleText = document.createElement('span');
        vimToggleText.textContent = 'Vim Mode';

        vimToggleLabel.appendChild(vimToggleCheckbox);
        vimToggleLabel.appendChild(vimToggleText);

        const vimStatus = document.createElement('span');
        vimStatus.id = 'vim-status';
        vimStatus.style.cssText = `
            padding: 4px 8px;
            background-color: #e5e7eb;
            color: #6b7280;
            font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
            font-size: 12px;
            border-radius: 3px;
            display: none;
        `;
        vimStatus.textContent = '-- NORMAL --';

        toolbar.appendChild(vimToggleLabel);
        toolbar.appendChild(vimStatus);

        const editorDiv = document.createElement('div');
        editorDiv.id = 'code-editor';
        editorDiv.style.cssText = `
            min-height: 400px;
            height: 600px;
            max-height: 90vh;
            overflow: auto;
        `;

        editorWrapper.appendChild(toolbar);
        editorWrapper.appendChild(editorDiv);

        textarea.style.display = 'none';
        container.insertBefore(editorWrapper, textarea);

        vimCompartment = new Compartment();

        const editor = new EditorView({
            doc: textarea.value || '',
            extensions: [
                basicSetup,
                rust(),
                keymap.of([indentWithTab]),
                vimCompartment.of([]),
                EditorView.lineWrapping,
                EditorView.updateListener.of((update) => {
                    if (update.docChanged) {
                        textarea.value = editor.state.doc.toString();
                    }
                })
            ],
            parent: editorDiv
        });

        function toggleVimMode(enabled: boolean): void {
            if (!vimCompartment || !editorInstance) return;

            vimEnabled = enabled;
            setVimModePreference(enabled);
            if (enabled) {
                editorInstance.dispatch({
                    effects: vimCompartment.reconfigure(vim())
                });
                vimStatus.style.display = 'none';
            } else {
                editorInstance.dispatch({
                    effects: vimCompartment.reconfigure([])
                });
                vimStatus.style.display = 'none';
            }
            editorInstance.focus();
        }

        vimToggleCheckbox.addEventListener('change', (e) => {
            toggleVimMode((e.target as HTMLInputElement).checked);
        });

        window.addEventListener('vim-mode-change', ((e: VimModeChangeEvent) => {
            if (!vimEnabled) return;

            const mode = e.detail.mode;
            if (mode === 'normal') {
                vimStatus.style.display = 'none';
            } else if (mode === 'insert') {
                vimStatus.textContent = '-- INSERT --';
                vimStatus.style.display = 'inline-block';
                vimStatus.style.backgroundColor = '#dbeafe';
                vimStatus.style.color = '#1e40af';
            } else if (mode === 'visual') {
                vimStatus.textContent = '-- VISUAL --';
                vimStatus.style.display = 'inline-block';
                vimStatus.style.backgroundColor = '#fef3c7';
                vimStatus.style.color = '#92400e';
            }
        }) as EventListener);

        editorInstance = editor;
        (window as any).rustEditor = editor;

        if (vimToggleCheckbox.checked) {
            toggleVimMode(true);
        } else {
            editor.focus();
        }

        console.log('CodeMirror editor initialized with Rust syntax highlighting and Vim mode');
    } catch (error) {
        console.error('Failed to initialize CodeMirror editor:', error);
        const textarea = document.querySelector('textarea[name="code"]') as HTMLTextAreaElement;
        if (textarea) {
            textarea.style.display = 'block';
        }
    }
}

function checkAndInitialize(): void {
    const codeInput = document.getElementById('code-input');
    const useCodeRadio = document.getElementById('use-code') as HTMLInputElement;

    if (useCodeRadio?.checked && codeInput && codeInput.style.display !== 'none') {
        initializeCodeEditor();
    }
}

const originalToggle = (window as any).toggleInputMethod;
(window as any).toggleInputMethod = function(): void {
    if (originalToggle) {
        originalToggle();
    }

    const useCodeRadio = document.getElementById('use-code') as HTMLInputElement;
    if (useCodeRadio?.checked) {
        setTimeout(() => initializeCodeEditor(), 0);
    }
};

if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', () => {
        setTimeout(checkAndInitialize, 100);
    });
} else {
    setTimeout(checkAndInitialize, 100);
}

