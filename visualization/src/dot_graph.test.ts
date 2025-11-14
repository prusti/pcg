import { openDotGraphInNewWindow } from './dot_graph';
import { Api } from './api';
import * as Viz from '@viz-js/viz';

jest.mock('@viz-js/viz');

describe('openDotGraphInNewWindow', () => {
  let mockApi: jest.Mocked<Api>;
  let mockVizInstance: any;
  let mockPopup: any;
  let originalWindowOpen: typeof window.open;

  beforeEach(() => {
    mockApi = {
      fetchDotFile: jest.fn()
        .mockResolvedValueOnce('digraph { a -> b; }')
        .mockRejectedValue(new Error('JSON file not found')),
    } as any;

    mockVizInstance = {
      renderSVGElement: jest.fn().mockReturnValue(document.createElementNS('http://www.w3.org/2000/svg', 'svg')),
    };

    (Viz.instance as jest.Mock).mockResolvedValue(mockVizInstance);

    mockPopup = {
      document: {
        head: { innerHTML: '' },
        body: { appendChild: jest.fn() },
        querySelectorAll: jest.fn().mockReturnValue([]),
      },
    };

    originalWindowOpen = window.open;
    window.open = jest.fn().mockReturnValue(mockPopup);
  });

  afterEach(() => {
    window.open = originalWindowOpen;
    jest.clearAllMocks();
  });

  it('should use the provided api to fetch dot file', async () => {
    const filename = 'test.dot';

    await openDotGraphInNewWindow(mockApi, filename);

    expect(mockApi.fetchDotFile).toHaveBeenCalledWith(filename);
    expect(mockApi.fetchDotFile).toHaveBeenCalledWith('test.json');
  });

  it('should open a new window with the rendered SVG', async () => {
    const filename = 'test.dot';

    await openDotGraphInNewWindow(mockApi, filename);

    await new Promise(resolve => setTimeout(resolve, 0));

    expect(window.open).toHaveBeenCalledWith(
      '',
      `Dot Graph - ${filename}`,
      'width=800,height=600'
    );
    expect(mockPopup.document.body.appendChild).toHaveBeenCalled();
  });

  it('should handle blocked popup gracefully', async () => {
    const consoleErrorSpy = jest.spyOn(console, 'error').mockImplementation();
    window.open = jest.fn().mockReturnValue(null);

    const filename = 'test.dot';

    await openDotGraphInNewWindow(mockApi, filename);

    await new Promise(resolve => setTimeout(resolve, 0));

    expect(consoleErrorSpy).toHaveBeenCalledWith('Failed to open popup window');
    expect(mockPopup.document.body.appendChild).not.toHaveBeenCalled();

    consoleErrorSpy.mockRestore();
  });

  it('should use correct api instance when different apis are provided', async () => {
    const mockApi1: jest.Mocked<Api> = {
      fetchDotFile: jest.fn()
        .mockResolvedValueOnce('digraph { x -> y; }')
        .mockRejectedValue(new Error('JSON file not found')),
    } as any;

    const mockApi2: jest.Mocked<Api> = {
      fetchDotFile: jest.fn()
        .mockResolvedValueOnce('digraph { a -> b; }')
        .mockRejectedValue(new Error('JSON file not found')),
    } as any;

    await openDotGraphInNewWindow(mockApi1, 'file1.dot');
    expect(mockApi1.fetchDotFile).toHaveBeenCalledWith('file1.dot');
    expect(mockApi2.fetchDotFile).not.toHaveBeenCalled();

    await openDotGraphInNewWindow(mockApi2, 'file2.dot');
    expect(mockApi2.fetchDotFile).toHaveBeenCalledWith('file2.dot');
  });
});

