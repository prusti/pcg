const path = require('path');

module.exports = {
  entry: './src/editor.ts',
  module: {
    rules: [
      {
        test: /\.tsx?$/,
        use: 'ts-loader',
        exclude: /node_modules/,
      },
    ],
  },
  resolve: {
    extensions: ['.tsx', '.ts', '.js'],
  },
  output: {
    filename: 'editor.bundle.js',
    path: path.resolve(__dirname, 'static'),
  },
  mode: 'production',
  devtool: 'source-map',
};



