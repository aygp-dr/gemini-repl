#!/bin/sh
#!/bin/sh
echo "Building optimized version..."
npx shadow-cljs release repl
echo "Build complete: dist/gemini-repl.js"
ls -lh dist/
