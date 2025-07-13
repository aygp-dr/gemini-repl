#!/bin/sh
#!/bin/sh
if [ ! -f ".env" ]; then
    echo "Error: .env file not found"
    echo "Copy .env.example to .env and add your API key"
    exit 1
fi

if [ -f "target/repl.js" ]; then
    node target/repl.js
else
    echo "Building first..."
    npx shadow-cljs compile repl
    node target/repl.js
fi
