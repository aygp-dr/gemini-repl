#!/bin/sh
#!/bin/sh
# Run directly with Lumo (if installed)
if command -v lumo >/dev/null 2>&1; then
    lumo src/gemini_repl/core.cljs
else
    echo "Lumo not installed. Install with: npm install -g lumo-cljs"
    exit 1
fi
