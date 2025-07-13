# CLAUDE.md - Project Generation Notes

## Project Guidelines
- Use conventional commits
- Use --trailer for co-author attribution
- Don't use 'generated with' in the body of commit messages
- At each step / commit / task commit the work and make a note of any prompts used in git notes

## Generation Context

This Gemini REPL project was generated through a series of prompts to create a formally-specified, self-hosting REPL for the Google Gemini API.

### Initial Vision
- "i want to have a simple, simple console app in clojurescript that just makes calls to curl [Gemini API endpoint] but in a repl-ish format"
- "the exit and help commands should use a slash structure"
- "i want to start by using formal methods to describe the interfaces or expectations of the system"

### Key Files Generated

#### SETUP.org (now removed after tangling)
- Created the initial project structure
- Defined formal specifications (TLA+ and Alloy)
- Generated directories: specs/, src/, tests/, docs/
- Included comprehensive requirements document
- Created with prompt: "show a SETUP.org that just builds out those initial files"

#### SPECS-SETUP.org
- Formal methods tooling setup for FreeBSD
- TLA+ and Alloy installation and configuration
- Created after user asked: "what tools do i need to use tla and alloy on freebsd"
- Final prompt: "create SPECS-TOOLING.org" (renamed to SPECS-SETUP.org)

#### NODE-SETUP.org
- ClojureScript development environment
- Shadow-CLJS configuration
- Complete REPL implementation
- Created proactively after seeing Node.js installation

#### GITHUB-SETUP.org
- GitHub Actions workflows
- Issue and PR templates
- RFC structure
- Created with minimal prompt: "show GITHUB-SETUP.org"

#### SHARED-SETUP.org
- Claude command system
- Project management directories
- Adapted from defrecord/shared-infrastructure examples
- Prompt: "i want a SHARED-SETUP.org that creates directories for change-requests/ experiments/ and research/"

### Project Evolution
1. Started with simple REPL concept
2. Added formal specifications requirement
3. Evolved to include self-hosting capabilities
4. Integrated comprehensive tooling and workflows
5. Created literate programming documentation

### Self-Hosting Vision
The project is designed to eventually read, analyze, and modify its own code, with formal specifications serving as safety constraints.