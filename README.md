# UML Class Diagram editor

A single-page, in-browser UML class diagram editor with automatic tidy layout. No build, no server: open `index.html`.

- Drag a blue port onto another box to connect; click a visibility symbol to cycle it; double-click text to edit
- **Tidy** lays boxes out by inheritance/composition rules and routes lines to avoid crossings
- Export PNG / SVG / JSON, import JSON; the diagram autosaves in your browser

Live site: https://min9904.github.io/uml-layout/

## Dev tooling
`engine.js`, `page-tidy.js`, `layout/`, `render.js`, `specs/`: Node harness used to benchmark layout variants (`npm install; node render.js specs/library.json out/x.png`).
