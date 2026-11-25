# uml-layout

Auto-layout ("tidy") engine for UML class diagrams, with a Node renderer that exports SVG/PNG.

## Usage

```
npm install
node render.js specs/library.json out/library.png [layout/tidy-final.js]
```

- `engine.js` – diagram model, default tidy, SVG export, metrics
- `layout/` – alternative tidy implementations
- `specs/` – example diagrams (JSON)
- `out/` – sample renders
