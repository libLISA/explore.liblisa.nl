#! /bin/bash

(cd liblisa-wasm && wasm-pack build --target web) && \
(cd site && npm run build) && \
(cd site && npx wrangler pages deploy --project-name liblisa-web dist/)