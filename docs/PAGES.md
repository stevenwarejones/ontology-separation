# Online examples

The expected URL is https://stevenwarejones.github.io/ontology-separation/.
The workflow publishes only after a push to `main` passes Lean verification,
snapshot regeneration checks and Python compatibility checks. PR branches do not
deploy. The site contains public, already-committed HTML examples; each page links
to its exact source revision. Markdown and Lean links point to that revision on
GitHub, so publishing only HTML does not break the documentation links.

## One-time repository setup

In Settings → Pages → Build and deployment, select **GitHub Actions** as Source.
Then merge the PR. The `Verify` workflow's `pages` job publishes the site after
its verification jobs succeed. If Pages has not been enabled, the deployment job
can fail while proof checks remain green; enable it and rerun the failed job.
The connector used to prepare this PR does not expose Pages administration.

See GitHub's [custom workflow documentation](https://docs.github.com/en/pages/getting-started-with-github-pages/using-custom-workflows-with-github-pages).

## Local preview of staging

```sh
python scripts/build_pages.py /tmp/ontology-pages
python -m http.server --directory /tmp/ontology-pages 8000
```

Open http://localhost:8000. Use a fresh output directory each time. Staging does
not rebuild proofs; the deployment workflow stages only after verification.
