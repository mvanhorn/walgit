import { api, type SetupRecipes } from "../api";
import { useData } from "../data";
import { CodeSample, CopyButton } from "./CopyButton";

/**
 * Clone/setup recipes for this host, rendered by the server at
 * `/services/setup.json` (crates/walgit-server/src/setup.rs — the same strings
 * go into /services/public/install.sh, the overview JSON and git's auth error text).
 * The UI is a client of those recipes, never a fork: where tokens come from and
 * what the installer does are the server's to define.
 *
 * Only `/services/public/*` (the installer) is reachable without a credential;
 * everything else needs a signed-in browser or a bearer token.
 */
export function useRecipes(repo?: string): SetupRecipes {
  return useData(`setup:${repo ?? ""}`, () => api.setupRecipes(repo), Infinity);
}

/** Shared by the Clone dropdown (compact) and the WAL page. `repo` = owner/name. */
export function CloneSetup({ repo, compact = false }: { repo: string; compact?: boolean }) {
  const r = useRecipes(repo);
  const url = `${r.base_url}/${repo}.git`;
  return (
    <div className="clone-setup">
      <div className="small strong">Run once per machine, then git just works</div>
      <div className="small muted">
        Asks for an access token once
        {r.token_url && (
          <>
            {" "}
            (create one at{" "}
            <a href={r.token_url} target="_blank" rel="noreferrer">
              {r.token_url.replace(/^https?:\/\//, "")}
            </a>
            )
          </>
        )}
        , stores it in a file only you can read, installs a git credential helper that hands it to git, and clones. Idempotent: re-run any time. Needs git ≥ 2.46 and curl.
      </div>
      <CodeSample code={r.install} />
      <div className="small strong">Already set up</div>
      <CodeSample code={r.plain_clone} />
      <div className="small strong">CI — no helper, the token from the environment</div>
      <CodeSample code={r.manual_clone} />
      <div className="clone-actions">
        <CopyButton text={() => api.installScript(repo)} label="Copy installer script" />
        <a className="btn btn-small" href={`/services/public/install.sh?repo=${repo}`} download="install.sh">
          Download install.sh
        </a>
      </div>
      {!compact && (
        <p className="small muted">
          The credential helper authenticates clones, fetches and pushes. When the server rejects the
          token (a real 401) git erases it from the helper, which tells you where to get a new one.
        </p>
      )}
      {!compact && (
        <>
          <p className="small muted">
            <strong>Blobless clone</strong> (full history, blobs on demand): keep <code>--sparse</code>: a full checkout
            would ask for every blob of HEAD's tree at once (minutes of server time); add areas with{" "}
            <code>git sparse-checkout add</code>.
          </p>
          <CodeSample code={r.blobless_clone} />
          <p className="small muted">
            <strong>CI / shallow clones</strong>: use <code>--depth=1 --single-branch</code>
            when the job only needs the current branch tip.
          </p>
        </>
      )}
      <div className="small muted">Clone URL</div>
      <CodeSample code={url} />
    </div>
  );
}
