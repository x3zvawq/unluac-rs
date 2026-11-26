import { readFile, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { resolve } from "node:path";
import process from "node:process";

const repoRoot = resolve(fileURLToPath(new URL("../..", import.meta.url)));
const checkOnly = process.argv.includes("--check");
const printVersion = process.argv.includes("--print-version");

const rootManifestPath = resolve(repoRoot, "Cargo.toml");
const targetFiles = [
  { kind: "cargo", path: "xtask/Cargo.toml" },
  { kind: "cargo", path: "packages/unluac-cli/Cargo.toml" },
  { kind: "cargo", path: "packages/unluac-test-support/Cargo.toml" },
  { kind: "cargo", path: "packages/unluac-wasm/Cargo.toml" },
  { kind: "json", path: "packages/unluac-js/package.json" },
  { kind: "package-lock", path: "packages/unluac-js/package-lock.json" },
  { kind: "json", path: "packages/unluac-web/package.json" },
  { kind: "package-lock", path: "packages/unluac-web/package-lock.json" },
];

const rootManifest = await readFile(rootManifestPath, "utf8");
const rootVersion = extractCargoPackageVersion(rootManifest, rootManifestPath);

if (printVersion) {
  process.stdout.write(rootVersion);
  process.exit(0);
}

const mismatches = [];

for (const target of targetFiles) {
  const absolutePath = resolve(repoRoot, target.path);
  if (target.kind === "cargo") {
    const manifest = await readFile(absolutePath, "utf8");
    const currentVersion = extractCargoPackageVersion(manifest, target.path);
    if (currentVersion !== rootVersion) {
      mismatches.push(`${target.path}: ${currentVersion} -> ${rootVersion}`);
      if (!checkOnly) {
        const updated = replaceCargoPackageVersion(manifest, rootVersion, target.path);
        await writeFile(absolutePath, updated);
      }
    }
    continue;
  }

  const packageJsonRaw = await readFile(absolutePath, "utf8");
  const packageJson = JSON.parse(packageJsonRaw);
  const currentVersion =
    target.kind === "package-lock" ? extractPackageLockVersion(packageJson, target.path) : packageJson.version;
  if (currentVersion !== rootVersion) {
    mismatches.push(`${target.path}: ${currentVersion} -> ${rootVersion}`);
    if (!checkOnly) {
      if (target.kind === "package-lock") {
        setPackageLockVersion(packageJson, rootVersion);
      } else {
        packageJson.version = rootVersion;
      }
      await writeFile(absolutePath, `${JSON.stringify(packageJson, null, 2)}\n`);
    }
  }
}

if (mismatches.length === 0) {
  process.stdout.write(
    checkOnly
      ? `version sync check passed (${rootVersion})\n`
      : `all package versions already match ${rootVersion}\n`
  );
  process.exit(0);
}

if (checkOnly) {
  process.stderr.write(
    [
      `version sync check failed: root Cargo.toml is ${rootVersion}`,
      ...mismatches.map((entry) => `  - ${entry}`),
      "run `node .github/scripts/sync_versions.mjs` to update them",
      "",
    ].join("\n")
  );
  process.exit(1);
}

process.stdout.write(
  [
    `synced package versions to ${rootVersion}:`,
    ...mismatches.map((entry) => `  - ${entry}`),
    "",
  ].join("\n")
);

function extractCargoPackageVersion(content, label) {
  const packageBlockMatch = content.match(/^\[package\]\n([\s\S]*?)(?=^\[|\Z)/m);
  if (!packageBlockMatch) {
    throw new Error(`failed to find [package] section in ${label}`);
  }

  const versionMatch = packageBlockMatch[1].match(/^version = "([^"]+)"$/m);
  if (!versionMatch) {
    throw new Error(`failed to find package version in ${label}`);
  }

  return versionMatch[1];
}

function replaceCargoPackageVersion(content, nextVersion, label) {
  const updated = content.replace(
    /^(\[package\]\n[\s\S]*?^version = ")([^"]+)(")$/m,
    `$1${nextVersion}$3`
  );

  if (updated === content) {
    throw new Error(`failed to update package version in ${label}`);
  }

  return updated;
}

function extractPackageLockVersion(packageLock, label) {
  const rootPackageVersion = packageLock?.packages?.[""]?.version;
  if (typeof packageLock.version !== "string" || typeof rootPackageVersion !== "string") {
    throw new Error(`failed to find package-lock version fields in ${label}`);
  }
  if (packageLock.version !== rootPackageVersion) {
    throw new Error(
      `package-lock top-level version ${packageLock.version} does not match root package version ${rootPackageVersion} in ${label}`
    );
  }
  return packageLock.version;
}

function setPackageLockVersion(packageLock, nextVersion) {
  packageLock.version = nextVersion;
  if (packageLock.packages?.[""]) {
    packageLock.packages[""].version = nextVersion;
  }
}
