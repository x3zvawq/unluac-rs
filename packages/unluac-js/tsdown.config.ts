import { spawn } from "node:child_process";
import { copyFile, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { dirname, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { defineConfig } from "tsdown";

const packageDir = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(packageDir, "..", "..");
const wasmCrateDir = resolve(repoRoot, "packages", "unluac-wasm");
const wasmBuildDir = resolve(packageDir, ".wasm-build");
const distDir = resolve(packageDir, "dist");
let wasmBuildPromise: Promise<void> | null = null;

export default defineConfig({
  entry: ["src/index.ts"],
  format: ["esm", "cjs"],
  dts: true,
  outDir: "dist",
  target: "es2022",
  hooks: {
    "build:prepare": async () => {
      if (!wasmBuildPromise) {
        wasmBuildPromise = buildWasmArtifacts();
      }
      await wasmBuildPromise;
    },
    "build:done": async () => {
      await mkdir(distDir, { recursive: true });
      for (const fileName of [
        "unluac_wasm.js",
        "unluac_wasm.d.ts",
        "unluac_wasm_bg.wasm",
        "unluac_wasm_bg.wasm.d.ts",
      ]) {
        await copyFile(resolve(wasmBuildDir, fileName), resolve(distDir, fileName));
      }
      await copyFile(resolve(packageDir, "README.md"), resolve(distDir, "README.md"));
      await copyFile(resolve(repoRoot, "LICENSE.txt"), resolve(distDir, "LICENSE.txt"));
      await writeFile(
        resolve(distDir, "package.json"),
        `${JSON.stringify(await buildPublishPackageJson(), null, 2)}\n`
      );
    },
  },
});

async function buildWasmArtifacts(): Promise<void> {
  await rm(wasmBuildDir, { recursive: true, force: true });
  await runCommand(
    "wasm-pack",
    [
      "build",
      wasmCrateDir,
      "--target",
      "web",
      "--out-dir",
      relative(wasmCrateDir, wasmBuildDir),
      "--out-name",
      "unluac_wasm",
      "--release",
    ],
    wasmCrateDir,
    {
      CARGO_PROFILE_RELEASE_CODEGEN_UNITS: "1",
      CARGO_PROFILE_RELEASE_LTO: "fat",
      CARGO_PROFILE_RELEASE_OPT_LEVEL: "z",
      CARGO_PROFILE_RELEASE_PANIC: "abort",
    }
  );
}

async function buildPublishPackageJson() {
  const sourcePackageJson = JSON.parse(
    await readFile(resolve(packageDir, "package.json"), "utf8")
  );

  return {
    name: sourcePackageJson.name,
    version: sourcePackageJson.version,
    description: sourcePackageJson.description,
    keywords: sourcePackageJson.keywords,
    license: sourcePackageJson.license,
    repository: sourcePackageJson.repository,
    type: "module",
    sideEffects: sourcePackageJson.sideEffects,
    engines: sourcePackageJson.engines,
    files: [
      "README.md",
      "LICENSE.txt",
      "index.cjs",
      "index.mjs",
      "index.d.cts",
      "index.d.mts",
      "unluac_wasm.js",
      "unluac_wasm.d.ts",
      "unluac_wasm_bg.wasm",
      "unluac_wasm_bg.wasm.d.ts",
    ],
    main: "./index.cjs",
    module: "./index.mjs",
    types: "./index.d.mts",
    exports: {
      ".": {
        types: "./index.d.mts",
        import: "./index.mjs",
        require: "./index.cjs",
        default: "./index.mjs",
      },
    },
  };
}

async function runCommand(
  command: string,
  args: string[],
  cwd: string,
  extraEnv: Record<string, string> = {}
): Promise<void> {
  await new Promise<void>((resolvePromise, rejectPromise) => {
    const child = spawn(command, args, {
      cwd,
      env: {
        ...process.env,
        ...extraEnv,
      },
      stdio: "inherit",
    });

    const formattedCommand = [command, ...args].join(" ");

    child.on("error", (error) => {
      rejectPromise(
        new Error(
          `failed to start ${formattedCommand} in ${cwd}: ${error.message}`
        )
      );
    });
    child.on("close", (code, signal) => {
      if (signal) {
        rejectPromise(
          new Error(
            `${formattedCommand} was terminated by signal ${signal} (cwd: ${cwd})`
          )
        );
      } else if (code !== 0) {
        rejectPromise(
          new Error(
            `${formattedCommand} exited with code ${code ?? "unknown"} (cwd: ${cwd})`
          )
        );
      } else {
        resolvePromise();
      }
    });
  });
}
