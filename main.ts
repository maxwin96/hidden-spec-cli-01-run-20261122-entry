// mend: one patch tool for every AI edit format.
// Applies unified diffs, SEARCH/REPLACE blocks, V4A patches and JSON edits
// to a tree of text files. Node 22, standard library only.

import { mkdirSync, readdirSync, readFileSync, unlinkSync, writeFileSync, writeSync } from "node:fs";
import { dirname, join } from "node:path";

// ---------------------------------------------------------------------------
// Small shared helpers
// ---------------------------------------------------------------------------

class ParseFault extends Error {
  line: number;
  constructor(line: number) {
    super(`parse ${line}`);
    this.line = line;
  }
}

function failParse(line: number): never {
  throw new ParseFault(line);
}

/** A patch's lines: split at \n, one trailing \r removed, no empty piece after a final \n. */
function splitPatchLines(text: string): string[] {
  const parts = text.split("\n").map((l) => (l.endsWith("\r") ? l.slice(0, -1) : l));
  if (text.endsWith("\n")) parts.pop();
  return parts;
}

function isBlank(line: string): boolean {
  return line.trim() === "";
}

function trimRightWs(line: string): string {
  return line.replace(/[ \t]+$/, "");
}

function leadingWs(line: string): string {
  const m = /^[ \t]*/.exec(line);
  return m ? m[0] : "";
}

function isSafePath(p: string): boolean {
  if (p === "") return false;
  if (p.startsWith("/")) return false;
  if (p.includes("\\")) return false;
  for (const seg of p.split("/")) {
    if (seg === "" || seg === "." || seg === "..") return false;
  }
  return true;
}

// A file's lines, its line break, and whether it ends with one.
interface FileView {
  lines: string[];
  br: string;
  ends: boolean;
}

function parseFileText(text: string): FileView {
  if (text === "") return { lines: [], br: "\n", ends: false };
  const firstLf = text.indexOf("\n");
  const br = firstLf > 0 && text[firstLf - 1] === "\r" ? "\r\n" : "\n";
  const parts = text.split(br);
  const ends = text.endsWith(br);
  if (ends) parts.pop();
  return { lines: parts, br, ends };
}

function serializeFile(lines: string[], br: string, ends: boolean): string {
  if (lines.length === 0) return "";
  return lines.join(br) + (ends ? br : "");
}

// ---------------------------------------------------------------------------
// Line matching (SPEC section 5)
// ---------------------------------------------------------------------------

function lineKey(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return trimRightWs(line);
  return line.replace(/^[ \t]+/, "").replace(/[ \t]+$/, "");
}

function findOccurrences(fileLines: string[], oldLines: string[], tier: number): number[] {
  const want = oldLines.map((l) => lineKey(l, tier));
  const have = fileLines.map((l) => lineKey(l, tier));
  const out: number[] = [];
  for (let i = 0; i + oldLines.length <= fileLines.length; i += 1) {
    let ok = true;
    for (let j = 0; j < oldLines.length; j += 1) {
      if (have[i + j] !== want[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

interface TierHit {
  tier: number;
  positions: number[];
}

/** First tier (0, then 1, then 2; strict means 0 only) at which O occurs at least once. */
function findTier(fileLines: string[], oldLines: string[], strict: boolean): TierHit | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const positions = findOccurrences(fileLines, oldLines, t);
    if (positions.length > 0) return { tier: t, positions };
  }
  return null;
}

function matchSingle(fileLine: string, anchor: string, tier: number): boolean {
  return lineKey(fileLine, tier) === lineKey(anchor, tier);
}

/** Re-indent one added line at tier 2 (SPEC section 5). */
function reindent(line: string, f: string, p: string): string {
  if (line === "" || /^[ \t]+$/.test(line)) return line;
  if (line.startsWith(p)) return f + line.slice(p.length);
  return line;
}

// One line of the new text: either a context line (written as the file's own
// matched line) or an added line.
interface NewLine {
  text: string;
  ctx: boolean;
  oIdx: number;
}

function resolveNewLines(nItems: NewLine[], fileLines: string[], pos: number, tier: number, oldLines: string[]): string[] {
  if (tier !== 2) {
    return nItems.map((n) => (n.ctx ? fileLines[pos + n.oIdx] : n.text));
  }
  const f = leadingWs(fileLines[pos]);
  const p = leadingWs(oldLines[0]);
  return nItems.map((n) => (n.ctx ? fileLines[pos + n.oIdx] : reindent(n.text, f, p)));
}

// A body line of a unified hunk or a V4A chunk.
interface BodyItem {
  kind: "ctx" | "old" | "new" | "mark";
  text: string;
}

function buildOldNew(items: BodyItem[]): { oldLines: string[]; newLines: NewLine[] } {
  const oldLines: string[] = [];
  const newLines: NewLine[] = [];
  for (const it of items) {
    if (it.kind === "ctx") {
      oldLines.push(it.text);
      newLines.push({ text: it.text, ctx: true, oIdx: oldLines.length - 1 });
    } else if (it.kind === "old") {
      oldLines.push(it.text);
    } else if (it.kind === "new") {
      newLines.push({ text: it.text, ctx: false, oIdx: -1 });
    }
  }
  return { oldLines, newLines };
}

/** True when a `\` line directly follows the last context or `+` body line. */
function backslashAfterLastNew(items: BodyItem[]): boolean {
  let last = -1;
  for (let k = 0; k < items.length; k += 1) {
    if (items[k].kind === "ctx" || items[k].kind === "new") last = k;
  }
  if (last === -1) return false;
  return items[last + 1] !== undefined && items[last + 1].kind === "mark";
}

/** True when a `\` line directly follows the last `+` body line. */
function backslashAfterLastPlus(items: BodyItem[]): boolean {
  let last = -1;
  for (let k = 0; k < items.length; k += 1) {
    if (items[k].kind === "new") last = k;
  }
  if (last === -1) return false;
  return items[last + 1] !== undefined && items[last + 1].kind === "mark";
}

// ---------------------------------------------------------------------------
// Edits
// ---------------------------------------------------------------------------

type Edit =
  | { kind: "u-create"; path: string; hunks: Hunk[] }
  | { kind: "u-delete"; path: string }
  | { kind: "u-move"; oldPath: string; newPath: string; hunks: Hunk[] }
  | { kind: "u-change"; path: string; hunks: Hunk[] }
  | { kind: "sr"; path: string; oldLines: string[]; newLines: string[] }
  | { kind: "v-add"; path: string; lines: string[] }
  | { kind: "v-delete"; path: string }
  | { kind: "v-update"; path: string; moveTo: string | null; chunks: VChunk[] }
  | { kind: "j-create"; path: string; text: string }
  | { kind: "j-str"; path: string; oldStr: string; newStr: string }
  | { kind: "j-insert"; path: string; insertLine: number; newStr: string };

interface Hunk {
  a: number;
  items: BodyItem[];
}

interface VChunk {
  anchor: string | null;
  eof: boolean;
  items: BodyItem[];
}

interface EditFailure {
  code: string;
  path: string;
}

type Tree = Map<string, string>;

function fail(code: string, path: string): EditFailure {
  return { code, path };
}

// ---------------------------------------------------------------------------
// Invocation (SPEC section 1) and format detection (SPEC section 4)
// ---------------------------------------------------------------------------

interface Args {
  format: string;
  check: boolean;
  strict: boolean;
  patch: string | null;
}

function parseArgs(argv: string[]): Args | null {
  let format = "auto";
  let check = false;
  let strict = false;
  const seen = new Set<string>();
  const positionals: string[] = [];
  let endOpts = false;
  for (const arg of argv) {
    if (!endOpts && arg === "--") {
      endOpts = true;
      continue;
    }
    if (!endOpts && arg.startsWith("-") && arg !== "-") {
      if (arg === "--check") {
        if (seen.has("check")) return null;
        seen.add("check");
        check = true;
      } else if (arg === "--strict") {
        if (seen.has("strict")) return null;
        seen.add("strict");
        strict = true;
      } else if (arg.startsWith("--format=")) {
        if (seen.has("format")) return null;
        seen.add("format");
        const value = arg.slice("--format=".length);
        if (value !== "unified" && value !== "search-replace" && value !== "v4a" && value !== "json" && value !== "auto") return null;
        format = value;
      } else {
        return null;
      }
    } else {
      positionals.push(arg);
    }
  }
  if (positionals.length > 1) return null;
  return { format, check, strict, patch: positionals.length === 1 ? positionals[0] : null };
}

function detectFormat(lines: string[]): string | null {
  const firstNb = lines.findIndex((l) => !isBlank(l));
  if (firstNb === -1) return null;
  if (lines[firstNb].trim() === "*** Begin Patch") return "v4a";
  const firstChar = lines[firstNb].trimStart().charAt(0);
  if (firstChar === "[" || firstChar === "{") return "json";
  for (const l of lines) {
    if (trimRightWs(l) === "<<<<<<< SEARCH") return "search-replace";
  }
  for (let i = 0; i < lines.length; i += 1) {
    if (lines[i].startsWith("diff --git ")) return "unified";
    if (lines[i].startsWith("--- ") && i + 1 < lines.length && lines[i + 1].startsWith("+++ ")) return "unified";
  }
  return null;
}

// ---------------------------------------------------------------------------
// Unified diffs (SPEC section 6)
// ---------------------------------------------------------------------------

interface USection {
  oldRaw: string | null;
  newRaw: string | null;
  renameFrom: string | null;
  renameTo: string | null;
  diffOld: string | null;
  diffNew: string | null;
  newFile: boolean;
  deletedFile: boolean;
  headerPair: boolean;
  hunks: Hunk[];
}

function newUSection(): USection {
  return {
    oldRaw: null,
    newRaw: null,
    renameFrom: null,
    renameTo: null,
    diffOld: null,
    diffNew: null,
    newFile: false,
    deletedFile: false,
    headerPair: false,
    hunks: [],
  };
}

/** The path after `--- `/`+++ `: up to the first tab, surrounding spaces removed. */
function headerPath(line: string): string {
  const rest = line.slice(4);
  const tab = rest.indexOf("\t");
  return (tab === -1 ? rest : rest.slice(0, tab)).trim();
}

/** A leading a/ or b/ is removed; /dev/null means no file. */
function stripHeaderPath(p: string): string | null {
  if (p === "/dev/null") return null;
  if (p.startsWith("a/") || p.startsWith("b/")) return p.slice(2);
  return p;
}

const DIFF_GIT_RE = /^diff --git a\/([^ \t]+) b\/([^ \t]+)[ \t]*$/;
const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(?: (.*)|)$/;

function isBodyLine(line: string): boolean {
  return line === "" || line.startsWith(" ") || line.startsWith("-") || line.startsWith("+") || line.startsWith("\\");
}

function bodyItemOf(line: string): BodyItem {
  if (line === "") return { kind: "ctx", text: "" };
  if (line.startsWith(" ")) return { kind: "ctx", text: line.slice(1) };
  if (line.startsWith("-")) return { kind: "old", text: line.slice(1) };
  if (line.startsWith("+")) return { kind: "new", text: line.slice(1) };
  return { kind: "mark", text: line.slice(1) };
}

function parseUnified(lines: string[]): Edit[] {
  const sections: USection[] = [];
  let cur: USection | null = null;
  let inHeader = false;
  let i = 0;
  while (i < lines.length) {
    const line = lines[i];
    if (line === "diff --git" || line.startsWith("diff --git ")) {
      const m = DIFF_GIT_RE.exec(line);
      if (m === null) failParse(i + 1);
      cur = newUSection();
      cur.diffOld = m[1];
      cur.diffNew = m[2];
      sections.push(cur);
      inHeader = true;
      i += 1;
      continue;
    }
    if (line.startsWith("--- ") && i + 1 < lines.length && lines[i + 1].startsWith("+++ ")) {
      if (cur !== null && inHeader && !cur.headerPair) {
        cur.oldRaw = stripHeaderPath(headerPath(line));
        cur.newRaw = stripHeaderPath(headerPath(lines[i + 1]));
        cur.headerPair = true;
      } else {
        cur = newUSection();
        cur.oldRaw = stripHeaderPath(headerPath(line));
        cur.newRaw = stripHeaderPath(headerPath(lines[i + 1]));
        cur.headerPair = true;
        sections.push(cur);
        inHeader = true;
      }
      i += 2;
      continue;
    }
    if (cur !== null && inHeader && line.startsWith("--- ")) {
      failParse(i + 2);
    }
    if (line.startsWith("@@")) {
      if (cur === null) failParse(i + 1);
      const m = HUNK_RE.exec(line);
      if (m === null) failParse(i + 1);
      const a = parseInt(m[1], 10);
      const items: BodyItem[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const bl = lines[j];
        if (bl.startsWith("diff --git")) break;
        if (bl.startsWith("--- ") && j + 1 < lines.length && lines[j + 1].startsWith("+++ ")) break;
        if (!isBodyLine(bl)) break;
        items.push(bodyItemOf(bl));
        j += 1;
      }
      while (items.length > 0) {
        const last = items[items.length - 1];
        if (last.kind === "ctx" && last.text === "") items.pop();
        else break;
      }
      cur.hunks.push({ a, items });
      inHeader = false;
      i = j;
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith("rename from ")) {
        cur.renameFrom = line.slice("rename from ".length).trim();
      } else if (line.startsWith("rename to ")) {
        cur.renameTo = line.slice("rename to ".length).trim();
      } else if (line.startsWith("new file mode")) {
        cur.newFile = true;
      } else if (line.startsWith("deleted file mode")) {
        cur.deletedFile = true;
      }
      i += 1;
      continue;
    }
    i += 1;
  }
  if (sections.length === 0) failParse(1);
  const edits: Edit[] = [];
  for (const s of sections) {
    let oldPath: string | null = null;
    let newPath: string | null = null;
    if (s.headerPair) {
      oldPath = s.oldRaw;
      newPath = s.newRaw;
    } else if (s.renameFrom !== null || s.renameTo !== null) {
      oldPath = s.renameFrom;
      newPath = s.renameTo;
    } else {
      oldPath = s.diffOld;
      newPath = s.diffNew;
    }
    // Creation and deletion are decided by the /dev/null marker or the mode
    // flags; a bare diff --git pair with equal paths is a change.
    if (s.newFile || (s.oldRaw === null && s.newRaw !== null && s.headerPair)) {
      edits.push({ kind: "u-create", path: newPath ?? oldPath ?? "", hunks: s.hunks });
    } else if (s.deletedFile || (s.newRaw === null && s.oldRaw !== null && s.headerPair)) {
      edits.push({ kind: "u-delete", path: oldPath ?? newPath ?? "" });
    } else if (oldPath !== null && newPath !== null && oldPath !== newPath) {
      edits.push({ kind: "u-move", oldPath, newPath, hunks: s.hunks });
    } else {
      edits.push({ kind: "u-change", path: oldPath ?? newPath ?? "", hunks: s.hunks });
    }
  }
  return edits;
}

// ---------------------------------------------------------------------------
// Applying unified hunks (SPEC section 6)
// ---------------------------------------------------------------------------

/** Apply one section's hunks to a file's lines; returns the new lines and
 *  final-break flag, or a failure. The file is not touched on failure. */
function applyHunks(
  view: FileView,
  hunks: Hunk[],
  strict: boolean,
  path: string,
): { lines: string[]; ends: boolean } | EditFailure {
  let lines = view.lines.slice();
  let ends = view.ends;
  let d = 0;
  for (const hunk of hunks) {
    const { oldLines, newLines } = buildOldNew(hunk.items);
    if (oldLines.length === 0) {
      const at = Math.min(hunk.a + d, lines.length);
      const wasAtEnd = at === lines.length;
      const inserted = newLines.map((n) => n.text);
      lines = lines.slice(0, at).concat(inserted).concat(lines.slice(at));
      if (inserted.length > 0 && wasAtEnd) {
        ends = !backslashAfterLastNew(hunk.items);
      }
      d += newLines.length;
      continue;
    }
    const hit = findTier(lines, oldLines, strict);
    if (hit === null) return fail("no-match", path);
    const target = hunk.a - 1 + d;
    let best = hit.positions[0];
    let bestDist = Math.abs(best - target);
    for (const pos of hit.positions) {
      const dist = Math.abs(pos - target);
      if (dist < bestDist) {
        best = pos;
        bestDist = dist;
      }
    }
    const resolved = resolveNewLines(newLines, lines, best, hit.tier, oldLines);
    const touchesEnd = best + oldLines.length === lines.length;
    lines = lines.slice(0, best).concat(resolved).concat(lines.slice(best + oldLines.length));
    if (touchesEnd) {
      ends = !backslashAfterLastNew(hunk.items);
    }
    d += newLines.length - oldLines.length;
  }
  return { lines, ends };
}

function applyUnifiedCreate(tree: Tree, edit: { path: string; hunks: Hunk[] }): EditFailure | null {
  if (!isSafePath(edit.path)) return fail("unsafe", edit.path);
  if (tree.has(edit.path)) return fail("exists", edit.path);
  const allItems: BodyItem[] = [];
  const created: string[] = [];
  for (const hunk of edit.hunks) {
    for (const it of hunk.items) {
      allItems.push(it);
      if (it.kind === "new") created.push(it.text);
    }
  }
  if (created.length === 0) {
    tree.set(edit.path, "");
    return null;
  }
  const ends = !backslashAfterLastPlus(allItems);
  tree.set(edit.path, serializeFile(created, "\n", ends));
  return null;
}

// ---------------------------------------------------------------------------
// SEARCH/REPLACE blocks (SPEC section 7)
// ---------------------------------------------------------------------------

function parseSearchReplace(lines: string[]): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = 0;
  let i = 0;
  while (i < lines.length) {
    if (trimRightWs(lines[i]) !== "<<<<<<< SEARCH") {
      i += 1;
      continue;
    }
    const searchLine = i + 1;
    let path: string | null = null;
    for (let j = i - 1; j >= prevEnd; j -= 1) {
      const t = lines[j].trim();
      if (t !== "" && !t.startsWith("```")) {
        path = t;
        break;
      }
    }
    if (path === null) {
      if (edits.length > 0) {
        path = (edits[edits.length - 1] as { path: string }).path;
      } else {
        failParse(searchLine);
      }
    }
    let eq = -1;
    let k = i + 1;
    let bad = false;
    while (k < lines.length) {
      if (trimRightWs(lines[k]) === "=======") {
        eq = k;
        break;
      }
      if (trimRightWs(lines[k]) === ">>>>>>> REPLACE") {
        bad = true;
        break;
      }
      k += 1;
    }
    if (eq === -1 || bad) failParse(searchLine);
    let rep = -1;
    let m = eq + 1;
    while (m < lines.length) {
      if (trimRightWs(lines[m]) === ">>>>>>> REPLACE") {
        rep = m;
        break;
      }
      m += 1;
    }
    if (rep === -1) failParse(searchLine);
    edits.push({ kind: "sr", path, oldLines: lines.slice(i + 1, eq), newLines: lines.slice(eq + 1, rep) });
    prevEnd = rep + 1;
    i = rep + 1;
  }
  if (edits.length === 0) failParse(1);
  return edits;
}

function applySearchReplace(tree: Tree, edit: { path: string; oldLines: string[]; newLines: string[] }, strict: boolean): EditFailure | null {
  if (!isSafePath(edit.path)) return fail("unsafe", edit.path);
  if (edit.oldLines.length === 0) {
    if (tree.has(edit.path)) return fail("exists", edit.path);
    tree.set(edit.path, serializeFile(edit.newLines, "\n", edit.newLines.length > 0));
    return null;
  }
  const current = tree.get(edit.path);
  if (current === undefined) return fail("missing", edit.path);
  const view = parseFileText(current);
  const hit = findTier(view.lines, edit.oldLines, strict);
  if (hit === null) return fail("no-match", edit.path);
  if (hit.positions.length > 1) return fail("ambiguous", edit.path);
  const pos = hit.positions[0];
  const items: NewLine[] = edit.newLines.map((t) => ({ text: t, ctx: false, oIdx: -1 }));
  const resolved = resolveNewLines(items, view.lines, pos, hit.tier, edit.oldLines);
  const lines = view.lines.slice(0, pos).concat(resolved).concat(view.lines.slice(pos + edit.oldLines.length));
  tree.set(edit.path, serializeFile(lines, view.br, view.ends));
  return null;
}

// ---------------------------------------------------------------------------
// V4A patches (SPEC section 8)
// ---------------------------------------------------------------------------

function isV4aSectionStart(line: string): boolean {
  return line.startsWith("*** Add File: ") || line.startsWith("*** Delete File: ") || line.startsWith("*** Update File: ");
}

function parseV4a(lines: string[]): Edit[] {
  const firstNb = lines.findIndex((l) => !isBlank(l));
  if (firstNb === -1) failParse(1);
  if (lines[firstNb].trim() !== "*** Begin Patch") failParse(firstNb + 1);
  let lastNb = -1;
  for (let i = lines.length - 1; i >= 0; i -= 1) {
    if (!isBlank(lines[i])) {
      lastNb = i;
      break;
    }
  }
  if (lines[lastNb].trim() !== "*** End Patch") failParse(lines.length + 1);
  const edits: Edit[] = [];
  let i = firstNb + 1;
  while (i < lastNb) {
    while (i < lastNb && isBlank(lines[i])) i += 1;
    if (i >= lastNb) break;
    const line = lines[i];
    if (line.startsWith("*** Add File: ")) {
      const path = line.slice("*** Add File: ".length).trim();
      const fileLines: string[] = [];
      let j = i + 1;
      while (j < lastNb && !isV4aSectionStart(lines[j])) {
        const l = lines[j];
        if (l.startsWith("+")) fileLines.push(l.slice(1));
        else if (isBlank(l)) fileLines.push("");
        else failParse(j + 1);
        j += 1;
      }
      while (fileLines.length > 0 && fileLines[fileLines.length - 1] === "") fileLines.pop();
      edits.push({ kind: "v-add", path, lines: fileLines });
      i = j;
      continue;
    }
    if (line.startsWith("*** Delete File: ")) {
      const path = line.slice("*** Delete File: ".length).trim();
      edits.push({ kind: "v-delete", path });
      i += 1;
      continue;
    }
    if (line.startsWith("*** Update File: ")) {
      const path = line.slice("*** Update File: ".length).trim();
      const updateLine = i + 1;
      let moveTo: string | null = null;
      const chunks: VChunk[] = [];
      let curChunk: VChunk | null = null;
      let seenChunk = false;
      let seenMove = false;
      let j = i + 1;
      while (j < lastNb && !isV4aSectionStart(lines[j])) {
        const l = lines[j];
        if (isBlank(l)) {
          if (curChunk !== null) curChunk.items.push({ kind: "ctx", text: "" });
          j += 1;
          continue;
        }
        if (l.startsWith(" ") || l.startsWith("-") || l.startsWith("+")) {
          if (curChunk === null) {
            // Only the first chunk may start at a body line.
            if (seenChunk) failParse(j + 1);
            curChunk = { anchor: null, eof: false, items: [] };
            chunks.push(curChunk);
            seenChunk = true;
          }
          curChunk.items.push(bodyItemOf(l));
          j += 1;
          continue;
        }
        if (l.startsWith("*** Move to: ")) {
          if (seenChunk || seenMove) failParse(j + 1);
          moveTo = l.slice("*** Move to: ".length).trim();
          seenMove = true;
          j += 1;
          continue;
        }
        if (l.startsWith("@@")) {
          const anchorText = l.slice(2).trim();
          curChunk = { anchor: anchorText === "" ? null : anchorText, eof: false, items: [] };
          chunks.push(curChunk);
          seenChunk = true;
          j += 1;
          continue;
        }
        if (l.trim() === "*** End of File") {
          if (curChunk === null) failParse(j + 1);
          curChunk.eof = true;
          curChunk = null;
          j += 1;
          continue;
        }
        failParse(j + 1);
      }
      if (!seenChunk && moveTo === null) failParse(updateLine);
      if (chunks.length > 0) {
        const last = chunks[chunks.length - 1];
        while (last.items.length > 0) {
          const item = last.items[last.items.length - 1];
          if (item.kind === "ctx" && item.text === "") last.items.pop();
          else break;
        }
      }
      edits.push({ kind: "v-update", path, moveTo, chunks });
      i = j;
      continue;
    }
    failParse(i + 1);
  }
  if (edits.length === 0) failParse(1);
  return edits;
}

function applyV4aUpdate(
  tree: Tree,
  edit: { path: string; moveTo: string | null; chunks: VChunk[] },
  strict: boolean,
  movePairs: { oldPath: string; newPath: string }[],
): EditFailure | null {
  if (!isSafePath(edit.path)) return fail("unsafe", edit.path);
  if (edit.moveTo !== null && !isSafePath(edit.moveTo)) return fail("unsafe", edit.moveTo);
  const current = tree.get(edit.path);
  if (current === undefined) return fail("missing", edit.path);
  if (edit.moveTo !== null && tree.has(edit.moveTo)) return fail("exists", edit.moveTo);
  const view = parseFileText(current);
  let lines = view.lines.slice();
  let cursor = 0;
  const tiers = strict ? [0] : [0, 1, 2];
  for (const chunk of edit.chunks) {
    if (chunk.anchor !== null) {
      let anchorIdx = -1;
      for (const t of tiers) {
        for (let idx = cursor; idx < lines.length; idx += 1) {
          if (matchSingle(lines[idx], chunk.anchor, t)) {
            anchorIdx = idx;
            break;
          }
        }
        if (anchorIdx !== -1) break;
      }
      if (anchorIdx === -1) return fail("no-match", edit.path);
      cursor = anchorIdx + 1;
    }
    const { oldLines, newLines } = buildOldNew(chunk.items);
    if (oldLines.length === 0) {
      const at = chunk.eof ? lines.length : cursor;
      const inserted = newLines.map((n) => n.text);
      lines = lines.slice(0, at).concat(inserted).concat(lines.slice(at));
      cursor = at + inserted.length;
      continue;
    }
    let found: { tier: number; pos: number } | null = null;
    for (const t of tiers) {
      const occs = findOccurrences(lines, oldLines, t).filter(
        (pos) => pos >= cursor && (!chunk.eof || pos + oldLines.length === lines.length),
      );
      if (occs.length > 0) {
        found = { tier: t, pos: occs[0] };
        break;
      }
    }
    if (found === null) return fail("no-match", edit.path);
    const resolved = resolveNewLines(newLines, lines, found.pos, found.tier, oldLines);
    lines = lines.slice(0, found.pos).concat(resolved).concat(lines.slice(found.pos + oldLines.length));
    cursor = found.pos + resolved.length;
  }
  const result = serializeFile(lines, view.br, view.ends);
  if (edit.moveTo !== null) {
    tree.delete(edit.path);
    tree.set(edit.moveTo, result);
    movePairs.push({ oldPath: edit.path, newPath: edit.moveTo });
  } else {
    tree.set(edit.path, result);
  }
  return null;
}

// ---------------------------------------------------------------------------
// JSON edits (SPEC section 9)
// ---------------------------------------------------------------------------

function validateJsonEdit(obj: unknown): Edit | null {
  if (typeof obj !== "object" || obj === null || Array.isArray(obj)) return null;
  const o = obj as Record<string, unknown>;
  if (typeof o.path !== "string") return null;
  if (typeof o.command !== "string") return null;
  if (o.command === "create") {
    if (typeof o.file_text !== "string") return null;
    return { kind: "j-create", path: o.path, text: o.file_text };
  }
  if (o.command === "str_replace") {
    if (typeof o.old_str !== "string" || o.old_str === "") return null;
    let newStr = "";
    if (o.new_str !== undefined) {
      if (typeof o.new_str !== "string") return null;
      newStr = o.new_str;
    }
    return { kind: "j-str", path: o.path, oldStr: o.old_str, newStr };
  }
  if (o.command === "insert") {
    if (typeof o.insert_line !== "number" || !Number.isInteger(o.insert_line)) return null;
    if (typeof o.new_str !== "string") return null;
    return { kind: "j-insert", path: o.path, insertLine: o.insert_line, newStr: o.new_str };
  }
  return null;
}

function parseJson(text: string, lines: string[]): Edit[] {
  const firstNb = lines.findIndex((l) => !isBlank(l));
  if (firstNb === -1) failParse(1);
  const firstChar = lines[firstNb].trimStart().charAt(0);
  if (firstChar === "[") {
    const startLine = firstNb + 1;
    let value: unknown;
    try {
      value = JSON.parse(text);
    } catch {
      failParse(startLine);
    }
    if (!Array.isArray(value)) failParse(startLine);
    const edits: Edit[] = [];
    for (const el of value) {
      const edit = validateJsonEdit(el);
      if (edit === null) failParse(startLine);
      edits.push(edit);
    }
    if (edits.length === 0) failParse(1);
    return edits;
  }
  const edits: Edit[] = [];
  for (let i = 0; i < lines.length; i += 1) {
    if (isBlank(lines[i])) continue;
    let value: unknown;
    try {
      value = JSON.parse(lines[i]);
    } catch {
      failParse(i + 1);
    }
    const edit = validateJsonEdit(value);
    if (edit === null) failParse(i + 1);
    edits.push(edit);
  }
  if (edits.length === 0) failParse(1);
  return edits;
}

function countOccurrences(text: string, needle: string): { count: number; first: number } {
  let count = 0;
  let first = -1;
  let from = 0;
  for (;;) {
    const idx = text.indexOf(needle, from);
    if (idx === -1) break;
    if (first === -1) first = idx;
    count += 1;
    from = idx + 1;
    if (count > 1) break;
  }
  return { count, first };
}

function applyJson(tree: Tree, edit: Edit): EditFailure | null {
  if (edit.kind === "j-create") {
    if (!isSafePath(edit.path)) return fail("unsafe", edit.path);
    if (tree.has(edit.path)) return fail("exists", edit.path);
    tree.set(edit.path, edit.text);
    return null;
  }
  if (edit.kind === "j-str") {
    if (!isSafePath(edit.path)) return fail("unsafe", edit.path);
    const current = tree.get(edit.path);
    if (current === undefined) return fail("missing", edit.path);
    const view = parseFileText(current);
    let text = current;
    let oldStr = edit.oldStr;
    let newStr = edit.newStr;
    if (view.br === "\r\n") {
      text = current.replace(/\r\n/g, "\n");
      oldStr = edit.oldStr.replace(/\r\n/g, "\n");
      newStr = edit.newStr.replace(/\r\n/g, "\n");
    }
    const found = countOccurrences(text, oldStr);
    if (found.count === 0) return fail("no-match", edit.path);
    if (found.count > 1) return fail("ambiguous", edit.path);
    let result = text.slice(0, found.first) + newStr + text.slice(found.first + oldStr.length);
    if (view.br === "\r\n") result = result.replace(/\n/g, "\r\n");
    tree.set(edit.path, result);
    return null;
  }
  // j-insert
  if (!isSafePath(edit.path)) return fail("unsafe", edit.path);
  const current = tree.get(edit.path);
  if (current === undefined) return fail("missing", edit.path);
  const view = parseFileText(current);
  if (edit.insertLine < 0 || edit.insertLine > view.lines.length) return fail("no-match", edit.path);
  const insLines = edit.newStr === "" ? [] : splitPatchLines(edit.newStr);
  const lines = view.lines.slice(0, edit.insertLine).concat(insLines).concat(view.lines.slice(edit.insertLine));
  tree.set(edit.path, serializeFile(lines, view.br, view.ends));
  return null;
}

// ---------------------------------------------------------------------------
// Dispatch, tree input/output (SPEC sections 2 and 10)
// ---------------------------------------------------------------------------

function applyEdit(tree: Tree, edit: Edit, strict: boolean, movePairs: { oldPath: string; newPath: string }[]): EditFailure | null {
  switch (edit.kind) {
    case "u-create":
      return applyUnifiedCreate(tree, edit);
    case "u-delete": {
      if (!isSafePath(edit.path)) return fail("unsafe", edit.path);
      if (!tree.has(edit.path)) return fail("missing", edit.path);
      tree.delete(edit.path);
      return null;
    }
    case "u-move": {
      if (!isSafePath(edit.oldPath)) return fail("unsafe", edit.oldPath);
      if (!isSafePath(edit.newPath)) return fail("unsafe", edit.newPath);
      const current = tree.get(edit.oldPath);
      if (current === undefined) return fail("missing", edit.oldPath);
      if (tree.has(edit.newPath)) return fail("exists", edit.newPath);
      const view = parseFileText(current);
      const applied = applyHunks(view, edit.hunks, strict, edit.oldPath);
      if ("code" in applied) return applied;
      tree.delete(edit.oldPath);
      tree.set(edit.newPath, serializeFile(applied.lines, view.br, applied.ends));
      movePairs.push({ oldPath: edit.oldPath, newPath: edit.newPath });
      return null;
    }
    case "u-change": {
      if (!isSafePath(edit.path)) return fail("unsafe", edit.path);
      const current = tree.get(edit.path);
      if (current === undefined) return fail("missing", edit.path);
      const view = parseFileText(current);
      const applied = applyHunks(view, edit.hunks, strict, edit.path);
      if ("code" in applied) return applied;
      tree.set(edit.path, serializeFile(applied.lines, view.br, applied.ends));
      return null;
    }
    case "sr":
      return applySearchReplace(tree, edit, strict);
    case "v-add": {
      if (!isSafePath(edit.path)) return fail("unsafe", edit.path);
      if (tree.has(edit.path)) return fail("exists", edit.path);
      tree.set(edit.path, serializeFile(edit.lines, "\n", edit.lines.length > 0));
      return null;
    }
    case "v-delete": {
      if (!isSafePath(edit.path)) return fail("unsafe", edit.path);
      if (!tree.has(edit.path)) return fail("missing", edit.path);
      tree.delete(edit.path);
      return null;
    }
    case "v-update":
      return applyV4aUpdate(tree, edit, strict, movePairs);
    default:
      return applyJson(tree, edit);
  }
}

function readTree(): Tree {
  const out: Tree = new Map();
  const walk = (dir: string, prefix: string): void => {
    let entries;
    try {
      entries = readdirSync(dir, { withFileTypes: true });
    } catch {
      return;
    }
    for (const e of entries) {
      const rel = prefix === "" ? e.name : `${prefix}/${e.name}`;
      if (e.isDirectory()) {
        walk(join(dir, e.name), rel);
      } else if (e.isFile()) {
        try {
          out.set(rel, readFileSync(join(dir, e.name), "utf8"));
        } catch {
          // unreadable file: leave it out of the snapshot
        }
      }
    }
  };
  walk(".", "");
  return out;
}

function writeTree(initial: Tree, tree: Tree): void {
  for (const p of new Set([...initial.keys(), ...tree.keys()])) {
    const before = initial.get(p);
    const after = tree.get(p);
    if (before === after) continue;
    if (after === undefined) {
      try {
        unlinkSync(p);
      } catch {
        // already gone
      }
    } else {
      try {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, after, "utf8");
      } catch {
        // unwritable path: nothing sensible to do here
      }
    }
  }
}

interface OutLine {
  key: string;
  line: string;
}

function computeOutput(initial: Tree, tree: Tree, movePairs: { oldPath: string; newPath: string }[]): string[] {
  let out: OutLine[] = [];
  for (const p of new Set([...initial.keys(), ...tree.keys()])) {
    const before = initial.get(p);
    const after = tree.get(p);
    if (before === after) continue;
    if (before === undefined) out.push({ key: p, line: `A ${p}` });
    else if (after === undefined) out.push({ key: p, line: `D ${p}` });
    else out.push({ key: p, line: `M ${p}` });
  }
  for (const pair of movePairs) {
    if (initial.has(pair.oldPath) && !tree.has(pair.oldPath) && !initial.has(pair.newPath) && tree.has(pair.newPath)) {
      out = out.filter((e) => e.line !== `D ${pair.oldPath}` && e.line !== `A ${pair.newPath}`);
      out.push({ key: pair.newPath, line: `R ${pair.oldPath} -> ${pair.newPath}` });
    }
  }
  out.sort((a, b) => {
    const c = Buffer.compare(Buffer.from(a.key, "utf8"), Buffer.from(b.key, "utf8"));
    return c !== 0 ? c : a.line < b.line ? -1 : a.line > b.line ? 1 : 0;
  });
  return out.map((e) => e.line);
}

function run(argv: string[]): { code: number; out: string[] } {
  const args = parseArgs(argv);
  if (args === null) return { code: 2, out: ["error: usage"] };
  let patchText: string;
  if (args.patch === null || args.patch === "-") {
    try {
      patchText = readFileSync(0, "utf8");
    } catch {
      patchText = "";
    }
  } else {
    try {
      patchText = readFileSync(args.patch, "utf8");
    } catch {
      return { code: 2, out: ["error: no-patch"] };
    }
  }
  const patchLines = splitPatchLines(patchText);
  let format = args.format;
  if (format === "auto") {
    const detected = detectFormat(patchLines);
    if (detected === null) return { code: 2, out: ["error: format"] };
    format = detected;
  }
  let edits: Edit[];
  try {
    if (format === "unified") edits = parseUnified(patchLines);
    else if (format === "search-replace") edits = parseSearchReplace(patchLines);
    else if (format === "v4a") edits = parseV4a(patchLines);
    else edits = parseJson(patchText, patchLines);
  } catch (err) {
    if (err instanceof ParseFault) return { code: 2, out: [`error: parse ${err.line}`] };
    throw err;
  }
  const initial = readTree();
  const tree: Tree = new Map(initial);
  const failures: EditFailure[] = [];
  const movePairs: { oldPath: string; newPath: string }[] = [];
  for (const edit of edits) {
    const f = applyEdit(tree, edit, args.strict, movePairs);
    if (f !== null) failures.push(f);
  }
  if (failures.length > 0) {
    const out = failures.map((f) => `error: ${f.code} ${f.path}`);
    out.push(`failed: ${failures.length} of ${edits.length} edits`);
    return { code: 1, out };
  }
  const lines = computeOutput(initial, tree, movePairs);
  if (!args.check) writeTree(initial, tree);
  lines.push(lines.length === 1 ? "ok: 1 file" : `ok: ${lines.length} files`);
  return { code: 0, out: lines };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
