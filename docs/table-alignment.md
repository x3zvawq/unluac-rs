# Aligned table layout

The `--table-style aligned` generate option rewrites table constructors so that
related values line up vertically. This page documents how the layout is
chosen, which values qualify, every option that tunes it, and what the output
looks like. The CLI quick reference in the README is a summary of this page.

Examples use Lua 5.1 and default options unless stated otherwise.

## Layout cascade

The `aligned` style picks one of four layouts per table, trying them in order:

1. **Single line** — the whole constructor fits on the current line:
   `local anchors = { 10, 20, 30 }`.
2. **Content on one line** — otherwise the content is kept as a single
   indented line between the braces whenever it fits there:
   ```lua
   local fallback = {
       alpha = 1, beta = 2, gamma = 3, delta = 4, epsilon = 5, zeta = 6, eta = 7, theta = 8
   }
   ```
3. **Aligned grid** — otherwise a pure array of small homogeneous elements is
   printed several cells per row, space-padded so columns line up (see
   [Grids](#grids)).
4. **One entry per line** — everything else (any dictionary, mixed arrays,
   over-wide strings, non-literal elements); nested tables follow the same
   rules at their own indentation. Multi-line entries carry trailing commas so
   appending a field never rewrites earlier lines.

Record fields (dictionary entries) additionally align their keys on `=`, which
is controlled by `--table-align-eq` and `--table-align-eq-max-spaces`.

## Grids

A table qualifies for the grid layout only when every field is a positional
array element of the same **cell kind**. The recognized primitives are:

| Cell kind | Rendered as | Default direction (`auto`) |
| --- | --- | --- |
| Number | integer/float literal | **right** — digits line up by magnitude and every trailing comma lands on the same column |
| String | short quoted literal | **left** — word-like values share a common left edge |
| Boolean | `true` / `false` | **left** |
| Name | plain identifier (no index/sugar) | **left** |
| Nil | `nil` | **left** (alignment-invariant: every cell is the same 3 characters) |

Anything else (function calls, binary expressions, long strings, nested
constructors, record fields) disqualifies the table from grid mode and it falls
back to one entry per line. A string wider than `--table-align-string-width`
(quotes included) disqualifies the whole table as well.

Grids are homogeneous by construction: one grid, one cell kind, so the
horizontal direction is resolved once per grid from the option and the kind.
Every column starts at a multiple of *widest cell + 2* characters, which keeps
the grid vertically aligned even when cell widths differ. Under `auto`,
right-aligned rows put the padding before each cell (commas line up);
left-aligned rows put it after each comma (values line up). Both directions
obey the same row budget from `--table-align-width`.

### Cell alignment: `--table-align-cells`

| Value | Behavior |
| --- | --- |
| `auto` (default) | Numbers right-align, every other primitive left-aligns. |
| `right` | All kinds right-align. |
| `left` | All kinds left-align. |

Rationale: for numbers, right alignment keeps mixed one- and two-digit values
comparable and lines up the trailing commas, which reads well in a column of
data. For strings, names and keywords, left alignment gives every value the
same starting column, which reads like a word list; padding before a quote
only pushes the text away from where the eye starts reading.

```lua
-- auto (default): strings left, padding sits after each comma
local labels = {
    "peninsula",   "archipelago", "mountains",   "waterfall",
    "wilderness",  "undergrowth", "tableland",   "watershed",
}

-- --table-align-cells=right: padding sits before each cell, commas align
-- local labels = {
--       "peninsula", "archipelago",   "mountains",   "waterfall",
--      "wilderness", "undergrowth",   "tableland",   "watershed",
-- }
```

```lua
-- auto (default): number grids right-align within their column
local values = {
     7, 42,  5, 91,  3, 28, 64, 12, 80, 56,  9, 47, 31, 75,  2, 60,
    38, 84, 15, 70, 26, 93, 58, 41,  6, 77, 19, 85, 32, 68, 24, 50,
}

-- --table-align-cells=left: same table, values start on a shared left edge
-- local values = {
--     7,  42, 5,  91, 3,  28, 64, 12, 80, 56, 9,  47, 31, 75, 2,  60,
--     38, 84, 15, 70, 26, 93, 58, 41, 6,  77, 19, 85, 32, 68, 24, 50,
-- }
```

## Options reference

Alignment options affect only `aligned`. `--table-drop-index-keys` applies before layout selection and therefore also affects the other styles.

| Option | Default | Effect |
| --- | --- | --- |
| `--table-align-width` | follows `--max-line-length` (100 by default) | Caps the rendered row width (including indentation), together with `--max-line-length`: the smaller limit governs grids, full single lines and packed content lines. An indivisible field may exceed the budget. |
| `--table-align-string-width` | 16 | Caps the rendered width (quotes included) of a string allowed inside a grid; a wider string disqualifies the whole table from grid mode (falls back to one entry per line). |
| `--table-align-cells` | `auto` | Horizontal alignment of grid cells. `auto`: numbers right, all other primitives left. `left`/`right` force one direction for every kind. |
| `--table-align-eq` | true | Aligns record keys by `=` in non-single-line tables: keys are padded to the widest key of their alignment run. `--table-align-eq=false` keeps single spaces around `=`. |
| `--table-align-eq-max-spaces` | 8 | Caps the total spaces between a record key and `=` (padding plus the mandatory separator): a key whose gap would exceed the cap starts a new alignment run instead of stretching every row. |
| `--table-drop-index-keys` | false | Omits continuous `[1]..[n]` keys only in safe PUC scalar constructors (see below). |

## Examples

### Record key alignment (`--table-align-eq`)

```lua
-- default: --table-align-eq aligns keys to the widest key of the run
local config = {
    name    = "unluac",
    threads = 4,
    paths   = { "/usr/share/lua/5.1/?.lua", "/usr/local/share/lua/5.1/?.lua" },
    retries = 3,
}
-- --table-align-eq=false: same table, no padding
--     name = "unluac",
--     threads = 4,
```

```lua
-- --table-align-eq-max-spaces=2: the visible gap between a key and `=` never
-- exceeds 2 spaces, so only keys one padding space apart stay aligned and
-- every wider key starts a new alignment run
--     id  = "op",
--     tag = "v1",
--     kind = "select",
--     timeout_ms = 1500,
--     retries = 4,
```

### Row budget (`--table-align-width`)

```lua
-- default (follows --max-line-length, 100 here): 16 cells per row
local values = {
     7, 42,  5, 91,  3, 28, 64, 12, 80, 56,  9, 47, 31, 75,  2, 60,
    38, 84, 15, 70, 26, 93, 58, 41,  6, 77, 19, 85, 32, 68, 24, 50,
}
-- --table-align-width=40: same table, 8 cells per row
-- local values = {
--      7, 42,  5, 91,  3, 28, 64, 12,
--     80, 56,  9, 47, 31, 75,  2, 60,
--     38, 84, 15, 70, 26, 93, 58, 41,
--      6, 77, 19, 85, 32, 68, 24, 50,
-- }
```

### String width cap (`--table-align-string-width`)

```lua
-- default cap of 16: the grid stays
local labels = {
    "peninsula",   "archipelago", "mountains",   "waterfall",
    "wilderness",  "undergrowth", "tableland",   "watershed",
}
-- --table-align-string-width=6: every rendered width (quotes included) is
-- wider than 6, so the whole table falls back to one entry per line
-- local labels = {
--     "peninsula",
--     "archipelago",
--     "mountains",
--     "waterfall",
--     "wilderness",
--     "undergrowth",
--     "tableland",
--     "watershed",
-- }
```

### Explicit index keys (`--table-drop-index-keys`)

This opt-in syntax projection applies to Lua 5.1–5.5 PUC batched constructors.
The numeric keys must occur as `[1]`, `[2]`, … in order, with no existing
positional fields. Every value must be a non-nil string, boolean or finite
number literal. Other fields may have static string, boolean or finite
non-integer numeric keys; they cannot overlap the array indices.

Calls (including a final multi-return call), varargs, variable reads, nested
allocations, nil values, dynamic keys, missing/repeated/out-of-order integer
keys and LuaJIT/Luau allocation protocols leave the entire constructor unchanged.
The static subset has no field-evaluation events, no overlapping writes and no
holes in the resulting array. This keeps scalar values and the array length
while permitting a different hash/array representation and unspecified `pairs`
iteration order. The default keeps all explicit keys.

```lua
local keyed = { "alpha", "beta" } -- was: { [1] = "alpha", [2] = "beta" }
local mixed = { mode = "dlg", "alpha", "beta", tag = 3 }
local sparse = { [1] = "alpha", [3] = "gamma" } -- gap: unchanged
local dynamic = { [1] = f() }                  -- single return: unchanged
local collision = { [1] = 7, [key] = 9 }       -- dynamic key: unchanged
```
