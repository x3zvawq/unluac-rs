# Aligned Table Layout

Passing `--table-style aligned` formats Lua table constructors so arrays line up in clean columns and record keys align on `=`. It is designed especially for reading large data and config tables.

## How a Table Layout Is Chosen

For each table constructor, `aligned` tries four layouts in order and picks the first one that fits:

1. **Single line** — the entire table fits on the current line:
   ```lua
   local anchors = { 10, 20, 30 }
   ```
2. **Packed inner line** — all fields fit on one indented line between `{` and `}`:
   ```lua
   local fallback = {
       alpha = 1, beta = 2, gamma = 3, delta = 4, epsilon = 5, zeta = 6
   }
   ```
3. **Aligned grid** — a pure positional array where every item is the same kind of simple literal (all numbers, all short strings, all booleans, all plain identifiers, or all `nil`) is formatted as an aligned multi-column grid:
   ```lua
   local values = {
        7, 42,  5, 91,  3, 28, 64, 12, 80, 56,  9, 47, 31, 75,  2, 60,
       38, 84, 15, 70, 26, 93, 58, 41,  6, 77, 19, 85, 32, 68, 24, 50,
   }

   local labels = {
       "peninsula",   "archipelago", "mountains",   "waterfall",
       "wilderness",  "undergrowth", "tableland",   "watershed",
   }
   ```
4. **One entry per line** — dictionaries, mixed arrays, expressions, nested tables, or strings wider than `--table-align-string-width` are laid out one field per line with trailing commas. Adjacent record keys align their `=` signs automatically:
   ```lua
   local config = {
       name    = "unluac",
       threads = 4,
       paths   = { "/usr/share/lua/5.1/?.lua", "/usr/local/share/lua/5.1/?.lua" },
       retries = 3,
   }
   ```

## Options Reference

All `--table-align-*` options apply only to `--table-style aligned`. `--table-drop-index-keys` works with every table style.

| CLI Flag | JS / Rust Option | Default | What It Controls |
| --- | --- | --- | --- |
| `--table-align-width` | `tableAlignWidth` / `table_align_width` | `max_line_length` (`100`) | Max width (including indentation) for aligned rows. |
| `--table-align-string-width` | `tableAlignStringWidth` / `table_align_string_width` | `16` | Max rendered width (including quotes) of a string inside a grid; wider strings fall back to one entry per line. |
| `--table-align-cells` | `tableAlignCells` / `table_align_cells` | `auto` | Grid cell alignment: `auto` right-aligns numbers and left-aligns everything else; `left` or `right` forces one direction. |
| `--table-align-eq` | `tableAlignEq` / `table_align_eq` | `true` | Align `=` across adjacent record keys in multi-line tables. |
| `--table-align-eq-max-spaces` | `tableAlignEqMaxSpaces` / `table_align_eq_max_spaces` | `8` | Maximum spaces inserted before `=` so one very long key does not stretch neighboring rows (`0` disables alignment). |
| `--table-drop-index-keys` | `tableDropIndexKeys` / `table_drop_index_keys` | `false` | Omit sequential `[1] = ...`, `[2] = ...` keys when provably safe (see below). |

## Omitting Sequential Index Keys (`--table-drop-index-keys`)

Compilers sometimes emit `{ [1] = "a", [2] = "b" }` as explicit hash/keyed writes. Enabling `--table-drop-index-keys` (included in `--preset readable` and `--preset ai`) turns safe sequential integer keys back into positional array items:

```lua
-- Before: { [1] = "alpha", [2] = "beta" }
local keyed = { "alpha", "beta" }

-- Unchanged when unsafe or sparse:
local sparse    = { [1] = "alpha", [3] = "gamma" } -- gap in indices
local dynamic   = { [1] = f() }                    -- function call (multi-return boundary)
local collision = { [1] = 7, [key] = 9 }           -- dynamic key could collide
```

This simplification only runs on Lua 5.1–5.5 constructors whose `[1]..[n]` values are contiguous non-`nil` scalar literals (numbers, strings, booleans) with no overlapping keys, side effects, or holes. Everything else is kept verbatim.
