#![forbid(unsafe_code)]

//! 这个 crate 承载 `unluac` 的 wasm 边界。
//!
//! 边界层只接受 JS 友好的字符串和对象，再把它们映射回核心库的强类型选项。
//! 这样 CLI、wasm 和后续 `unluac-js` 都能共享同一套枚举协议，而不是各自依赖
//! Rust enum 的内部表示。

use serde::de::IgnoredAny;
use serde::{Deserialize, Serialize};
use std::str::FromStr;
use wasm_bindgen::prelude::*;

use unluac::decompile::{
    DecompileDialect, DecompileOptions, NamingMode, QuoteStyle, TableStyle,
    decompile as run_decompile,
};
use unluac::parser::{ParseMode, StringDecodeMode, StringEncoding};

pub use unluac as core;

#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
struct WasmDecompileOptions {
    dialect: Option<String>,
    parse: Option<WasmParseOptions>,
    debug: Option<IgnoredAny>,
    readability: Option<WasmReadabilityOptions>,
    naming: Option<WasmNamingOptions>,
    generate: Option<WasmGenerateOptions>,
}

#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
struct WasmParseOptions {
    mode: Option<String>,
    string_encoding: Option<String>,
    string_decode_mode: Option<String>,
}

#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
struct WasmReadabilityOptions {
    return_inline_max_complexity: Option<usize>,
    index_inline_max_complexity: Option<usize>,
    args_inline_max_complexity: Option<usize>,
    access_base_inline_max_complexity: Option<usize>,
}

#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
struct WasmNamingOptions {
    mode: Option<String>,
    debug_like_include_function: Option<bool>,
}

#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase", default)]
struct WasmGenerateOptions {
    mode: Option<String>,
    indent_width: Option<usize>,
    max_line_length: Option<usize>,
    quote_style: Option<String>,
    table_style: Option<String>,
    conservative_output: Option<bool>,
    comment: Option<bool>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct WasmSupportedOptionValues {
    dialects: Vec<&'static str>,
    parse_modes: Vec<&'static str>,
    string_encodings: Vec<&'static str>,
    string_decode_modes: Vec<&'static str>,
    naming_modes: Vec<&'static str>,
    quote_styles: Vec<&'static str>,
    table_styles: Vec<&'static str>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct WasmBridgeError {
    code: &'static str,
    message: String,
    field: Option<&'static str>,
}

type BridgeResult<T> = Result<T, WasmBridgeError>;

#[wasm_bindgen(js_name = decompile)]
pub fn decompile_wasm(bytes: &[u8], options: JsValue) -> Result<JsValue, JsValue> {
    let options = parse_wasm_options(options).map_err(WasmBridgeError::into_js_value)?;
    let result = run_decompile(bytes, options).map_err(|error| {
        WasmBridgeError::new("decompile-failed", error.to_string(), None).into_js_value()
    })?;

    let generated_source = result
        .state
        .generated
        .map(|generated| generated.source)
        .ok_or_else(|| {
            WasmBridgeError::new(
                "missing-generated-source",
                "expected generate stage output, but no source was produced",
                None,
            )
            .into_js_value()
        })?;

    to_js_value(&generated_source)
}

#[wasm_bindgen(js_name = supportedOptionValues)]
pub fn supported_option_values() -> Result<JsValue, JsValue> {
    to_js_value(&WasmSupportedOptionValues {
        dialects: dialect_labels(),
        parse_modes: parse_mode_labels(),
        string_encodings: string_encoding_labels(),
        string_decode_modes: string_decode_mode_labels(),
        naming_modes: naming_mode_labels(),
        quote_styles: quote_style_labels(),
        table_styles: table_style_labels(),
    })
}

fn parse_wasm_options(value: JsValue) -> BridgeResult<DecompileOptions> {
    let options = if value.is_undefined() || value.is_null() {
        WasmDecompileOptions::default()
    } else {
        serde_wasm_bindgen::from_value(value)
            .map_err(|error| WasmBridgeError::new("invalid-options", error.to_string(), None))?
    };

    options.into_core_options()
}

impl WasmDecompileOptions {
    fn into_core_options(self) -> BridgeResult<DecompileOptions> {
        let mut options = default_wasm_decompile_options();

        if let Some(value) = self.dialect {
            options.dialect = parse_option("dialect", &value)?;
        }
        if let Some(parse) = self.parse {
            parse.apply(&mut options)?;
        }
        if self.debug.is_some() {
            return Err(WasmBridgeError::new(
                "unsupported-option",
                "the published wasm build omits debug and timing support to keep the bundle small",
                Some("debug"),
            ));
        }
        if let Some(readability) = self.readability {
            readability.apply(&mut options);
        }
        if let Some(naming) = self.naming {
            naming.apply(&mut options)?;
        }
        if let Some(generate) = self.generate {
            generate.apply(&mut options)?;
        }

        Ok(options)
    }
}

impl WasmParseOptions {
    fn apply(self, options: &mut DecompileOptions) -> BridgeResult<()> {
        if let Some(value) = self.mode {
            options.parse.mode = parse_option("parse.mode", &value)?;
        }
        if let Some(value) = self.string_encoding {
            options.parse.string_encoding = parse_option("parse.stringEncoding", &value)?;
        }
        if let Some(value) = self.string_decode_mode {
            options.parse.string_decode_mode = parse_option("parse.stringDecodeMode", &value)?;
        }
        Ok(())
    }
}

impl WasmReadabilityOptions {
    fn apply(self, options: &mut DecompileOptions) {
        if let Some(value) = self.return_inline_max_complexity {
            options.readability.return_inline_max_complexity = value;
        }
        if let Some(value) = self.index_inline_max_complexity {
            options.readability.index_inline_max_complexity = value;
        }
        if let Some(value) = self.args_inline_max_complexity {
            options.readability.args_inline_max_complexity = value;
        }
        if let Some(value) = self.access_base_inline_max_complexity {
            options.readability.access_base_inline_max_complexity = value;
        }
    }
}

impl WasmNamingOptions {
    fn apply(self, options: &mut DecompileOptions) -> BridgeResult<()> {
        if let Some(value) = self.mode {
            options.naming.mode = parse_option("naming.mode", &value)?;
        }
        if let Some(value) = self.debug_like_include_function {
            options.naming.debug_like_include_function = value;
        }
        Ok(())
    }
}

impl WasmGenerateOptions {
    fn apply(self, options: &mut DecompileOptions) -> BridgeResult<()> {
        if let Some(value) = self.mode {
            options.generate.mode = parse_option("generate.mode", &value)?;
        }
        if let Some(value) = self.indent_width {
            options.generate.indent_width = value;
        }
        if let Some(value) = self.max_line_length {
            options.generate.max_line_length = value;
        }
        if let Some(value) = self.quote_style {
            options.generate.quote_style = parse_option("generate.quoteStyle", &value)?;
        }
        if let Some(value) = self.table_style {
            options.generate.table_style = parse_option("generate.tableStyle", &value)?;
        }
        if let Some(value) = self.conservative_output {
            options.generate.conservative_output = value;
        }
        if let Some(value) = self.comment {
            options.generate.comment = value;
        }
        Ok(())
    }
}

fn parse_option<T>(field: &'static str, value: &str) -> BridgeResult<T>
where
    T: FromStr,
{
    value.parse().map_err(|_| {
        WasmBridgeError::new(
            "invalid-enum-value",
            format!("unsupported value {value:?} for `{field}`"),
            Some(field),
        )
    })
}

fn default_wasm_decompile_options() -> DecompileOptions {
    let mut options = DecompileOptions::default();
    // WASM 面向最终用户，默认使用 Permissive 以尽可能输出结果。
    options.generate.mode = unluac::decompile::GenerateMode::Permissive;
    options
}

impl WasmBridgeError {
    fn new(code: &'static str, message: impl Into<String>, field: Option<&'static str>) -> Self {
        Self {
            code,
            message: message.into(),
            field,
        }
    }

    fn into_js_value(self) -> JsValue {
        serde_wasm_bindgen::to_value(&self).expect("serializing bridge error should not fail")
    }
}

fn to_js_value<T>(value: &T) -> Result<JsValue, JsValue>
where
    T: Serialize,
{
    serde_wasm_bindgen::to_value(value)
        .map_err(|error| WasmBridgeError::new("bridge-serialize-failed", error.to_string(), None))
        .map_err(WasmBridgeError::into_js_value)
}

fn dialect_labels() -> Vec<&'static str> {
    [
        DecompileDialect::Lua51,
        DecompileDialect::Lua52,
        DecompileDialect::Lua53,
        DecompileDialect::Lua54,
        DecompileDialect::Lua55,
        DecompileDialect::Luajit,
        DecompileDialect::Luau,
    ]
    .into_iter()
    .map(DecompileDialect::as_str)
    .collect()
}

fn parse_mode_labels() -> Vec<&'static str> {
    [ParseMode::Strict, ParseMode::Permissive]
        .into_iter()
        .map(ParseMode::as_str)
        .collect()
}

fn string_encoding_labels() -> Vec<&'static str> {
    [StringEncoding::Utf8, StringEncoding::Gbk]
        .into_iter()
        .map(StringEncoding::as_str)
        .collect()
}

fn string_decode_mode_labels() -> Vec<&'static str> {
    [StringDecodeMode::Strict, StringDecodeMode::Lossy]
        .into_iter()
        .map(StringDecodeMode::as_str)
        .collect()
}

fn naming_mode_labels() -> Vec<&'static str> {
    [
        NamingMode::DebugLike,
        NamingMode::Simple,
        NamingMode::Heuristic,
    ]
    .into_iter()
    .map(NamingMode::as_str)
    .collect()
}

fn quote_style_labels() -> Vec<&'static str> {
    [
        QuoteStyle::PreferDouble,
        QuoteStyle::PreferSingle,
        QuoteStyle::MinEscape,
    ]
    .into_iter()
    .map(QuoteStyle::as_str)
    .collect()
}

fn table_style_labels() -> Vec<&'static str> {
    [
        TableStyle::Compact,
        TableStyle::Balanced,
        TableStyle::Expanded,
    ]
    .into_iter()
    .map(TableStyle::as_str)
    .collect()
}

#[cfg(test)]
mod tests {
    use super::{
        WasmDecompileOptions, WasmGenerateOptions, WasmNamingOptions, WasmParseOptions,
        default_wasm_decompile_options, parse_mode_labels, quote_style_labels,
    };
    use serde::de::IgnoredAny;
    use unluac::decompile::{DecompileDialect, NamingMode, QuoteStyle, TableStyle};
    use unluac::parser::{ParseMode, StringDecodeMode, StringEncoding};

    #[test]
    fn wasm_options_default_to_repo_generate_preset() {
        let options = WasmDecompileOptions::default()
            .into_core_options()
            .expect("default wasm options should be valid");

        assert_eq!(options, default_wasm_decompile_options());
        assert_eq!(options.parse.mode, ParseMode::Permissive);
        assert_eq!(options.naming.mode, NamingMode::DebugLike);
        assert!(options.naming.debug_like_include_function);
    }

    #[test]
    fn wasm_options_map_nested_string_enums_into_core_options() {
        let options = WasmDecompileOptions {
            dialect: Some("luau".to_owned()),
            parse: Some(WasmParseOptions {
                mode: Some("permissive".to_owned()),
                string_encoding: Some("gbk".to_owned()),
                string_decode_mode: Some("lossy".to_owned()),
            }),
            debug: None,
            readability: None,
            naming: Some(WasmNamingOptions {
                mode: Some("heuristic".to_owned()),
                debug_like_include_function: Some(false),
            }),
            generate: Some(WasmGenerateOptions {
                mode: None,
                indent_width: Some(2),
                max_line_length: Some(120),
                quote_style: Some("prefer-single".to_owned()),
                table_style: Some("expanded".to_owned()),
                conservative_output: Some(false),
                comment: Some(false),
            }),
        }
        .into_core_options()
        .expect("explicit wasm options should be valid");

        assert_eq!(options.dialect, DecompileDialect::Luau);
        assert_eq!(options.parse.mode, ParseMode::Permissive);
        assert_eq!(options.parse.string_encoding, StringEncoding::Gbk);
        assert_eq!(options.parse.string_decode_mode, StringDecodeMode::Lossy);
        assert_eq!(options.naming.mode, NamingMode::Heuristic);
        assert!(!options.naming.debug_like_include_function);
        assert_eq!(options.generate.indent_width, 2);
        assert_eq!(options.generate.max_line_length, 120);
        assert_eq!(options.generate.quote_style, QuoteStyle::PreferSingle);
        assert_eq!(options.generate.table_style, TableStyle::Expanded);
        assert!(!options.generate.conservative_output);
        assert!(!options.generate.comment);
    }

    #[test]
    fn wasm_options_reject_unknown_enum_values() {
        let error = WasmDecompileOptions {
            dialect: Some("lua9000".to_owned()),
            ..WasmDecompileOptions::default()
        }
        .into_core_options()
        .expect_err("unknown wasm enum values should be rejected");

        assert_eq!(error.code, "invalid-enum-value");
        assert_eq!(error.field, Some("dialect"));
    }

    #[test]
    fn wasm_options_reject_debug_payloads() {
        let error = WasmDecompileOptions {
            debug: Some(IgnoredAny),
            ..WasmDecompileOptions::default()
        }
        .into_core_options()
        .expect_err("published wasm build should reject debug options");

        assert_eq!(error.code, "unsupported-option");
        assert_eq!(error.field, Some("debug"));
    }

    #[test]
    fn supported_value_lists_match_public_labels() {
        assert_eq!(parse_mode_labels(), vec!["strict", "permissive"]);
        assert_eq!(
            quote_style_labels(),
            vec!["prefer-double", "prefer-single", "min-escape"]
        );
    }
}
