use crate::cache::CacheConfig;
use crate::parser_types::DcaMode;

/// This struct is used to configure optional behaviour within the ESI processor.
///
/// ## Usage Example
/// ```rust,no_run
/// let config = esi::Configuration::default()
///     .with_caching(esi::CacheConfig {
///         is_rendered_cacheable: true,
///         rendered_cache_control: true,
///         rendered_ttl: Some(600),
///         is_includes_cacheable: true,
///         includes_default_ttl: Some(300),
///         includes_force_ttl: None,
///     });
/// ```
#[allow(clippy::return_self_not_must_use)]
#[derive(Clone, Debug)]
pub struct Configuration {
    /// For working with non-HTML ESI templates, e.g. JSON files, this option allows you to disable the unescaping of URLs
    pub is_escaped_content: bool,
    /// Cache configuration for ESI includes
    pub cache: CacheConfig,
    /// Maximum recursion depth for user-defined function calls (per ESI spec, default: 5)
    pub function_recursion_depth: usize,
    /// Size of the read buffer (in bytes) used when streaming ESI input (default: 16384)
    pub chunk_size: usize,
    /// Default DCA mode for includes/evals without an explicit `dca` attribute.
    /// When set to `DcaMode::Esi`, fragments are processed as ESI by default
    /// (matching Akamai-style behaviour). Default: `DcaMode::None`.
    pub default_dca: DcaMode,
    /// Maximum nesting depth for ESI includes/evals (default: 15).
    /// Per the EdgeSuite ESI spec, up to fifteen levels of nested include
    /// statements are supported. When the limit is reached, fragment content
    /// is passed through as raw bytes without ESI processing.
    pub max_include_depth: usize,
    /// Enable parsing of `Edge-Control` response headers for per-fragment DCA
    /// directives (e.g. `Edge-Control: dca=esi`). When enabled, the header
    /// value overrides `default_dca` but is itself overridden by an explicit
    /// `dca` attribute on the tag. Default: `false`.
    pub enable_edge_control: bool,
    /// When true, an unspecified child fragment inside an explicit `dca=esi`
    /// subtree inherits ESI processing instead of falling back to `default_dca`.
    /// This lets `dca=esi` "stick" to its children without forcing all
    /// top-level includes to default to ESI. Default: `false`.
    pub inherit_parent_dca: bool,
}

impl Default for Configuration {
    fn default() -> Self {
        Self {
            is_escaped_content: true,
            cache: CacheConfig::default(),
            function_recursion_depth: 5,
            chunk_size: 16384,
            default_dca: DcaMode::None,
            max_include_depth: 15,
            enable_edge_control: false,
            inherit_parent_dca: false,
        }
    }
}

impl Configuration {
    /// For working with non-HTML ESI templates, eg JSON files, allows to disable URLs unescaping
    pub fn with_escaped(mut self, is_escaped: impl Into<bool>) -> Self {
        self.is_escaped_content = is_escaped.into();
        self
    }

    /// Configure caching for ESI includes
    ///
    /// See [`CacheConfig::rendered_cache_control`] for important notes on
    /// which processing methods support automatic `Cache-Control` header emission.
    pub const fn with_caching(mut self, cache: CacheConfig) -> Self {
        self.cache = cache;
        self
    }

    /// Configure maximum recursion depth for user-defined function calls
    pub const fn with_function_recursion_depth(mut self, depth: usize) -> Self {
        self.function_recursion_depth = depth;
        self
    }

    /// Configure the read buffer size (in bytes) for streaming ESI input.
    ///
    /// Larger values may improve throughput for big documents; smaller values
    /// reduce memory usage.  Default: 16384 (16 KB).
    pub const fn with_chunk_size(mut self, chunk_size: usize) -> Self {
        self.chunk_size = chunk_size;
        self
    }

    /// Configure the default DCA mode for `<esi:include>` and `<esi:eval>` tags
    /// that do not specify an explicit `dca` attribute.
    ///
    /// Set to `DcaMode::Esi` to enable Akamai-style behaviour where all
    /// fragments are ESI-processed by default. An explicit `dca="none"` on a
    /// tag still opts out.
    ///
    /// Default: `DcaMode::None`.
    pub const fn with_default_dca(mut self, dca: DcaMode) -> Self {
        self.default_dca = dca;
        self
    }

    /// Configure the maximum nesting depth for ESI includes and evals.
    ///
    /// Per the EdgeSuite ESI spec, up to fifteen levels of nested include
    /// statements are supported by default.  When the limit is reached,
    /// fragment content is passed through as raw bytes without further ESI
    /// processing.
    ///
    /// Default: `15`.
    pub const fn with_max_include_depth(mut self, depth: usize) -> Self {
        self.max_include_depth = depth;
        self
    }

    /// Enable or disable `Edge-Control` response header parsing.
    ///
    /// When enabled, fragment responses may include an `Edge-Control` header
    /// with a `dca=esi` or `dca=none` directive to control per-fragment ESI
    /// processing. This matches Akamai's "Enable Through Response Headers"
    /// property setting.
    ///
    /// Precedence (highest wins): tag attribute → Edge-Control header → `default_dca`.
    ///
    /// Default: `false` (disabled).
    pub const fn with_edge_control(mut self, enabled: bool) -> Self {
        self.enable_edge_control = enabled;
        self
    }

    /// Enable or disable subtree DCA inheritance.
    ///
    /// When enabled, an unspecified child fragment inside an explicit
    /// `dca=esi` subtree is processed as ESI, rather than falling back to
    /// the global `default_dca`. Top-level includes (not inside any ESI
    /// subtree) still use `default_dca`.
    ///
    /// Precedence (highest wins): tag attribute → Edge-Control header →
    /// inherited parent DCA (if enabled & inside subtree) → `default_dca`.
    ///
    /// Default: `false` (disabled).
    pub const fn with_inherit_parent_dca(mut self, enabled: bool) -> Self {
        self.inherit_parent_dca = enabled;
        self
    }
}
