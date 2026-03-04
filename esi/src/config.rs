use crate::cache::CacheConfig;

/// This struct is used to configure optional behaviour within the ESI processor.
///
/// ## Usage Example
/// ```rust,no_run
/// let config = esi::Configuration::default()
///     .with_caching(esi::cache::CacheConfig {
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
}

impl Default for Configuration {
    fn default() -> Self {
        Self {
            is_escaped_content: true,
            cache: CacheConfig::default(),
            function_recursion_depth: 5,
            chunk_size: 16384,
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
}
