/// Caching module for ESI fragments
///
/// This module provides TTL tracking and calculation for ESI fragments based on Cache-Control headers.
/// Fastly's native edge cache handles actual caching - this module just tracks TTL for the rendered document.
use crate::Result;
use fastly::http::header::{CACHE_CONTROL, SET_COOKIE};
use fastly::Response;
use log::trace;

/// Cache configuration options
#[derive(Clone, Debug)]
pub struct CacheConfig {
    /// Enable caching of the rendered document (with a common minimum TTL tracked across includes)
    pub is_rendered_cacheable: bool,
    /// Emit Cache-Control header on final response (independent of `is_rendered_cacheable`)
    pub rendered_cache_control: bool,
    /// TTL in seconds for the rendered document (overrides tracked minimum TTL from includes)
    pub rendered_ttl: Option<u32>,
    /// Enable caching of ESI include fragment responses (subrequests)
    pub is_includes_cacheable: bool,
    /// Default TTL in seconds for include responses when Cache-Control doesn't specify max-age or s-maxage
    pub includes_default_ttl: Option<u32>,
    /// Force TTL in seconds for includes - overrides all Cache-Control headers and makes everything cacheable
    ///
    /// **Warning:** When set, this will cache ALL responses regardless of Cache-Control headers
    /// (including `private`, `no-cache`, `no-store`) and Set-Cookie headers. Use with caution.
    pub includes_force_ttl: Option<u32>,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            is_rendered_cacheable: false,
            rendered_cache_control: false,
            rendered_ttl: None,
            is_includes_cacheable: true,
            includes_default_ttl: None,
            includes_force_ttl: None,
        }
    }
}

/// Determine if a response is cacheable and calculate its TTL
///
/// Returns Ok(Some(ttl)) if cacheable, Ok(None) if not cacheable
pub fn calculate_ttl(response: &Response, config: &CacheConfig) -> Result<Option<u32>> {
    // If includes_force_ttl is set, everything is cacheable
    if let Some(force_ttl) = config.includes_force_ttl {
        trace!("Using includes_force_ttl: {force_ttl}s");
        return Ok(Some(force_ttl));
    }

    // Check for Set-Cookie header - don't cache responses that set cookies
    if response.get_header(SET_COOKIE).is_some() {
        trace!("Response has Set-Cookie header, not caching");
        return Ok(None);
    }

    // Parse Cache-Control header
    if let Some(cache_control) = response.get_header_str(CACHE_CONTROL) {
        trace!("Parsing Cache-Control: {cache_control}");

        let directives: Vec<&str> = cache_control.split(',').map(str::trim).collect();

        // Check for directives that prevent caching
        for directive in &directives {
            if directive.eq_ignore_ascii_case("private")
                || directive.eq_ignore_ascii_case("no-cache")
                || directive.eq_ignore_ascii_case("no-store")
                || directive.eq_ignore_ascii_case("must-revalidate")
            {
                trace!("Response has {directive} directive, not caching");
                return Ok(None);
            }
        }

        // Look for s-maxage first, then max-age
        let mut ttl = None;
        for directive in &directives {
            if let Some(value) = directive.strip_prefix("s-maxage=") {
                if let Ok(seconds) = value.parse::<u32>() {
                    trace!("Found s-maxage={seconds}");
                    ttl = Some(seconds);
                    break; // s-maxage takes precedence
                }
            }
        }

        // If no s-maxage, look for max-age
        if ttl.is_none() {
            for directive in &directives {
                if let Some(value) = directive.strip_prefix("max-age=") {
                    if let Ok(seconds) = value.parse::<u32>() {
                        trace!("Found max-age={seconds}");
                        ttl = Some(seconds);
                        break;
                    }
                }
            }
        }

        // If we found a TTL, use it
        if let Some(ttl) = ttl {
            return Ok(Some(ttl));
        }
    }

    // No Cache-Control or no max-age/s-maxage, use includes_default_ttl if set
    if let Some(default_ttl) = config.includes_default_ttl {
        trace!("Using includes_default_ttl: {default_ttl}s");
        return Ok(Some(default_ttl));
    }

    // No TTL available, don't cache
    trace!("No TTL available, not caching");
    Ok(None)
}

/// Parse ESI TTL string format (e.g., "120m", "1h", "2d", "0s") into seconds
///
/// Format: integer followed by unit specifier
/// - s: seconds
/// - m: minutes  
/// - h: hours
/// - d: days
///
/// Returns None if the format is invalid
pub fn parse_ttl(ttl_str: &str) -> Option<u32> {
    let ttl_str = ttl_str.trim();
    if ttl_str.is_empty() {
        return None;
    }

    // Find the last digit position
    let mut num_end = 0;
    for (i, &b) in ttl_str.as_bytes().iter().enumerate() {
        if b.is_ascii_digit() {
            num_end = i + 1;
        } else if i > 0 {
            break;
        }
    }

    if num_end == 0 {
        return None;
    }

    let (num_part, unit_part) = ttl_str.split_at(num_end);
    let value = num_part.parse::<u32>().ok()?;

    let multiplier = match unit_part.trim() {
        "s" => 1,
        "m" => 60,
        "h" => 3600,
        "d" => 86400,
        _ => return None,
    };

    Some(value * multiplier)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_calculate_ttl_force() {
        let config = CacheConfig {
            is_rendered_cacheable: true,
            rendered_cache_control: false,
            rendered_ttl: None,
            is_includes_cacheable: true,
            includes_default_ttl: Some(300),
            includes_force_ttl: Some(600),
        };

        let mut resp = Response::new();
        resp.set_header(CACHE_CONTROL, "private, no-cache");
        resp.set_header(SET_COOKIE, "session=abc");

        // force_ttl should override everything
        let ttl = calculate_ttl(&resp, &config).unwrap();
        assert_eq!(ttl, Some(600));
    }

    #[test]
    fn test_calculate_ttl_set_cookie() {
        let config = CacheConfig {
            is_rendered_cacheable: true,
            rendered_cache_control: false,
            rendered_ttl: None,
            is_includes_cacheable: true,
            includes_default_ttl: Some(300),
            includes_force_ttl: None,
        };

        let mut resp = Response::new();
        resp.set_header(SET_COOKIE, "session=abc");

        let ttl = calculate_ttl(&resp, &config).unwrap();
        assert_eq!(ttl, None);
    }

    #[test]
    fn test_calculate_ttl_private() {
        let config = CacheConfig {
            is_rendered_cacheable: true,
            rendered_cache_control: false,
            rendered_ttl: None,
            is_includes_cacheable: true,
            includes_default_ttl: Some(300),
            includes_force_ttl: None,
        };

        let mut resp = Response::new();
        resp.set_header(CACHE_CONTROL, "private, max-age=600");

        let ttl = calculate_ttl(&resp, &config).unwrap();
        assert_eq!(ttl, None);
    }

    #[test]
    fn test_calculate_ttl_no_cache() {
        let config = CacheConfig {
            is_rendered_cacheable: true,
            rendered_cache_control: false,
            rendered_ttl: None,
            is_includes_cacheable: true,
            includes_default_ttl: Some(300),
            includes_force_ttl: None,
        };

        let mut resp = Response::new();
        resp.set_header(CACHE_CONTROL, "no-cache");

        let ttl = calculate_ttl(&resp, &config).unwrap();
        assert_eq!(ttl, None);
    }

    #[test]
    fn test_calculate_ttl_s_maxage() {
        let config = CacheConfig {
            is_rendered_cacheable: true,
            rendered_cache_control: false,
            rendered_ttl: None,
            is_includes_cacheable: true,
            includes_default_ttl: Some(300),
            includes_force_ttl: None,
        };

        let mut resp = Response::new();
        resp.set_header(CACHE_CONTROL, "public, max-age=100, s-maxage=500");

        let ttl = calculate_ttl(&resp, &config).unwrap();
        assert_eq!(ttl, Some(500)); // s-maxage should take precedence
    }

    #[test]
    fn test_calculate_ttl_max_age() {
        let config = CacheConfig {
            is_rendered_cacheable: true,
            rendered_cache_control: false,
            rendered_ttl: None,
            is_includes_cacheable: true,
            includes_default_ttl: Some(300),
            includes_force_ttl: None,
        };

        let mut resp = Response::new();
        resp.set_header(CACHE_CONTROL, "public, max-age=400");

        let ttl = calculate_ttl(&resp, &config).unwrap();
        assert_eq!(ttl, Some(400));
    }

    #[test]
    fn test_calculate_ttl_default() {
        let config = CacheConfig {
            is_rendered_cacheable: true,
            rendered_cache_control: false,
            rendered_ttl: None,
            is_includes_cacheable: true,
            includes_default_ttl: Some(300),
            includes_force_ttl: None,
        };

        let resp = Response::new();

        let ttl = calculate_ttl(&resp, &config).unwrap();
        assert_eq!(ttl, Some(300));
    }

    #[test]
    fn test_calculate_ttl_must_revalidate() {
        let config = CacheConfig {
            is_rendered_cacheable: true,
            rendered_cache_control: false,
            rendered_ttl: None,
            is_includes_cacheable: true,
            includes_default_ttl: Some(300),
            includes_force_ttl: None,
        };

        let mut resp = Response::new();
        resp.set_header(CACHE_CONTROL, "public, max-age=600, must-revalidate");

        let ttl = calculate_ttl(&resp, &config).unwrap();
        assert_eq!(ttl, None); // must-revalidate prevents caching
    }

    #[test]
    fn test_parse_ttl_seconds() {
        assert_eq!(parse_ttl("0s"), Some(0));
        assert_eq!(parse_ttl("30s"), Some(30));
        assert_eq!(parse_ttl("120s"), Some(120));
    }

    #[test]
    fn test_parse_ttl_minutes() {
        assert_eq!(parse_ttl("1m"), Some(60));
        assert_eq!(parse_ttl("5m"), Some(300));
        assert_eq!(parse_ttl("120m"), Some(7200));
    }

    #[test]
    fn test_parse_ttl_hours() {
        assert_eq!(parse_ttl("1h"), Some(3600));
        assert_eq!(parse_ttl("2h"), Some(7200));
        assert_eq!(parse_ttl("24h"), Some(86400));
    }

    #[test]
    fn test_parse_ttl_days() {
        assert_eq!(parse_ttl("1d"), Some(86400));
        assert_eq!(parse_ttl("7d"), Some(604800));
    }

    #[test]
    fn test_parse_ttl_invalid() {
        assert_eq!(parse_ttl(""), None);
        assert_eq!(parse_ttl("invalid"), None);
        assert_eq!(parse_ttl("120x"), None);
        assert_eq!(parse_ttl("s"), None);
        assert_eq!(parse_ttl("m"), None);
    }

    #[test]
    fn test_parse_ttl_whitespace() {
        assert_eq!(parse_ttl(" 120m "), Some(7200));
        assert_eq!(parse_ttl("  1h  "), Some(3600));
    }
}
