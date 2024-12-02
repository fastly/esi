/// This struct is used to configure optional behaviour within the ESI processor.
///
/// ## Usage Example
/// ```rust,no_run
/// let config = esi::Configuration::default()
///     .with_namespace("app");
/// ```
#[allow(clippy::return_self_not_must_use)]
#[derive(Clone, Debug)]
pub struct Configuration {
    // Define the tag names that the processor will operate on.
    pub tag_names: TagNames,
    /// For working with non-HTML ESI templates, e.g. JSON files, this option allows you to disable the unescaping of URLs
    pub is_escaped_content: bool,
}

impl Default for Configuration {
    fn default() -> Self {
        Self {
            tag_names: Default::default(),
            is_escaped_content: true,
        }
    }
}

impl Configuration {
    /// Sets an alternative ESI namespace, which is used to identify ESI instructions.
    ///
    /// For example, setting this to `test` would cause the processor to only match tags like `<test:include>`.
    pub fn with_namespace(mut self, namespace: impl Into<String>) -> Self {
        self.tag_names = TagNames::from_namespace_with_defaults(&namespace.into());
        self
    }
    /// Sets the tag names that the processor will operate on.
    pub fn with_tag_names(mut self, tag_names: TagNames) -> Self {
        self.tag_names = tag_names;
        self
    }
    /// For working with non-HTML ESI templates, eg JSON files, allows to disable URLs unescaping
    pub fn with_escaped(mut self, is_escaped: impl Into<bool>) -> Self {
        self.is_escaped_content = is_escaped.into();
        self
    }
}

/// Defines the HTML tag names that the processor will operate on.
#[derive(Clone, Debug)]
pub struct TagNames {
    pub include: Vec<u8>,
    pub comment: Vec<u8>,
    pub remove: Vec<u8>,
    pub r#try: Vec<u8>,
    pub attempt: Vec<u8>,
    pub except: Vec<u8>,
}

impl TagNames {
    /// Returns tag names as defined within the ESI specification within the given namespace.
    pub fn from_namespace_with_defaults(namespace: &str) -> Self {
        Self {
            include: format!("{namespace}:include",).into_bytes(),
            comment: format!("{namespace}:comment",).into_bytes(),
            remove: format!("{namespace}:remove",).into_bytes(),
            r#try: format!("{namespace}:try",).into_bytes(),
            attempt: format!("{namespace}:attempt",).into_bytes(),
            except: format!("{namespace}:except",).into_bytes(),
        }
    }
}

impl Default for TagNames {
    fn default() -> Self {
        Self::from_namespace_with_defaults("esi")
    }
}
