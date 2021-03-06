use util::FlatCsv;

/// `Accept-Ranges` header, defined in [RFC7233](http://tools.ietf.org/html/rfc7233#section-2.3)
///
/// The `Accept-Ranges` header field allows a server to indicate that it
/// supports range requests for the target resource.
///
/// # ABNF
///
/// ```text
/// Accept-Ranges     = acceptable-ranges
/// acceptable-ranges = 1#range-unit / \"none\"
///
/// # Example values
/// * `bytes`
/// * `none`
/// * `unknown-unit`
/// ```
///
/// # Examples
/// ```
/// ```
#[derive(Clone, Debug, Header, PartialEq)]
pub struct AcceptRanges(FlatCsv);

impl AcceptRanges {
    /// A constructor to easily create the common `Accept-Ranges: bytes` header.
    pub fn bytes() -> Self {
        AcceptRanges(::HeaderValue::from_static("bytes").into())
    }
}
