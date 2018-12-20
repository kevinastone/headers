
use crate::{Error, Header, HeaderName, HeaderValue};
use crate::util::{TryFromValues, UriReference};
use http::{header, Uri};
use std::iter;

/// `Location` header, defined in
/// [RFC7231](http://tools.ietf.org/html/rfc7231#section-7.1.2)
///
/// The `Location` header field is used in some responses to refer to a
/// specific resource in relation to the response.  The type of
/// relationship is defined by the combination of request method and
/// status code semantics.
///
/// # ABNF
///
/// ```text
/// Location = URI-reference
/// ```
///
/// # Example values
/// * `/People.html#tim`
/// * `http://www.example.net/index.html`
///
/// # Examples
///
/// ```
/// # extern crate headers_ext as headers;
/// # extern crate http;
/// use headers::Location;
/// use http::Uri;
/// let loc = Location::from(Uri::from_static("/auth/login"));
/// ```

#[derive(Clone, Debug, PartialEq)]
pub struct Location(UriReference);

impl Location {
    /// Get the uri for this header
    pub fn uri_ref(&self) -> &UriReference {
        &self.0
    }

    /// Try to get an absolute Uri from this header
    pub fn try_uri(&self) -> Option<&Uri> {
        match self.uri_ref() {
            UriReference::Uri(uri) => Some(uri),
            _ => None,
        }
    }
}

impl Header for Location {
    fn name() -> &'static HeaderName {
        &header::LOCATION
    }

    fn decode<'i, I>(values: &mut I) -> Result<Self, Error>
    where
        Self: Sized,
        I: Iterator<Item = &'i HeaderValue>,
    {
        UriReference::try_from_values(values).map(Location)
    }

    fn encode<E: Extend<HeaderValue>>(&self, values: &mut E) {
        values.extend(iter::once((&self.0).into()))
    }
}

impl From<Uri> for Location {
    fn from(uri: Uri) -> Self {
        Location(UriReference::uri(uri))
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_decode;
    use super::*;

    #[test]
    fn absolute_uri() {
        let s = "http://www.example.net/index.html";
        let loc = test_decode::<Location>(&[s]).unwrap();

        assert_eq!(loc, Location(UriReference::uri(Uri::from_static(s))));
    }

    #[test]
    fn relative_uri_with_fragment() {
        let s = "/People.html#tim";
        let loc = test_decode::<Location>(&[s]).unwrap();

        assert_eq!(loc, Location(UriReference::relative("/People.html#tim")));
    }

    #[test]
    fn absolute_uri_with_dot_path() {
        let s = "http://www.example.net/something/../another";
        let loc = test_decode::<Location>(&[s]).unwrap();

        assert_eq!(loc, Location(UriReference::uri(Uri::from_static(s))));
    }

    #[test]
    fn relative_uri_with_dot_path() {
        let s = "../something";
        let loc = test_decode::<Location>(&[s]).unwrap();

        assert_eq!(loc, Location(UriReference::relative("../something")));
    }
}
