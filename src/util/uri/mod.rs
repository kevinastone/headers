mod parse;

use crate::{Error, HeaderValue};
use super::HeaderValueString;
use http::Uri;
use std::str::FromStr;
use std::fmt;
use crate::util::TryFromValues;
use super::iter::IterExt;
use std::ops::Range;
use self::parse::*;

#[derive(Debug, Clone, PartialEq)]
pub enum UriReference {
    Uri(Uri),
    Relative(RelativeRef)
}

impl UriReference {
    pub fn uri<T: Into<Uri>>(uri: T) -> Self {
        UriReference::Uri(uri.into())
    }

    pub fn relative<T: Into<RelativeRef>>(relative: T) -> Self {
        UriReference::Relative(relative.into())
    }
}

impl From<&UriReference> for HeaderValue {
    fn from(uri_ref: &UriReference) -> Self {
        match uri_ref {
            UriReference::Uri(uri) => uri.to_string().parse().unwrap(),
            UriReference::Relative(relative) => relative.into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RelativeRef {
    serialization: HeaderValueString,
    authority: Option<Range<usize>>,
    path: Range<usize>,
    query: Option<Range<usize>>,
    fragment: Option<Range<usize>>,
}

impl RelativeRef {
    pub fn from_static(s: &'static str) -> Self {
        s.parse::<RelativeRef>().unwrap()
    }

    pub fn authority(&self) -> Option<&str> {
        self.authority.clone().map(|r| &self.serialization.as_str()[r])
    }

    pub fn path(&self) -> &str {
        &self.serialization.as_str()[self.path.clone()]
    }

    pub fn query(&self) -> Option<&str> {
        self.query.clone().map(|r| &self.serialization.as_str()[r])
    }

    pub fn fragment(&self) -> Option<&str> {
        self.fragment.clone().map(|r| &self.serialization.as_str()[r])
    }
}

impl fmt::Display for RelativeRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(authority) = self.authority() {
            f.write_str(authority)?;
        }

        f.write_str(self.path())?;

        if let Some(query) = self.query() {
            f.write_str(query)?;
        }

        if let Some(fragment) = self.fragment() {
            f.write_str(fragment)?;
        }

        Ok(())
    }
}

impl From<&'static str> for RelativeRef {
    fn from(s: &'static str) -> Self {
        RelativeRef::from_static(s)
    }
}

impl From<&RelativeRef> for HeaderValue {
    fn from(relative_ref: &RelativeRef) -> Self {
        relative_ref.to_string().parse().unwrap()
    }
}

impl FromStr for RelativeRef {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut idx = 0;

        let authority = match parse_authority(s) {
            None => None,
            Some(range) => {
                idx = range.end;
                Some(range)
            }
        };

        let path_idx = parse_path(&s[idx..]);
        let path = (path_idx.start+idx)..(path_idx.end+idx);
        idx = path.end;

        let query = match parse_query(&s[idx..]) {
            None => None,
            Some(range) => {
                let range = range.start+idx..range.end+idx;
                idx += range.end;
                Some(range)
            }
        };

        let fragment = match parse_fragment(&s[idx..]) {
            None => None,
            Some(range) => {
                Some(range.start+idx..range.end+idx)
            }
        };

        Ok(RelativeRef {
            serialization: s.parse().map_err(|_| Error::invalid())?,
            authority,
            path,
            query,
            fragment,
        })
    }
}

impl FromStr for UriReference {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(_) = parse_scheme(s) {
            s.parse::<Uri>().map(UriReference::Uri).map_err(|_| Error::invalid())
        } else {
            s.parse::<RelativeRef>().map(UriReference::Relative).map_err(|_| Error::invalid())
        }
    }
}

impl TryFromValues for UriReference {
    fn try_from_values<'i, I>(values: &mut I) -> Result<Self, Error>
    where
        I: Iterator<Item = &'i HeaderValue>,
    {
        let header_string = values.just_one().ok_or_else(Error::invalid)?.to_str().map_err(|_| Error::invalid())?;
        header_string.parse::<UriReference>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_scheme() {
        assert!(parse_scheme("http://example.com").is_some());
        assert!(parse_scheme("https://example.com").is_some());
        assert!(parse_scheme("file:///etc/hosts").is_some());
        assert!(parse_scheme("git+https://example.com").is_some());
        assert!(parse_scheme("git-fs://example.com").is_some());
    }

    #[test]
    fn test_not_parse_scheme() {
        assert!(parse_scheme("/something").is_none());
        assert!(parse_scheme("../something").is_none());
        assert!(parse_scheme("something/another").is_none());
        assert!(parse_scheme("//example.com").is_none());
        assert!(parse_scheme("example.com").is_none());
        assert!(parse_scheme("_error").is_none());
        assert!(parse_scheme("😎").is_none());
    }

    #[test]
    fn test_parse_relative() {
        let s = "../something";
        assert_eq!(s.parse::<UriReference>().unwrap(), UriReference::relative(s))
    }

    #[test]
    fn test_parse_relative_parts() {
        let s = "../something";
        let uri_ref = s.parse::<RelativeRef>().unwrap();
        assert_eq!(uri_ref.authority(), None);
        assert_eq!(uri_ref.path(), s);
        assert_eq!(uri_ref.query(), None);
        assert_eq!(uri_ref.fragment(), None);
    }

    #[test]
    fn test_parse_absolute() {
        let s = "http://example.com/first?second=third#fourth";
        assert_eq!(s.parse::<UriReference>().unwrap(), UriReference::uri(Uri::from_static(s)))
    }
}
