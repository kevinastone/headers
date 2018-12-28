use std::ops::Range;

pub(super) fn parse_scheme(s: &str) -> Option<Range<usize>> {
    let mut stream = s.chars().enumerate();
    if stream.next().filter(|c| c.1.is_ascii_alphabetic()).is_none() {
        return None;
    }

    for (idx, ch) in stream {
        match ch {
            'a'...'z' | 'A'...'Z' | '0'...'9' | '+' | '-' | '.' => continue,
            ':' => return Some(0..idx),
            _ => break
        }
    }

    None
}

fn parse_pct_encoded<T>(iter: &mut T) -> Option<u8>
    where T: Iterator<Item=(usize, char)>
 {
    let mut iter = iter.map(|(_, ch)| ch);

    let mut ch = iter.next().and_then(|ch| ch.to_digit(16))? as u8;
    ch <<= 4;
    ch = ch.checked_add(iter.next().and_then(|ch| ch.to_digit(16))? as u8)?;
    println!("Pct Encoded {:?}", ch);
    Some(ch)
}

pub(super) fn parse_userinfo(s: &str) -> Option<Range<usize>> {
    let mut stream = s.chars().enumerate();

    while let Some((idx, ch)) = stream.next() {
        let _ = match ch {
            'a'...'z' | 'A'...'Z' | '0'...'9' | '-' | '.' | '_' | '~' => continue,  // Unreserved
            '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | ';' | '=' => continue, // Sub-delims
            ':' => continue, // Colon
            '@' => return Some(0..idx),
            '%' => parse_pct_encoded(&mut stream)?,
            _ => return None
        };
    }

    None
}

pub(super) fn parse_regname(s: &str) -> Option<Range<usize>> {
    let mut stream = s.chars().enumerate();

    while let Some((idx, ch)) = stream.next() {
        let _ = match ch {
            'a'...'z' | 'A'...'Z' | '0'...'9' | '-' | '.' | '_' | '~' => continue,  // Unreserved
            '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | ';' | '=' => continue, // Sub-delims
            '%' => parse_pct_encoded(&mut stream)?,
            ':' => return Some(0..idx),
            _ => return None
        };
    }

    Some(0..s.len())
}

fn parse_dec_octet(s: &[u8]) -> Result<Option<u8>, ()>
 {
    match s.len() {
        1 => match s[0] {
            b'0' ... b'9' => Ok(Some(s[0] - b'0')),
            _ => Ok(None),
        },
        2 => match (s[0], s[1]) {
            (b'1' ... b'9', b'0' ... b'9') => Ok(Some((s[1] - b'0') * 10 + s[0] - b'0')),
            (b'0' ... b'9', b'0' ... b'9') => Err(()),
            _ => Ok(None),
        },
        3 => match (s[0], s[1], s[2]) {
            (b'1', b'0' ... b'9', b'0' ... b'9') => Ok(Some(100 + (s[1] - b'0') * 10 + (s[0] - b'0'))),
            (b'2', b'0' ... b'4', b'0' ... b'9') => Ok(Some(200 + (s[1] - b'0') * 10 + (s[0] - b'0'))),
            (b'2', b'5', b'0' ... b'5') => Ok(Some(250 + (s[0] - b'0'))),
            (b'0' ... b'9', b'0' ... b'9', b'0' ... b'9') => Err(()),
            _ => Ok(None),
        }
        _ => Ok(None),
    }
}

/// https://url.spec.whatwg.org/#ipv4-number-parser
pub(super) fn parse_ipv4(s: &str) -> Result<Option<Range<usize>>, ()> {

    let s = s.splitn(2, |ch| ch == ':' || ch == '/').next().unwrap();

    if s.is_empty() {
        return Ok(None)
    }

    let mut parts: Vec<_> = s.split('.').collect();
    if parts.last() == Some(&"") {
        parts.pop();
    }

    if parts.len() > 4 {
        return Ok(None);
    }

    for part in parts {
        match parse_dec_octet(part.as_bytes())? {
            Some(_) => continue,
            None => return Ok(None),
        };
    }

    Ok(Some(0..s.len()))
}

fn parse_authority_section(s: &str) -> Option<Range<usize>> {

    let mut stream = s.chars().enumerate();
    // Check for the leading the '//'
    if stream.next().map(|(_, c)| c) != Some('/') { return None }
    if stream.next().map(|(_, c)| c) != Some('/') { return None }

    for (idx, ch) in stream {
        match ch {
            '/' | '?' | '#' => return Some(2..idx),
            _ => continue
        }
    }

    Some(2..s.len())
}

pub(super) fn parse_authority(s: &str) -> Option<Range<usize>> {
    parse_authority_section(s).and_then(|r| {
        let s = &s[r.clone()];

        match parse_ipv4(s) {
            Err(_) => return None,
            Ok(value) => value,
        }.or_else(|| parse_regname(s)).map(|_| r)
    })
}

pub(super) fn parse_path(s: &str) -> Range<usize> {
    let stream = s.chars().enumerate();

    for (idx, ch) in stream {
        match ch {
            '?' | '#' => return 0..idx,
            _ => continue
        }
    }

    0..s.len()
}

pub(super) fn parse_query(s: &str) -> Option<Range<usize>> {
    let mut stream = s.chars().enumerate();

    if stream.next() != Some((0, '?')) {
        return None
    }

    for (idx, ch) in stream {
        match ch {
            '#' => return Some(0..idx),
            _ => continue
        }
    }

    Some(0..s.len())
}

pub(super) fn parse_fragment(s: &str) -> Option<Range<usize>> {
    let mut stream = s.chars().enumerate();

    if stream.next() != Some((0, '#')) {
        return None
    }

    Some(0..s.len())
}


#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_parse {
        ($parser:ident(
            $($input:expr => $output:expr,)*
        )) => {
            $(
                assert_eq!($parser($input).map(|range| &$input[range]), Some($output), "failed to properly parse {}", $input);
            )*
        }
    }

    macro_rules! assert_not_parse {
        ($parser:ident(
            $($input:expr,)*
        )) => {
            $(
                assert_eq!($parser($input).map(|range| &$input[range]), None, "failed to properly parse {}", $input);
            )*
        }
    }

    #[test]
    fn test_parse_scheme() {
        assert_parse! {
            parse_scheme(
                "http://example.com" => "http",
                "https://example.com" => "https",
                "file:///etc/hosts" => "file",
                "git+https://example.com" => "git+https",
                "coap+ws://example.com/path?query" => "coap+ws",
                "chrome-extension://mgijmajocgfcbeboacabfaaabmjgjcoja/options.html" => "chrome-extension",
                "xmlrpc.beep://stateserver.example.com/NumberToName" => "xmlrpc.beep",
                "z39.50s://melvyl.ucop.edu/cat" => "z39.50s",
            )
        }

        assert_not_parse! {
            parse_scheme(
                "/something",
                "../something",
                "something/another",
                "//example.com",
                "example.com",
                "_error",
                "😎",
            )
        }
    }

    #[test]
    fn test_parse_authority() {
        assert_parse! {
            parse_authority(
                "//example.com" => "example.com",
                "//example.com:1234" => "example.com:1234",
                "//example.com/" => "example.com",
                "//example.com/whatever?query" => "example.com",
                "///etc/hosts" => "",
                "//user:passwd@example.com/whatever" => "user:passwd@example.com",
                "//user:passwd@example.com:6789/whatever" => "user:passwd@example.com:6789",
                // IPV4
                "//127.0.0.1/whatever" => "127.0.0.1",
                "//255.255.255.255" => "255.255.255.255",
                "//1.2.3.4" => "1.2.3.4",
                // // IPV6
                // "//[FEDC:BA98:7654:3210:FEDC:BA98:7654:3210]:80/index.html" => "[FEDC:BA98:7654:3210:FEDC:BA98:7654:3210]:80",
                // "//[1080:0:0:0:8:800:200C:417A]/index.html" => "[1080:0:0:0:8:800:200C:417A]",
                // "//[3ffe:2a00:100:7031::1]" => "[3ffe:2a00:100:7031::1]",
                // "//[1080::8:800:200C:417A]/foo" => "[1080::8:800:200C:417A]",
                // "//[::192.9.5.5]/ipng" => "[::192.9.5.5]",
                // "//[::FFFF:129.144.52.38]:80/index.html" => "[::FFFF:129.144.52.38]:80",
                // "//[2010:836B:4179::836B:4179]" => "[2010:836B:4179::836B:4179]",
            )
        }

        assert_not_parse! {
            parse_authority(
                "/something",
                "../something",
                "example.com",
                "something/another",
                "_error",
                "😎",
                // IPV4
                "//256.255.255.255",
                "//999.0.1.2",
                "//1.2.3.04",
            )
        }
    }

    #[test]
    fn test_parse_userinfo() {
        assert_parse! {
            parse_userinfo(
                "user@example.com" => "user",
                "user:passwd@example.com" => "user:passwd",
                "user%2Falice:passwd@example.com" => "user%2Falice:passwd",
                ":secret@example.com" => ":secret",
                "%00%01%09%0A%0D%1F%20!%22%23$&'()*+,-.%2F09%3A%3B%3C%3D%3E%3F%40AZ%5B%5C%5D%5E_%60az%7B%7C%7D~%7F%C2%80%C2%81%C3%89%C3%A9@example.com/" => "%00%01%09%0A%0D%1F%20!%22%23$&'()*+,-.%2F09%3A%3B%3C%3D%3E%3F%40AZ%5B%5C%5D%5E_%60az%7B%7C%7D~%7F%C2%80%C2%81%C3%89%C3%A9",
                "%C3%89t%C3%A9@example.com/" => "%C3%89t%C3%A9",
            )
        }

        assert_not_parse! {
            parse_userinfo(
                "something",
                "user%2_alice:passwd@example.com",
                "user%",
                "user%$",
            )
        }
    }

    #[test]
    fn test_parse_ipv4() {
        let parse_ipv4_with_option = |s: &str| parse_ipv4(s).ok().and_then(|o| o);

        assert_parse! {
            parse_ipv4_with_option(
                "127.0.0.1" => "127.0.0.1",
                "127.0.0.1:8000" => "127.0.0.1",
                "127" => "127",
                "1.2.3.4" => "1.2.3.4",
                "1.0.0.1" => "1.0.0.1",
                "127.1" => "127.1",
                "127.1." => "127.1.",
                "127.0.0.1." => "127.0.0.1.",
            )
        }

        assert_not_parse! {
            parse_ipv4_with_option(
                "something",
                "user%2alice:passwd@example.com",
                "user%",
                "user%$",
            )
        }
    }

    #[test]
    fn test_parse_dec_octet() {
        for input in vec![
            "0",
            "1",
            "9",
            "10",
            "99",
            "100",
            "127",
            "200",
            "240",
            "255",
        ] {
            assert!(parse_dec_octet(input.as_bytes()).ok().and_then(|o| o).is_some(), "failed to parse: {}", input);
        }

        for input in vec![
            "00",
            "000",
            "01",
            "009",
            "010",
            "256",
            "300",
            "999",
        ] {
            assert!(parse_dec_octet(input.as_bytes()).is_err(), "should have failed to parse: {}", input);
        }

        for input in vec![
            "",
            "A",
            "0A",
            "aaa",
            "x",
            "_",
            "+",
            "2000",
            "0100",
        ] {
            assert!(parse_dec_octet(input.as_bytes()).unwrap().is_none(), "should have failed to parse: {}", input);
        }
    }

    #[test]
    fn test_parse_regname() {
        assert_parse! {
            parse_regname(
                "example.com" => "example.com",
                "example.com:8080" => "example.com",
                "%C3%9F" => "%C3%9F",
            )
        }

        assert_not_parse! {
            parse_regname(
                "example%",
                "example%$",
                "../something",
            )
        }
    }

    #[test]
    fn test_path() {
        let parse_path_with_option = |s: &str| Some(parse_path(s));

        assert_parse! {
            parse_path_with_option(
                "g" => "g",
                "g?y/./x" => "g",
                "g?y/../x" => "g",
                "g?y#s" => "g",
                "g#s" => "g",
                "g#s/./x" => "g",
                "g#s/../x" => "g",
                "./../g" => "./../g",
                "./g/." => "./g/.",
                "g/./h" => "g/./h",
                "g/../h" => "g/../h",
                "g;x=1/./y" => "g;x=1/./y",
                "g;x=1/../y" => "g;x=1/../y",
                "/./g" => "/./g",
                "/../g" => "/../g",
                "g." => "g.",
                ".g" => ".g",
                "g." => "g.",
                "..g" => "..g",
                "../../../g" => "../../../g",
                "../../../../g" => "../../../../g",
            )
        }
    }

    #[test]
    fn test_query() {
        assert_parse! {
            parse_query(
                "?y" => "?y",
                "?y#z" => "?y",
                "?y#z?" => "?y",
                "?x=y&w=z" => "?x=y&w=z",
                "?x;y&z" => "?x;y&z",
                "??" => "??",
                "?x?" => "?x?",
                "??#?" => "??",
                "?x?#?" => "?x?",
            )
        }
    }
}
