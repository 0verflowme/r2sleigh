//! Deterministic argument accounting for printf-family format literals.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PrintfFormatRefusal {
    UnterminatedSpecifier,
    UnsupportedConversion,
    InvalidPosition,
    MixedPositionalAndSequential,
    CountOverflow,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArgumentMode {
    Unknown,
    Sequential,
    Positional,
}

fn decimal(bytes: &[u8], cursor: &mut usize) -> Result<Option<usize>, PrintfFormatRefusal> {
    let start = *cursor;
    let mut value = 0usize;
    while let Some(digit) = bytes.get(*cursor).copied().filter(u8::is_ascii_digit) {
        value = value
            .checked_mul(10)
            .and_then(|value| value.checked_add(usize::from(digit - b'0')))
            .ok_or(PrintfFormatRefusal::CountOverflow)?;
        *cursor += 1;
    }
    Ok((*cursor != start).then_some(value))
}

fn positional_index(
    bytes: &[u8],
    cursor: &mut usize,
) -> Result<Option<usize>, PrintfFormatRefusal> {
    let start = *cursor;
    let Some(position) = decimal(bytes, cursor)? else {
        return Ok(None);
    };
    if bytes.get(*cursor) != Some(&b'$') {
        *cursor = start;
        return Ok(None);
    }
    *cursor += 1;
    position
        .checked_sub(1)
        .map(Some)
        .ok_or(PrintfFormatRefusal::InvalidPosition)
}

fn consume_argument(
    position: Option<usize>,
    mode: &mut ArgumentMode,
    sequential_count: &mut usize,
    largest_position: &mut Option<usize>,
) -> Result<(), PrintfFormatRefusal> {
    match position {
        Some(position) => {
            if *mode == ArgumentMode::Sequential {
                return Err(PrintfFormatRefusal::MixedPositionalAndSequential);
            }
            *mode = ArgumentMode::Positional;
            *largest_position = Some(largest_position.map_or(position, |old| old.max(position)));
        }
        None => {
            if *mode == ArgumentMode::Positional {
                return Err(PrintfFormatRefusal::MixedPositionalAndSequential);
            }
            *mode = ArgumentMode::Sequential;
            *sequential_count = sequential_count
                .checked_add(1)
                .ok_or(PrintfFormatRefusal::CountOverflow)?;
        }
    }
    Ok(())
}

/// Count the arguments consumed by a complete printf-family format literal.
///
/// Escaped `%%` consumes nothing; `*` width and precision each consume one;
/// flags, widths, precisions, and length modifiers remain part of one
/// conversion. POSIX positional operands are accepted only when every
/// consuming operand is positional.
pub(crate) fn printf_consumed_argument_count(format: &str) -> Result<usize, PrintfFormatRefusal> {
    let bytes = format.as_bytes();
    let mut cursor = 0usize;
    let mut mode = ArgumentMode::Unknown;
    let mut sequential_count = 0usize;
    let mut largest_position = None;

    while cursor < bytes.len() {
        if bytes[cursor] != b'%' {
            cursor += 1;
            continue;
        }
        cursor += 1;
        if bytes.get(cursor) == Some(&b'%') {
            cursor += 1;
            continue;
        }

        let conversion_position = positional_index(bytes, &mut cursor)?;
        while bytes
            .get(cursor)
            .is_some_and(|byte| b"#0- +'I".contains(byte))
        {
            cursor += 1;
        }

        if bytes.get(cursor) == Some(&b'*') {
            cursor += 1;
            let width_position = positional_index(bytes, &mut cursor)?;
            consume_argument(
                width_position,
                &mut mode,
                &mut sequential_count,
                &mut largest_position,
            )?;
        } else {
            let _ = decimal(bytes, &mut cursor)?;
        }

        if bytes.get(cursor) == Some(&b'.') {
            cursor += 1;
            if bytes.get(cursor) == Some(&b'*') {
                cursor += 1;
                let precision_position = positional_index(bytes, &mut cursor)?;
                consume_argument(
                    precision_position,
                    &mut mode,
                    &mut sequential_count,
                    &mut largest_position,
                )?;
            } else {
                let _ = decimal(bytes, &mut cursor)?;
            }
        }

        if matches!(
            bytes.get(cursor..cursor.saturating_add(2)),
            Some(b"hh" | b"ll")
        ) {
            cursor += 2;
        } else if bytes
            .get(cursor)
            .is_some_and(|byte| b"hljztLqZ".contains(byte))
        {
            cursor += 1;
        }

        let conversion = bytes
            .get(cursor)
            .copied()
            .ok_or(PrintfFormatRefusal::UnterminatedSpecifier)?;
        cursor += 1;
        match conversion {
            b'd' | b'i' | b'o' | b'u' | b'x' | b'X' | b'f' | b'F' | b'e' | b'E' | b'g' | b'G'
            | b'a' | b'A' | b'c' | b'C' | b's' | b'S' | b'p' | b'n' | b'b' | b'B' => {
                consume_argument(
                    conversion_position,
                    &mut mode,
                    &mut sequential_count,
                    &mut largest_position,
                )?
            }
            // GNU printf's strerror conversion consumes no operand.
            b'm' if conversion_position.is_none() => {}
            _ => return Err(PrintfFormatRefusal::UnsupportedConversion),
        }
    }

    match mode {
        ArgumentMode::Unknown | ArgumentMode::Sequential => Ok(sequential_count),
        ArgumentMode::Positional => largest_position
            .and_then(|position| position.checked_add(1))
            .ok_or(PrintfFormatRefusal::InvalidPosition),
    }
}

#[cfg(test)]
mod tests {
    use super::{PrintfFormatRefusal, printf_consumed_argument_count};

    #[test]
    fn counts_conversion_operands_instead_of_percent_bytes() {
        assert_eq!(printf_consumed_argument_count("done: 100%%").unwrap(), 0);
        assert_eq!(printf_consumed_argument_count("%08.3lld %s").unwrap(), 2);
        assert_eq!(printf_consumed_argument_count("%*.*f").unwrap(), 3);
        assert_eq!(printf_consumed_argument_count("%m").unwrap(), 0);
    }

    #[test]
    fn positional_operands_count_distinct_argument_slots() {
        assert_eq!(printf_consumed_argument_count("%2$*1$d %2$d").unwrap(), 2);
        assert_eq!(
            printf_consumed_argument_count("%1$d %d"),
            Err(PrintfFormatRefusal::MixedPositionalAndSequential)
        );
    }

    #[test]
    fn malformed_or_unknown_specifiers_refuse() {
        assert_eq!(
            printf_consumed_argument_count("value %"),
            Err(PrintfFormatRefusal::UnterminatedSpecifier)
        );
        assert_eq!(
            printf_consumed_argument_count("%Q"),
            Err(PrintfFormatRefusal::UnsupportedConversion)
        );
    }
}
