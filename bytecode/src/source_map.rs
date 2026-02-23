//! Delta-encoded VLQ source map: maps bytecode PCs to source character ranges.
//!
//! Each entry is 3 VLQ values:
//! - `delta_pc` (unsigned VLQ)
//! - `delta_start` (signed, zigzag + VLQ)
//! - `delta_end` (signed, zigzag + VLQ)
//!
/// Accumulates source map entries during compilation.
pub struct SourceMapBuilder {
    entries: Vec<(u32, u32, u32)>, // (pc, start, end)
}

impl SourceMapBuilder {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Record a mapping from a bytecode offset to a source character range.
    pub fn add(&mut self, pc: u32, start: u32, end: u32) {
        self.entries.push((pc, start, end));
    }

    /// Produce the delta-encoded VLQ byte stream.
    pub fn finish(self) -> Vec<u8> {
        let mut buf = Vec::new();
        let mut prev_pc: u32 = 0;
        let mut prev_start: i64 = 0;
        let mut prev_end: i64 = 0;

        for (pc, start, end) in &self.entries {
            let delta_pc = pc - prev_pc;
            let delta_start = *start as i64 - prev_start;
            let delta_end = *end as i64 - prev_end;

            encode_unsigned_vlq(delta_pc, &mut buf);
            encode_unsigned_vlq(zigzag_encode(delta_start), &mut buf);
            encode_unsigned_vlq(zigzag_encode(delta_end), &mut buf);

            prev_pc = *pc;
            prev_start = *start as i64;
            prev_end = *end as i64;
        }

        buf
    }
}

impl Default for SourceMapBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Look up the source range for `target_pc` in a delta-encoded source map.
/// Returns the `(start, end)` character offsets of the last entry with `pc <= target_pc`.
pub fn source_map_lookup(encoded: &[u8], target_pc: u32) -> Option<(u32, u32)> {
    let mut pos = 0;
    let mut pc: u32 = 0;
    let mut start: i64 = 0;
    let mut end: i64 = 0;
    let mut best: Option<(u32, u32)> = None;

    while pos < encoded.len() {
        let delta_pc = decode_unsigned_vlq(encoded, &mut pos)?;
        let delta_start =
            zigzag_decode(decode_unsigned_vlq(encoded, &mut pos)?);
        let delta_end = zigzag_decode(decode_unsigned_vlq(encoded, &mut pos)?);

        pc += delta_pc;
        start += delta_start;
        end += delta_end;

        if pc > target_pc {
            break;
        }
        best = Some((start as u32, end as u32));
    }

    best
}

// ── VLQ helpers ─────────────────────────────────────────────────────

/// Encode an unsigned integer as a variable-length quantity.
/// Each byte uses 7 data bits + 1 continuation bit (MSB).
fn encode_unsigned_vlq(mut value: u32, buf: &mut Vec<u8>) {
    loop {
        let mut byte = (value & 0x7F) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        buf.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Decode an unsigned VLQ from `encoded` starting at `pos`.
/// Advances `pos` past the consumed bytes.
fn decode_unsigned_vlq(encoded: &[u8], pos: &mut usize) -> Option<u32> {
    let mut result: u32 = 0;
    let mut shift = 0;
    loop {
        if *pos >= encoded.len() {
            return None;
        }
        let byte = encoded[*pos];
        *pos += 1;
        result |= ((byte & 0x7F) as u32) << shift;
        if byte & 0x80 == 0 {
            return Some(result);
        }
        shift += 7;
        if shift >= 35 {
            return None; // overflow
        }
    }
}

/// Zigzag-encode a signed i64 into an unsigned u32.
fn zigzag_encode(value: i64) -> u32 {
    ((value << 1) ^ (value >> 63)) as u32
}

/// Zigzag-decode an unsigned u32 back to a signed i64.
fn zigzag_decode(value: u32) -> i64 {
    ((value >> 1) as i64) ^ (-((value & 1) as i64))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_source_map() {
        let builder = SourceMapBuilder::new();
        let encoded = builder.finish();
        assert!(encoded.is_empty());
        assert_eq!(source_map_lookup(&encoded, 0), None);
    }

    #[test]
    fn single_entry() {
        let mut builder = SourceMapBuilder::new();
        builder.add(0, 10, 20);
        let encoded = builder.finish();
        assert_eq!(source_map_lookup(&encoded, 0), Some((10, 20)));
        assert_eq!(source_map_lookup(&encoded, 5), Some((10, 20)));
    }

    #[test]
    fn multiple_entries() {
        let mut builder = SourceMapBuilder::new();
        builder.add(0, 0, 5);
        builder.add(3, 10, 15);
        builder.add(7, 20, 30);
        let encoded = builder.finish();

        assert_eq!(source_map_lookup(&encoded, 0), Some((0, 5)));
        assert_eq!(source_map_lookup(&encoded, 2), Some((0, 5)));
        assert_eq!(source_map_lookup(&encoded, 3), Some((10, 15)));
        assert_eq!(source_map_lookup(&encoded, 5), Some((10, 15)));
        assert_eq!(source_map_lookup(&encoded, 7), Some((20, 30)));
        assert_eq!(source_map_lookup(&encoded, 100), Some((20, 30)));
    }

    #[test]
    fn zigzag_round_trip() {
        for v in [-1000, -1, 0, 1, 1000, i32::MAX as i64, i32::MIN as i64] {
            assert_eq!(zigzag_decode(zigzag_encode(v)), v);
        }
    }

    #[test]
    fn vlq_round_trip() {
        let values = [0, 1, 127, 128, 16383, 16384, u32::MAX >> 4];
        for &v in &values {
            let mut buf = Vec::new();
            encode_unsigned_vlq(v, &mut buf);
            let mut pos = 0;
            let decoded = decode_unsigned_vlq(&buf, &mut pos).unwrap();
            assert_eq!(decoded, v);
            assert_eq!(pos, buf.len());
        }
    }

    #[test]
    fn typical_size() {
        // A 100-entry source map should be compact
        let mut builder = SourceMapBuilder::new();
        for i in 0..100u32 {
            builder.add(i * 3, i * 10, i * 10 + 5);
        }
        let encoded = builder.finish();
        assert!(encoded.len() < 500);
    }
}
