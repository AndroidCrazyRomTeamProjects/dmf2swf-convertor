// Convert the uncompressed DMF container used by LGUI-SWFDMF.dll to SWF.
//
// ============================================================================
// REVERSE ENGINEERING & CONVERSION FINDINGS (from trace.json, LGUI-SWFDMF.dll,
// and FXGeneratorLib.dll):
// ============================================================================
//
// 1. CONTAINER LAYOUT:
//    - DMF offset 0..3    : "DMF\t" container magic.
//    - DMF offset 4..7    : Little-endian uint32 declared payload/file size.
//    - DMF offset 8..19   : SWF movie header fields (Frame size RECT bitfield,
//                           frame rate UI16, frame count UI16).
//    - DMF offset 20..102 : DMF-only metadata / reserved area (83 bytes).
//    - DMF offset 103..end: Standard SWF tag stream, starting with FileAttributes
//                           (tag 69) at offset 103, followed by Metadata,
//                           SetBackgroundColor, etc.
//
// 2. THE DMF PROPRIETARY IMAGE TAG: TAG 570 (0x23A):
//    - In standard SWF files, images are stored in tags such as:
//        * Tag 20 (0x14): DefineBitsLossless
//        * Tag 36 (0x24): DefineBitsLossless2
//    - In DMF files, LG replaced all lossless image tags with proprietary Tag 570:
//        * In tag header: tag_type = 570 (0x23a).
//        * Header encoding: tag_hdr = (570 << 6) | 0x3f (0x8ebf), followed by
//          32-bit little-endian tag length.
//        * Tag payload:
//            - Offset 0..1 : Character ID (uint16_t LE).
//            - Offset 2..4 : Compression magic: "UCL" (0x55, 0x43, 0x4c) or "LZO".
//            - Offset 5    : Method byte (0x02 = Direct Color, 0x03 = Indexed Palette).
//            - Offset 6    : Format byte (0x01 = Direct, 0x00 = Indexed).
//            - Offset 7..8 : Width (uint16_t LE).
//            - Offset 9..10: Height (uint16_t LE).
//            - Offset 11   : Extra / Palette count:
//                            * Method 2: 0.
//                            * Method 3: (palette_entries - 1), so palette has (byte11 + 1) colors.
//            - Offset 12.. : Compressed image data stream.
//
// 3. COMPRESSION ALGORITHM (UCL NRV2B):
//    - Reverse-engineered from FXGeneratorLib.dll at RVA 0x52d50:
//      The decompression algorithm is UCL's nrv2b_decompress_8 (bit-level NRV2B
//      with byte-level matches and M_OFF > 0x500 length adjustment).
//
// 4. COLOR FORMATS IN DMF:
//    - Method 2 (Direct Color):
//      Decompressed payload consists of 16-bit Big-Endian RGB565 pixels:
//        uint16_t v = (byte0 << 8) | byte1;
//        Red   = ((v >> 11) & 0x1F) * 255 / 31;
//        Green = ((v >> 5)  & 0x3F) * 255 / 63;
//        Blue  = (v & 0x1F)        * 255 / 31;
//      * If total decompressed bytes == width * height * 2 (e.g. cid 1 wallpaper):
//        Image has no alpha channel. Converted to SWF Tag 20 (DefineBitsLossless).
//      * If total decompressed bytes == width * height * 3 (e.g. cid 14, 16):
//        Each pixel has 2 bytes of RGB565 followed by 1 byte of Alpha.
//        Converted to SWF Tag 36 (DefineBitsLossless2) with premultiplied alpha.
//
//    - Method 3 (Indexed Palette):
//      Decompressed payload consists of:
//        * Palette: (palette_entries) * 3 bytes.
//          Each palette entry is: [RGB565_hi, RGB565_lo, Alpha].
//        * Pixel indices: (width * height) bytes of 8-bit palette indices
//          (or 4-bit indices if palette_entries <= 16).
//
// ============================================================================

#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <string>
#include <vector>
#include <algorithm>
#include <cstring>
#include <cstdlib>

#define SDEFL_IMPLEMENTATION
#include "sdefl.h"

namespace {

struct ConvertOptions {
    bool compress_images = false;
    bool cws_container = false;
    int compression_level = 6;
};

constexpr std::size_t kDmfHeaderSize = 120;
constexpr std::size_t kMovieHeaderStart = 8;
constexpr std::size_t kMovieHeaderSize = 12;
constexpr std::size_t kTagStreamStart = 103;

// ----------------------------------------------------------------------------
// Adler-32 Checksum for zlib wrapper
// ----------------------------------------------------------------------------
std::uint32_t adler32(const std::uint8_t* data, std::size_t len) {
    constexpr std::uint32_t kModAdler = 65521;
    std::uint32_t a = 1, b = 0;
    while (len > 0) {
        std::size_t tlen = len > 5552 ? 5552 : len;
        len -= tlen;
        while (tlen-- > 0) {
            a += *data++;
            b += a;
        }
        a %= kModAdler;
        b %= kModAdler;
    }
    return (b << 16) | a;
}

// ----------------------------------------------------------------------------
// Wrap uncompressed data in a standard RFC 1950 / RFC 1951 zlib stream using
// non-compressed Deflate blocks (BTYPE = 00). 100% compliant with Flash Player.
// ----------------------------------------------------------------------------
void zlib_compress_store(const std::vector<std::uint8_t>& in, std::vector<std::uint8_t>& out) {
    out.clear();
    // zlib header: CMF = 0x78 (deflate, 32K window), FLG = 0x01 (check bits)
    out.push_back(0x78);
    out.push_back(0x01);

    std::size_t offset = 0;
    const std::size_t total = in.size();

    if (total == 0) {
        // Single empty final block
        out.push_back(0x01); // BFINAL = 1, BTYPE = 00
        out.push_back(0x00);
        out.push_back(0x00);
        out.push_back(0xff);
        out.push_back(0xff);
    } else {
        while (offset < total) {
            std::size_t block_len = std::min<std::size_t>(total - offset, 65535);
            bool is_final = (offset + block_len == total);
            out.push_back(is_final ? 0x01 : 0x00);

            out.push_back(static_cast<std::uint8_t>(block_len & 0xff));
            out.push_back(static_cast<std::uint8_t>((block_len >> 8) & 0xff));

            std::uint16_t nlen = static_cast<std::uint16_t>(~block_len);
            out.push_back(static_cast<std::uint8_t>(nlen & 0xff));
            out.push_back(static_cast<std::uint8_t>((nlen >> 8) & 0xff));

            out.insert(out.end(), in.begin() + offset, in.begin() + offset + block_len);
            offset += block_len;
        }
    }

    // Append 32-bit Adler checksum (big endian)
    std::uint32_t checksum = adler32(in.data(), in.size());
    out.push_back(static_cast<std::uint8_t>((checksum >> 24) & 0xff));
    out.push_back(static_cast<std::uint8_t>((checksum >> 16) & 0xff));
    out.push_back(static_cast<std::uint8_t>((checksum >> 8) & 0xff));
    out.push_back(static_cast<std::uint8_t>(checksum & 0xff));
}

// ----------------------------------------------------------------------------
// Lossless zlib DEFLATE compression using sdefl (RFC 1950 / RFC 1951)
// ----------------------------------------------------------------------------
void zlib_compress_deflate(const std::vector<std::uint8_t>& in,
                           std::vector<std::uint8_t>& out,
                           int level = 6) {
    out.clear();
    if (in.empty()) {
        zlib_compress_store(in, out);
        return;
    }

    std::uint8_t cmf = 0x78;
    std::uint8_t flg = 0x9c;
    if (level <= 1) flg = 0x01;
    else if (level <= 5) flg = 0x5e;
    else if (level <= 6) flg = 0x9c;
    else flg = 0xda;

    std::uint16_t hdr_val = (static_cast<std::uint16_t>(cmf) << 8) | flg;
    flg += static_cast<std::uint8_t>((31 - (hdr_val % 31)) % 31);

    out.push_back(cmf);
    out.push_back(flg);

    int bound = sdefl_bound(static_cast<int>(in.size()));
    std::size_t header_size = out.size();
    out.resize(header_size + bound);

    struct sdefl s;
    std::memset(&s, 0, sizeof(s));
    int comp_len = sdeflate(&s, out.data() + header_size, in.data(), static_cast<int>(in.size()), level);
    if (comp_len <= 0) {
        zlib_compress_store(in, out);
        return;
    }
    out.resize(header_size + comp_len);

    std::uint32_t checksum = adler32(in.data(), in.size());
    out.push_back(static_cast<std::uint8_t>((checksum >> 24) & 0xff));
    out.push_back(static_cast<std::uint8_t>((checksum >> 16) & 0xff));
    out.push_back(static_cast<std::uint8_t>((checksum >> 8) & 0xff));
    out.push_back(static_cast<std::uint8_t>(checksum & 0xff));
}

void zlib_compress(const std::vector<std::uint8_t>& in,
                   std::vector<std::uint8_t>& out,
                   bool deflate,
                   int level = 6) {
    if (deflate) {
        zlib_compress_deflate(in, out, level);
    } else {
        zlib_compress_store(in, out);
    }
}

// ----------------------------------------------------------------------------
// Compress FWS SWF container into CWS SWF container (SWF 6+ specification)
// ----------------------------------------------------------------------------
bool compress_swf_to_cws(const std::vector<std::uint8_t>& fws_swf,
                         std::vector<std::uint8_t>& cws_swf,
                         int level = 6) {
    if (fws_swf.size() < 8) return false;
    cws_swf.clear();
    cws_swf.push_back('C');
    cws_swf.push_back('W');
    cws_swf.push_back('S');
    cws_swf.push_back(fws_swf[3]); // SWF version

    // Uncompressed file length from FWS header (bytes 4..7)
    cws_swf.insert(cws_swf.end(), fws_swf.begin() + 4, fws_swf.begin() + 8);

    // Compress SWF body from byte 8 to EOF
    std::vector<std::uint8_t> body(fws_swf.begin() + 8, fws_swf.end());
    std::vector<std::uint8_t> compressed_body;
    zlib_compress_deflate(body, compressed_body, level);

    cws_swf.insert(cws_swf.end(), compressed_body.begin(), compressed_body.end());
    return true;
}

// ----------------------------------------------------------------------------
// UCL NRV2B Decompressor (Reverse-engineered from FXGeneratorLib.dll RVA 0x52D50)
// ----------------------------------------------------------------------------
bool ucl_nrv2b_decompress_8(const std::uint8_t* src, std::size_t src_len,
                           std::vector<std::uint8_t>& dst) {
    dst.clear();
    std::size_t src_pos = 0;
    std::uint32_t bc = 0;
    std::size_t last_m_off = 1;

    auto getbit = [&]() -> std::uint32_t {
        if ((bc & 0x7f) == 0) {
            if (src_pos >= src_len) return 0;
            std::uint32_t b = src[src_pos++];
            bc = ((b << 1) | 1) & 0x1ff;
        } else {
            bc = (bc << 1) & 0x1ff;
        }
        return (bc >> 8) & 1;
    };

    while (src_pos < src_len) {
        if (getbit() == 1) {
            if (src_pos >= src_len) break;
            dst.push_back(src[src_pos++]);
            continue;
        }

        std::size_t m_off = 1;
        while (true) {
            m_off = (m_off * 2) + getbit();
            if (getbit()) break;
            m_off = (m_off - 1) * 2 + getbit();
        }

        std::size_t m_len = 0;
        if (m_off == 2) {
            m_off = last_m_off;
            m_len = getbit();
        } else {
            if (src_pos >= src_len) break;
            std::uint32_t c = src[src_pos++];
            std::size_t val = (m_off - 3) * 256 + c;
            if (val == static_cast<std::size_t>(-1) || val == 0xffffffff || val == 0xfffffffe) {
                break; // EOF marker
            }
            m_len = (val ^ 1) & 1;
            m_off = (val >> 1) + 1;
            last_m_off = m_off;
        }

        if (m_len != 0) {
            m_len = 1 + getbit();
        } else if (getbit()) {
            m_len = 3 + getbit();
        } else {
            m_len = 1;
            while (true) {
                m_len = (m_len * 2) + getbit();
                if (getbit()) break;
            }
            m_len += 3;
        }

        if (m_off > 0x500) {
            m_len += 1;
        }

        if (m_off > dst.size()) {
            // Match offset out of bounds
            return false;
        }

        for (std::size_t i = 0; i <= m_len; ++i) {
            dst.push_back(dst[dst.size() - m_off]);
        }
    }

    return true;
}

// ----------------------------------------------------------------------------
// Little-endian I/O helpers
// ----------------------------------------------------------------------------
bool has_magic(const std::vector<std::uint8_t>& bytes,
               std::size_t offset,
               const char* magic) {
    return offset + 4 <= bytes.size() &&
           bytes[offset] == static_cast<std::uint8_t>(magic[0]) &&
           bytes[offset + 1] == static_cast<std::uint8_t>(magic[1]) &&
           bytes[offset + 2] == static_cast<std::uint8_t>(magic[2]) &&
           bytes[offset + 3] == static_cast<std::uint8_t>(magic[3]);
}

std::uint16_t read_u16_le(const std::vector<std::uint8_t>& bytes, std::size_t offset) {
    return static_cast<std::uint16_t>(bytes[offset]) |
           (static_cast<std::uint16_t>(bytes[offset + 1]) << 8);
}

std::uint32_t read_u32_le(const std::vector<std::uint8_t>& bytes, std::size_t offset) {
    return static_cast<std::uint32_t>(bytes[offset]) |
           (static_cast<std::uint32_t>(bytes[offset + 1]) << 8) |
           (static_cast<std::uint32_t>(bytes[offset + 2]) << 16) |
           (static_cast<std::uint32_t>(bytes[offset + 3]) << 24);
}

void append_u16_le(std::vector<std::uint8_t>& output, std::uint16_t value) {
    output.push_back(static_cast<std::uint8_t>(value));
    output.push_back(static_cast<std::uint8_t>(value >> 8));
}

void append_u32_le(std::vector<std::uint8_t>& output, std::uint32_t value) {
    output.push_back(static_cast<std::uint8_t>(value));
    output.push_back(static_cast<std::uint8_t>(value >> 8));
    output.push_back(static_cast<std::uint8_t>(value >> 16));
    output.push_back(static_cast<std::uint8_t>(value >> 24));
}

void write_u32_le(std::vector<std::uint8_t>& output, std::size_t offset, std::uint32_t value) {
    output[offset] = static_cast<std::uint8_t>(value);
    output[offset + 1] = static_cast<std::uint8_t>(value >> 8);
    output[offset + 2] = static_cast<std::uint8_t>(value >> 16);
    output[offset + 3] = static_cast<std::uint8_t>(value >> 24);
}

// ----------------------------------------------------------------------------
// Convert DMF Tag 570 into standard SWF DefineBitsLossless / DefineBitsLossless2
// ----------------------------------------------------------------------------
bool convert_tag_570(const std::uint8_t* tag_data, std::size_t tag_len,
                     std::vector<std::uint8_t>& swf_tag,
                     bool compress_images = false,
                     int compression_level = 6) {
    if (tag_len < 12) return false;

    std::uint16_t char_id = static_cast<std::uint16_t>(tag_data[0]) |
                            (static_cast<std::uint16_t>(tag_data[1]) << 8);

    if (tag_data[2] != 'U' || tag_data[3] != 'C' || tag_data[4] != 'L') {
        std::cerr << "error: tag 570 non-UCL compression not supported\n";
        return false;
    }

    std::uint8_t method = tag_data[5];
    std::uint8_t format = tag_data[6];
    std::uint16_t width = static_cast<std::uint16_t>(tag_data[7]) |
                          (static_cast<std::uint16_t>(tag_data[8]) << 8);
    std::uint16_t height = static_cast<std::uint16_t>(tag_data[9]) |
                           (static_cast<std::uint16_t>(tag_data[10]) << 8);
    std::uint8_t byte11 = tag_data[11];

    std::vector<std::uint8_t> raw_pixels;
    if (!ucl_nrv2b_decompress_8(tag_data + 12, tag_len - 12, raw_pixels)) {
        std::cerr << "error: UCL NRV2B decompression failed for character " << char_id << "\n";
        return false;
    }

    std::size_t pixel_count = static_cast<std::size_t>(width) * height;

    if (method == 2 && format == 1) {
        // Direct Color (Method 2)
        if (raw_pixels.size() == pixel_count * 2) {
            // Case 1: 16-bit RGB565, no alpha channel -> Tag 20 (DefineBitsLossless), format 5 (PIX24)
            // Color layout: [0, R, G, B]
            std::vector<std::uint8_t> pix24(pixel_count * 4);
            for (std::size_t i = 0; i < pixel_count; ++i) {
                std::uint8_t b0 = raw_pixels[i * 2 + 0];
                std::uint8_t b1 = raw_pixels[i * 2 + 1];
                std::uint8_t r = b0 & 0xf8;
                std::uint8_t g = ((b0 << 5) & 0xe0) | ((b1 >> 3) & 0x1c);
                std::uint8_t b = (b1 << 3) & 0xf8;

                pix24[i * 4 + 0] = 0; // Reserved
                pix24[i * 4 + 1] = r;
                pix24[i * 4 + 2] = g;
                pix24[i * 4 + 3] = b;
            }

            std::vector<std::uint8_t> zlib_data;
            zlib_compress(pix24, zlib_data, compress_images, compression_level);

            std::vector<std::uint8_t> payload;
            append_u16_le(payload, char_id);
            payload.push_back(5); // Format 5 (24-bit RGB)
            append_u16_le(payload, width);
            append_u16_le(payload, height);
            payload.insert(payload.end(), zlib_data.begin(), zlib_data.end());

            // Build Tag 20 header
            std::uint16_t tag_type = 20;
            if (payload.size() >= 0x3f) {
                append_u16_le(swf_tag, (tag_type << 6) | 0x3f);
                append_u32_le(swf_tag, static_cast<std::uint32_t>(payload.size()));
            } else {
                append_u16_le(swf_tag, (tag_type << 6) | static_cast<std::uint16_t>(payload.size()));
            }
            swf_tag.insert(swf_tag.end(), payload.begin(), payload.end());
            return true;
        } else if (raw_pixels.size() == pixel_count * 3) {
            // Case 2: 16-bit RGB565 + 8-bit Alpha -> Tag 36 (DefineBitsLossless2), format 5 (RGBA32)
            // Planar format: first pixel_count * 2 bytes are RGB565 colors, followed by pixel_count bytes of Alpha.
            const std::uint8_t* colors = raw_pixels.data();
            const std::uint8_t* alphas = raw_pixels.data() + pixel_count * 2;

            std::vector<std::uint8_t> rgba32(pixel_count * 4);
            for (std::size_t i = 0; i < pixel_count; ++i) {
                std::uint8_t b0 = colors[i * 2 + 0];
                std::uint8_t b1 = colors[i * 2 + 1];
                std::uint8_t a  = alphas[i];

                std::uint8_t r = b0 & 0xf8;
                std::uint8_t g = ((b0 << 5) & 0xe0) | ((b1 >> 3) & 0x1c);
                std::uint8_t b = (b1 << 3) & 0xf8;

                std::uint8_t pr = r;
                std::uint8_t pg = g;
                std::uint8_t pb = b;
                if (a != 255) {
                    pr = std::min<std::uint8_t>(a, static_cast<std::uint8_t>((r * (a + 1)) >> 8));
                    pg = std::min<std::uint8_t>(a, static_cast<std::uint8_t>((g * (a + 1)) >> 8));
                    pb = std::min<std::uint8_t>(a, static_cast<std::uint8_t>((b * (a + 1)) >> 8));
                }

                rgba32[i * 4 + 0] = a;
                rgba32[i * 4 + 1] = pr;
                rgba32[i * 4 + 2] = pg;
                rgba32[i * 4 + 3] = pb;
            }

            std::vector<std::uint8_t> zlib_data;
            zlib_compress(rgba32, zlib_data, compress_images, compression_level);

            std::vector<std::uint8_t> payload;
            append_u16_le(payload, char_id);
            payload.push_back(5); // Format 5 (32-bit RGBA)
            append_u16_le(payload, width);
            append_u16_le(payload, height);
            payload.insert(payload.end(), zlib_data.begin(), zlib_data.end());

            // Build Tag 36 header
            std::uint16_t tag_type = 36;
            if (payload.size() >= 0x3f) {
                append_u16_le(swf_tag, (tag_type << 6) | 0x3f);
                append_u32_le(swf_tag, static_cast<std::uint32_t>(payload.size()));
            } else {
                append_u16_le(swf_tag, (tag_type << 6) | static_cast<std::uint16_t>(payload.size()));
            }
            swf_tag.insert(swf_tag.end(), payload.begin(), payload.end());
            return true;
        }
    } else if (method == 3 && format == 0) {
        // Method 3: Indexed Palette -> Tag 36 (DefineBitsLossless2), Format 5 (RGBA32)
        std::size_t num_colors = static_cast<std::size_t>(byte11) + 1;
        std::size_t pal_bytes = num_colors * 3;
        bool is_4bit = (num_colors <= 16);
        std::size_t pixel_bytes_needed = is_4bit ? (pixel_count + 1) / 2 : pixel_count;
        if (raw_pixels.size() < pal_bytes + pixel_bytes_needed) {
            std::cerr << "error: indexed image buffer too short for character " << char_id << "\n";
            return false;
        }

        struct ColorRGBA {
            std::uint8_t a, r, g, b;
        };
        std::vector<ColorRGBA> palette(num_colors);
        for (std::size_t i = 0; i < num_colors; ++i) {
            std::uint8_t b0 = raw_pixels[i * 3 + 0];
            std::uint8_t b1 = raw_pixels[i * 3 + 1];
            std::uint8_t a  = raw_pixels[i * 3 + 2];

            std::uint8_t r = b0 & 0xf8;
            std::uint8_t g = ((b0 << 5) & 0xe0) | ((b1 >> 3) & 0x1c);
            std::uint8_t b = (b1 << 3) & 0xf8;

            std::uint8_t pr = r;
            std::uint8_t pg = g;
            std::uint8_t pb = b;
            if (a != 255) {
                pr = std::min<std::uint8_t>(a, static_cast<std::uint8_t>((r * a) >> 8));
                pg = std::min<std::uint8_t>(a, static_cast<std::uint8_t>((g * a) >> 8));
                pb = std::min<std::uint8_t>(a, static_cast<std::uint8_t>((b * a) >> 8));
            }
            palette[i] = {a, pr, pg, pb};
        }

        const std::uint8_t* indices = raw_pixels.data() + pal_bytes;
        std::vector<std::uint8_t> rgba32(pixel_count * 4);
        for (std::size_t p = 0; p < pixel_count; ++p) {
            std::uint8_t idx = 0;
            if (is_4bit) {
                std::uint8_t bv = indices[p / 2];
                idx = (p % 2 == 0) ? ((bv >> 4) & 0x0f) : (bv & 0x0f);
            } else {
                idx = indices[p];
            }
            const ColorRGBA& c = palette[idx];
            rgba32[p * 4 + 0] = c.a;
            rgba32[p * 4 + 1] = c.r;
            rgba32[p * 4 + 2] = c.g;
            rgba32[p * 4 + 3] = c.b;
        }

        std::vector<std::uint8_t> zlib_data;
        zlib_compress(rgba32, zlib_data, compress_images, compression_level);

        std::vector<std::uint8_t> payload;
        append_u16_le(payload, char_id);
        payload.push_back(5); // Format 5 (32-bit RGBA)
        append_u16_le(payload, width);
        append_u16_le(payload, height);
        payload.insert(payload.end(), zlib_data.begin(), zlib_data.end());

        // Build Tag 36 header
        std::uint16_t tag_type = 36;
        if (payload.size() >= 0x3f) {
            append_u16_le(swf_tag, (tag_type << 6) | 0x3f);
            append_u32_le(swf_tag, static_cast<std::uint32_t>(payload.size()));
        } else {
            append_u16_le(swf_tag, (tag_type << 6) | static_cast<std::uint16_t>(payload.size()));
        }
        swf_tag.insert(swf_tag.end(), payload.begin(), payload.end());
        return true;
    }

    std::cerr << "error: unsupported method (" << static_cast<int>(method)
              << ") / format (" << static_cast<int>(format) << ") for character " << char_id << "\n";
    return false;
}

bool read_file(const std::string& path, std::vector<std::uint8_t>& bytes) {
    std::ifstream input(path, std::ios::binary);
    if (!input) {
        std::cerr << "error: cannot open input file: " << path << '\n';
        return false;
    }

    input.seekg(0, std::ios::end);
    const std::streamoff size = input.tellg();
    if (size < 0 ||
        static_cast<unsigned long long>(size) >
            std::numeric_limits<std::size_t>::max()) {
        std::cerr << "error: invalid input size\n";
        return false;
    }
    input.seekg(0, std::ios::beg);
    bytes.resize(static_cast<std::size_t>(size));
    if (!bytes.empty() &&
        !input.read(reinterpret_cast<char*>(bytes.data()), size)) {
        std::cerr << "error: cannot read input file: " << path << '\n';
        return false;
    }
    return true;
}

bool write_file(const std::string& path,
                const std::vector<std::uint8_t>& bytes) {
    std::ofstream output(path, std::ios::binary | std::ios::trunc);
    if (!output) {
        std::cerr << "error: cannot create output file: " << path << '\n';
        return false;
    }
    if (!bytes.empty()) {
        output.write(reinterpret_cast<const char*>(bytes.data()),
                     static_cast<std::streamsize>(bytes.size()));
    }
    if (!output) {
        std::cerr << "error: cannot write output file: " << path << '\n';
        return false;
    }
    return true;
}

// ----------------------------------------------------------------------------
// Full DMF to SWF Conversion
// ----------------------------------------------------------------------------
bool convert_dmf_to_swf(const std::vector<std::uint8_t>& dmf,
                        std::vector<std::uint8_t>& swf,
                        const ConvertOptions& options) {
    if (dmf.size() < kDmfHeaderSize) {
        std::cerr << "error: DMF is shorter than its 120-byte header\n";
        return false;
    }
    if (!has_magic(dmf, 0, "DMF\t")) {
        if (has_magic(dmf, 8, "DMF\t")) {
            std::cerr << "error: compressed DMF is not supported by this standalone converter\n";
        } else {
            std::cerr << "error: input does not have a DMF header\n";
        }
        return false;
    }

    const std::uint32_t declared_size = read_u32_le(dmf, 4);
    if (declared_size != dmf.size()) {
        std::cerr << "error: DMF size field (" << declared_size
                  << ") does not match file size (" << dmf.size() << ")\n";
        return false;
    }

    swf.clear();
    swf.reserve(dmf.size() * 2);

    // SWF Header: "FWS", version 8, file size (filled later), MovieHeader (12 bytes)
    swf.insert(swf.end(), {'F', 'W', 'S', 8});
    append_u32_le(swf, 0); // Placeholder for final SWF file length
    swf.insert(swf.end(), dmf.begin() + kMovieHeaderStart,
               dmf.begin() + kMovieHeaderStart + kMovieHeaderSize);

    // Parse DMF tags starting from offset 103 (TagStreamStart)
    std::size_t pos = kTagStreamStart;
    std::size_t tag_count = 0;
    std::size_t converted_images = 0;

    while (pos < dmf.size()) {
        if (pos + 2 > dmf.size()) break;
        std::uint16_t tag_hdr = read_u16_le(dmf, pos);
        std::uint16_t tag_type = tag_hdr >> 6;
        std::size_t tag_len = tag_hdr & 0x3f;
        std::size_t hdr_size = 2;

        if (tag_len == 0x3f) {
            if (pos + 6 > dmf.size()) break;
            tag_len = read_u32_le(dmf, pos + 2);
            hdr_size = 6;
        }

        if (pos + hdr_size + tag_len > dmf.size()) {
            std::cerr << "warning: tag " << tag_type << " extends beyond EOF\n";
            break;
        }

        const std::uint8_t* tag_payload = dmf.data() + pos + hdr_size;

        if (tag_type == 570) {
            // Convert proprietary DMF tag 570 to standard SWF DefineBitsLossless(2)
            std::vector<std::uint8_t> converted_tag;
            if (convert_tag_570(tag_payload, tag_len, converted_tag, options.compress_images, options.compression_level)) {
                swf.insert(swf.end(), converted_tag.begin(), converted_tag.end());
                converted_images++;
            } else {
                std::cerr << "error: failed to convert tag 570 at offset " << pos << "\n";
                return false;
            }
        } else {
            // Standard SWF tag: copy verbatim
            swf.insert(swf.end(), dmf.begin() + pos, dmf.begin() + pos + hdr_size + tag_len);
        }

        pos += hdr_size + tag_len;
        tag_count++;
    }

    // Write final SWF file length into header (offset 4)
    write_u32_le(swf, 4, static_cast<std::uint32_t>(swf.size()));

    if (options.cws_container) {
        std::vector<std::uint8_t> cws;
        if (compress_swf_to_cws(swf, cws, options.compression_level)) {
            swf = std::move(cws);
        } else {
            std::cerr << "error: failed to apply CWS container compression\n";
            return false;
        }
    }

    std::cout << "Successfully converted " << tag_count << " tags ("
              << converted_images << " images converted with corrected colors)\n";
    return true;
}

void print_usage(const char* prog) {
    std::cout << "Usage: " << prog << " [options] <input.dmf> <output.swf>\n\n"
              << "Converts LG proprietary DMF files into standard SWF format.\n\n"
              << "Options:\n"
              << "  --compress, -c         Enable lossless DEFLATE compression on images.\n"
              << "                         (Matches original LGUI output, reduces ~1.5MB to ~150KB)\n"
              << "  --cws                  Compress the entire SWF container to CWS format.\n"
              << "                         (Reduces SWF further to ~123KB, matching compressed DMF)\n"
              << "  --compress-all         Enable both image DEFLATE and CWS container compression.\n"
              << "  --level <1-9>          Set compression level (default: 6).\n"
              << "  -h, --help             Show this help message.\n\n"
              << "Examples:\n"
              << "  " << prog << " input.dmf output.swf\n"
              << "  " << prog << " --compress input.dmf output.swf\n"
              << "  " << prog << " -c --cws input.dmf output.swf\n";
}

}  // namespace

int main(int argc, char* argv[]) {
    ConvertOptions options;
    std::string input_path;
    std::string output_path;

    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "-h" || arg == "--help") {
            print_usage(argv[0]);
            return 0;
        } else if (arg == "--compress" || arg == "-c") {
            options.compress_images = true;
        } else if (arg == "--cws") {
            options.cws_container = true;
        } else if (arg == "--compress-all" || arg == "--all") {
            options.compress_images = true;
            options.cws_container = true;
        } else if (arg == "--level" && i + 1 < argc) {
            int lvl = std::atoi(argv[++i]);
            options.compression_level = std::max(1, std::min(9, lvl));
        } else if (!arg.empty() && arg[0] == '-') {
            std::cerr << "error: unknown option: " << arg << "\n";
            print_usage(argv[0]);
            return 2;
        } else {
            if (input_path.empty()) {
                input_path = arg;
            } else if (output_path.empty()) {
                output_path = arg;
            } else {
                std::cerr << "error: unexpected extra argument: " << arg << "\n";
                print_usage(argv[0]);
                return 2;
            }
        }
    }

    if (input_path.empty() || output_path.empty()) {
        std::cerr << "error: missing input or output file path\n\n";
        print_usage(argv[0]);
        return 2;
    }

    std::vector<std::uint8_t> dmf;
    std::vector<std::uint8_t> swf;
    if (!read_file(input_path, dmf) || !convert_dmf_to_swf(dmf, swf, options) ||
        !write_file(output_path, swf)) {
        return 1;
    }

    std::cout << "converted " << dmf.size() << " bytes to " << swf.size()
              << " bytes";
    if (options.cws_container && options.compress_images) {
        std::cout << " (DEFLATE images + CWS container compression active)";
    } else if (options.cws_container) {
        std::cout << " (CWS container compression active)";
    } else if (options.compress_images) {
        std::cout << " (lossless DEFLATE image compression active)";
    } else {
        std::cout << " (uncompressed stored blocks; use --compress to shrink to ~150KB)";
    }
    std::cout << "\n";
    return 0;
}
