# The Tir codepage

Most golfing languages have SBCS codepages, or **Single Byte Character Substitution**. Such examples of this are [Jelly](https://github.com/DennisMitchell/jellylanguage/wiki/Code-page), [05AB1E](https://github.com/Adriandmen/05AB1E/wiki/Codepage), and [Husk](https://github.com/barbuz/Husk/wiki/Codepage). However, Tir has a bit of a different codepage.

Tir's codepage is more similar to UTF-8, being a variable-width character encoding scheme. While still in development, a UTF-8 file is encoded by using a few multibyte characters. Here is generally how the code page works, which is more like a parsing scheme than anything else.

Bytes `0x00` to `0xF9` (code values `0` to `249` inclusive) translate to a single command each. Bytes `0xFA` to `0xFE` can be followed by any byte. This two-byte pair is translated to a single command. Finally, `0xFF` can be followed by any two bytes. This triple is translated to a single command.

Thus, the following number of commands are possible:

- 1 byte commands (`0x00-0xF9`) - **249 commands**
- 2 byte commands (`0xFA*-0xFE*`) - 256 &times; 5 = **1280 commands**
- 3 byte commands (`0xFF**`) - 256<sup>2</sup> = **65536 commands**
- **Total: 67065 commands**
