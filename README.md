# folderHash
Compute hashes for all files in a folder tree (Windows 7+).

This is a versatile Windows multithreaded command-line interface to the portable Hashing Library by Stephan Brumme (all rights reserved).
https://create.stephan-brumme.com/hash-library/

Supported algorithms : XX, CRC32, MD5, SHA1/2/3, Keccak

Example usage:  `folderHash -u -crc -g -ss 0 -l 20k c:/tmp`

-> Hash `c:\tmp`, skip files less than 20 Kbytes in size (`-l 20k`), use uppercase (`-u`) for CRC32 hash (`-crc`), prefix each line with 'CRC32' (`-g`),
and do not show file sizes (`-ss 0`).

See Usage.txt for full detail.


This is released under the Zlib Licence (https://opensource.org/licenses/Zlib).

Please report any issues to wj.osprojects@gmail.com


