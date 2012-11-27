#!/usr/bin/env python
# vim:set ts=8 sw=4 sts=4 et:

# Copyright (c) 2012 Serban Giuroiu
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

# ------------------------------------------------------------------------------

import argparse
import array
import hashlib
import pdb
import pprint
import struct
import subprocess
import time
import wave

import crcmod

from bitarray import bitarray

# ------------------------------------------------------------------------------

EXIT_SUCCESS    = 0
EXIT_FAILURE    = 1
EXIT_CMDFAILURE = 2

# TTY Colors
NOCOLOR     = '\033[0m'
RED         = '\033[01;31m'
GREEN       = '\033[01;32m'
YELLOW      = '\033[01;33m'
BLUE        = '\033[01;34m'
MAGENTA     = '\033[01;35m'
CYAN        = '\033[01;36m'
WHITE       = '\033[01;37m'

def msg(s):
    print(GREEN + "*", s, NOCOLOR)

def err(s):
    print(RED + "!", s, NOCOLOR)

def dbg(s):
    if not __debug__:
        return

    if isinstance(s, dict) or isinstance(s, list):
        print(YELLOW + "%", pprint.pformat(s, indent=2), NOCOLOR)
    else:
        print(YELLOW + "%", s, NOCOLOR)

def sep():
    try:
        num_columns = int(subprocess.getoutput('stty size').split()[1])
    except IndexError:
        num_columns = 80

    s = "".join(["-" for i in range(num_columns)])

    print(WHITE + s + NOCOLOR)

def run_process(s):
    if __debug__:
        print(CYAN + ">", s, NOCOLOR)

    subprocess.call(s, shell=True)

class Timer(object):
    def start(self):
        self.start_time = int(time.time())

    def stop(self):
        self.end_time = int(time.time())

    def time_delta(self):
        return self.end_time - self.start_time

    def string_delta(self):
        total = self.time_delta()

        days    = total     // 86400
        remain  = total     %  86400
        hours   = remain    //  3600
        remain  = remain    %   3600
        minutes = remain    //    60
        seconds = remain    %     60

        return str(days) + "d " + str(hours) + "h " + str(minutes) + "m " + str(seconds) + "s"

# ------------------------------------------------------------------------------

crc8 = crcmod.predefined.mkPredefinedCrcFun('crc-8')
crc16 = crcmod.predefined.mkPredefinedCrcFun('crc-16-buypass')

def bitarray_from_int(i, width):
    return bitarray(('{:0' + str(width) + 'b}').format(i))

def utf8_encoded_bitarray_from_int(i):
    # i < 2**7
    if i < 0x80:
        return bitarray_from_int(i, 8)

    # i < 2**11
    if i < 0x800:
        bits = bitarray(16)

        bits[0:8]   = bitarray_from_int(0xC0 | (i >> 6), 8)
        bits[8:16]  = bitarray_from_int(0x80 | (i & 0x3F), 8)

        return bits

    # i < 2**16
    if i < 0x10000:
        bits = bitarray(24)

        bits[0:8]   = bitarray_from_int(0xE0 | (i >> 12), 8)
        bits[8:16]  = bitarray_from_int(0x80 | ((i >> 6) & 0x3F), 8)
        bits[16:24] = bitarray_from_int(0x80 | (i & 0x3F), 8)

        return bits

    # i < 2**21
    if i < 0x200000:
        bits = bitarray(32)

        bits[0:8]   = bitarray_from_int(0xF0 | ((i >> 18)), 8)
        bits[8:16]  = bitarray_from_int(0x80 | ((i >> 12) & 0x3F), 8)
        bits[16:24] = bitarray_from_int(0x80 | ((i >> 6) & 0x3F), 8)
        bits[24:32] = bitarray_from_int(0x80 | (i & 0x3F), 8)

        return bits

    # i < 2**26
    if i < 0x4000000:
        bits = bitarray(40)

        bits[0:8]   = bitarray_from_int(0xF0 | ((i >> 24)), 8)
        bits[8:16]  = bitarray_from_int(0x80 | ((i >> 18) & 0x3F), 8)
        bits[16:24] = bitarray_from_int(0x80 | ((i >> 12) & 0x3F), 8)
        bits[24:32] = bitarray_from_int(0x80 | ((i >> 6) & 0x3F), 8)
        bits[32:40] = bitarray_from_int(0x80 | (i & 0x3F), 8)

        return bits

    # i < 2**31
    if i < 0x80000000:
        bits = bitarray(40)

        bits[0:8]   = bitarray_from_int(0xF0 | ((i >> 24)), 8)
        bits[8:16]  = bitarray_from_int(0x80 | ((i >> 18) & 0x3F), 8)
        bits[16:24] = bitarray_from_int(0x80 | ((i >> 12) & 0x3F), 8)
        bits[24:32] = bitarray_from_int(0x80 | ((i >> 6) & 0x3F), 8)
        bits[32:40] = bitarray_from_int(0x80 | (i & 0x3F), 8)

        return bits

    assert False, "We shouldn't need to encode any integers that require more than 31 bits"

# ------------------------------------------------------------------------------

BLOCK_SIZE      = 4096  # Num samples per block
SAMPLE_RATE     = 44100 # Hz
SAMPLE_SIZE     = 16    # Num bits per sample
NUM_CHANNELS    = 2

# ------------------------------------------------------------------------------

BLOCK_TYPE_STREAMINFO       = 0
BLOCK_TYPE_PADDING          = 1
BLOCK_TYPE_APPLICATION      = 2
BLOCK_TYPE_SEEKTABLE        = 3
BLOCK_TYPE_VORBIS_COMMENT   = 4
BLOCK_TYPE_CUESHEET         = 5
BLOCK_TYPE_PICTURE          = 6

class Stream:
    def __init__(self, metadata_blocks, frames):
        self.metadata_blocks = metadata_blocks
        self.frames = frames

    def get_bytes(self):
        return b'fLaC' + \
               b''.join([block.get_bytes() for block in self.metadata_blocks]) + \
               b''.join([frame.get_bytes() for frame in self.frames])

class MetadataBlock:
    def __init__(self, metadata_block_header, metadata_block_data):
        self.metadata_block_header = metadata_block_header
        self.metadata_block_data = metadata_block_data

    def get_bytes(self):
        return self.metadata_block_header.get_bytes() + \
               self.metadata_block_data.get_bytes()

class MetadataBlockHeader:
    def __init__(self, last_metadata_block, block_type, length):
        self.last_metadata_block = last_metadata_block
        self.block_type = block_type
        self.length = length

    def get_bytes(self):
        bits = bitarray(32)

        bits[0] = self.last_metadata_block
        bits[1:8] = bitarray_from_int(self.block_type, 7)
        bits[8:32] = bitarray_from_int(self.length, 24)

        return bits.tobytes()

class MetadataBlockStreamInfo:
    def __init__(self, num_samples, md5_digest):
        self.num_samples = num_samples
        self.md5_digest = md5_digest

    def get_bytes(self):
        bits = bitarray(144)

        bits[0:16]      = bitarray_from_int(BLOCK_SIZE, 16)         # Min block size in samples
        bits[16:32]     = bitarray_from_int(BLOCK_SIZE, 16)         # Max block size in samples
        bits[32:56]     = 0                                         # TODO: Min frame size in bytes
        bits[56:80]     = 0                                         # TODO: Max frame size in bytes
        bits[80:100]    = bitarray_from_int(SAMPLE_RATE, 20)        # Sample rate in Hz
        bits[100:103]   = bitarray_from_int(NUM_CHANNELS - 1, 3)    # (Num channels) - 1
        bits[103:108]   = bitarray_from_int(SAMPLE_SIZE - 1, 5)     # (Sample size) - 1 in bits per sample
        bits[108:144]   = bitarray_from_int(self.num_samples, 36)   # Total num samples
#       bits[144:272]   = md5_bits                                  # MD5 signature of the input stream

        return bits.tobytes() + self.md5_digest

class Frame:
    def __init__(self, frame_header, frame_footer, subframes):
        self.frame_header = frame_header
        self.frame_footer = frame_footer
        self.subframes = subframes

    def get_bytes(self):
        # TODO: In the future, we may need to include zero padding
        return self.frame_header.get_bytes() + \
               b''.join([subframe.get_bytes() for subframe in self.subframes]) + \
               self.frame_footer.get_bytes()

class FrameHeader:
    def __init__(self, frame_number, num_samples):
        self.frame_number = frame_number
        self.num_samples = num_samples

    def get_bytes(self):
        bits = bitarray(32)                         # Only the first 32 bits are fixed

        bits[0:14]  = bitarray('11111111111110')    # Sync code
        bits[14]    = 0                             # Mandatory Value
        bits[15]    = 0                             # Fixed blocksize stream
        bits[16:20] = bitarray('1100')              # Num samples, hardcoded to 4096 samples per block. Per the spec, n = 12 ==> 1100. See below for exception.
        bits[20:24] = bitarray('1001')              # Sample rate, hardcoded to 44.1 kHz
        bits[24:28] = bitarray('0001')              # Channel assignment, hardcoded to independent stereo
        bits[28:31] = bitarray('100')               # Sample size, hardcoded to 16 bits per sample
        bits[31]    = 0                             # Mandatory Value

        frame_number_bits = utf8_encoded_bitarray_from_int(self.frame_number)

        custom_block_size_bits = bitarray()

        # The last block can have less than BLOCK_SIZE samples
        if self.num_samples != BLOCK_SIZE:
            bits[16:20] = bitarray('0111')          # Num samples should be retrieved from a separate 16-bit field (custom_block_size_bits)

            custom_block_size_bits = bitarray_from_int(self.num_samples - 1, 16)

        # We do not have to specify a custom sample rate because the sample rate is fixed to 44.1 kHz

        crc_input = (bits + frame_number_bits + custom_block_size_bits).tobytes()
        crc_bytes = bytes((crc8(crc_input),))

        return crc_input + crc_bytes

class FrameFooter:
    def __init__(self, frame_header, subframes):
        # TODO: Should FrameFooter depend on frame_header and subframes? The
        # only thing this object stores is the CRC-16 calculation of those
        # objects, so if we were to follow the established pattern, then the
        # CRC-16 calculation should happen outside of this class, and the result
        # should be the only dependency.

        self.frame_header = frame_header
        self.subframes = subframes

    def get_bytes(self):
        # TODO: In the future, we may need to include zero padding
        crc_input = self.frame_header.get_bytes() + \
                    b''.join([subframe.get_bytes() for subframe in self.subframes])

        crc_bytes = struct.pack('>H', crc16(crc_input))

        return crc_bytes

class Subframe:
    def __init__(self, subframe_header, subframe_data):
        self.subframe_header = subframe_header
        self.subframe_data = subframe_data

    def get_bytes(self):
        return self.subframe_header.get_bytes() + \
               self.subframe_data.get_bytes()

class SubframeHeader:
    def get_bytes(self):
        bits = bitarray(8)

        bits[0] = 0                     # Mandatory value
        bits[1:7] = bitarray('000001')  # SUBFRAME_VERBATIM
        bits[7] = 0                     # TODO: Wasted bits

        return bits.tobytes()

class SubframeVerbatim:
    def __init__(self, samples):
        self.samples = samples

    def get_bytes(self):
        return struct.pack('>' + str(len(self.samples)) + 'h', *self.samples)

class WaveStream:
    def __init__(self, sample_size, sample_rate, channels, md5_digest):
        self.sample_size = sample_size
        self.sample_rate = sample_rate
        self.channels = channels
        self.md5_digest = md5_digest

        self.num_channels = len(channels)
        self.num_samples = len(channels[0])

# ------------------------------------------------------------------------------

def read_wave(input_path):
    timer = Timer()

    input_file = wave.open(input_path, 'rb')

    sample_size = input_file.getsampwidth() * 8             # Convert bytes per sample into bits per sample
    sample_rate = input_file.getframerate()                 # In Hz
    num_channels = input_file.getnchannels()
    num_samples = input_file.getnframes()
    num_interleaved_samples = num_channels * num_samples

    sorry_string = "Sorry, we only support 16-bit 44.1 kHz stereo input"

    assert sample_size == SAMPLE_SIZE, sorry_string
    assert sample_rate == SAMPLE_RATE, sorry_string
    assert num_channels == NUM_CHANNELS, sorry_string

    msg("num_samples = {}".format(num_samples))

    raw_frames = input_file.readframes(num_samples)

    input_file.close()

    md5_digest = hashlib.md5(raw_frames).digest()

    timer.start()

    # Wave file samples are little-endian signed integers
    interleaved_samples = struct.unpack('<' + str(num_interleaved_samples) + 'h', raw_frames)

    timer.stop()

    dbg("unpacking took " + timer.string_delta())

    # TODO: Consider going straight to array.array, but I think we'd have to
    # assume a little-endian machine.

    # TODO: Use NumPy

    channels = [list() for i in range(num_channels)]

    timer.start()

    for index, sample in enumerate(interleaved_samples):
        channels[index % num_channels].append(sample)

    timer.stop()

    dbg("splitting took " + timer.string_delta())

    timer.start()

    wave_stream = WaveStream(input_file.getframerate(),
                             input_file.getsampwidth(),
                             [array.array('h', channel) for channel in channels],
                             md5_digest)

    timer.stop()

    dbg("making arrays took " + timer.string_delta())

    return wave_stream

def encode_wave_stream(wave_stream):
    frames = list()

    for sample_index in range(0, wave_stream.num_samples, BLOCK_SIZE):
        frame_number = sample_index // BLOCK_SIZE

        subframes = list()

        for channel in wave_stream.channels:
            subframe_verbatim = SubframeVerbatim(channel[sample_index : sample_index + BLOCK_SIZE])
            subframe_header = SubframeHeader()
            subframe = Subframe(subframe_header, subframe_verbatim)

            subframes.append(subframe)

        num_samples_in_frame = (wave_stream.num_samples - sample_index) if (wave_stream.num_samples - sample_index) < BLOCK_SIZE else BLOCK_SIZE

        frame_header = FrameHeader(frame_number, num_samples_in_frame)
        frame_footer = FrameFooter(frame_header, subframes)
        frame = Frame(frame_header, frame_footer, subframes)

        frames.append(frame)

    metadata_block_stream_info = MetadataBlockStreamInfo(wave_stream.num_samples, wave_stream.md5_digest)
    metadata_block_header = MetadataBlockHeader(True, BLOCK_TYPE_STREAMINFO, len(metadata_block_stream_info.get_bytes()))
    metadata_block = MetadataBlock(metadata_block_header, metadata_block_stream_info)

    metadata_blocks = (metadata_block,)

    stream = Stream(metadata_blocks, frames)

    return stream

def write_stream(stream, output_path):
    with open(output_path, 'wb') as output_file:
        output_file.write(stream.get_bytes())

def get_command_line_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('input_path', help="The 16-bit 44.1 kHz stereo wave file to encode")
    parser.add_argument('output_path', help="The resulting FLAC file")

    return vars(parser.parse_args())

def main():
    args = get_command_line_args()

    wave_stream = read_wave(args['input_path'])
    stream = encode_wave_stream(wave_stream)
    write_stream(stream, args['output_path'])

# ------------------------------------------------------------------------------

if __name__ == '__main__':
    main()