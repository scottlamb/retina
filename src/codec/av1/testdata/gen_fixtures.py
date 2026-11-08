#!/usr/bin/env python3
# Copyright (C) The Retina Authors
# SPDX-License-Identifier: MIT OR Apache-2.0
"""Generate AV1 RTP test vectors for the depacketizer tests.

One encode per fixture, tee'd three ways after av1parse (obu-stream, tu):
  1. reference temporal units          -> <name>.tu
  2. rtpav1pay mtu=600 RTP packets     -> <name>.rtp
  3. the same TUs pushed through appsrc into isofmp4mux (gst-plugins-rs
     fmp4, which builds av1C from the sequence header, config OBUs included)
                                       -> av1C box body -> <name>.av1c
and the av1parse src caps are written to <name>.caps.txt, and GStreamer's
RFC 6381 codec string for those caps plus the av1C (pbutils
codec_utils_caps_get_mime_codec) to <name>.codec.txt.

File framing (.tu and .rtp): repeated records of
  u32 big-endian length, u8 flags, <length> bytes
flags bit 0 = GStreamer did NOT mark the buffer DELTA_UNIT (a keyframe TU);
for RTP records the flag is unused (0).

Run from anywhere: python3 gen_fixtures.py <output dir>
"""
import os
import struct
import sys
import tempfile

import gi

gi.require_version("Gst", "1.0")
gi.require_version("GstPbutils", "1.0")
from gi.repository import Gst, GstPbutils  # noqa: E402

FIXTURES = [
    # name, encoder description, width, height, frames
    (
        "aom_640x360",
        "av1enc usage-profile=realtime cpu-used=10 lag-in-frames=0 "
        "keyframe-max-dist=30 target-bitrate=150 threads=4",
        640,
        360,
        60,
    ),
    (
        "svt_320x180",
        "svtav1enc preset=12 intra-period-length=14 target-bitrate=100",
        320,
        180,
        30,
    ),
]


def run(name, enc, w, h, frames, outdir):
    Gst.init(None)
    tmp = tempfile.mkdtemp()
    mp4 = os.path.join(tmp, "out.mp4")
    desc = (
        f"videotestsrc num-buffers={frames} pattern=ball ! "
        f"video/x-raw,format=I420,width={w},height={h},framerate=30/1 ! "
        f"{enc} ! av1parse ! "
        "video/x-av1,stream-format=obu-stream,alignment=tu ! tee name=t "
        "t. ! queue ! appsink name=ref emit-signals=true sync=false "
        "t. ! queue ! rtpav1pay mtu=600 ! "
        "appsink name=rtp emit-signals=true sync=false"
    )
    pipe = Gst.parse_launch(desc)
    tus, pkts, caps = [], [], []

    def on_ref(sink):
        s = sink.emit("pull-sample")
        b = s.get_buffer()
        ok, m = b.map(Gst.MapFlags.READ)
        key = 0 if b.has_flags(Gst.BufferFlags.DELTA_UNIT) else 1
        tus.append((key, bytes(m.data)))
        b.unmap(m)
        if not caps:
            caps.append(s.get_caps().to_string())
        return Gst.FlowReturn.OK

    def on_rtp(sink):
        b = sink.emit("pull-sample").get_buffer()
        ok, m = b.map(Gst.MapFlags.READ)
        pkts.append((0, bytes(m.data)))
        b.unmap(m)
        return Gst.FlowReturn.OK

    pipe.get_by_name("ref").connect("new-sample", on_ref)
    pipe.get_by_name("rtp").connect("new-sample", on_rtp)
    pipe.set_state(Gst.State.PLAYING)
    msg = pipe.get_bus().timed_pop_filtered(
        60 * Gst.SECOND, Gst.MessageType.EOS | Gst.MessageType.ERROR
    )
    pipe.set_state(Gst.State.NULL)
    if msg is None or msg.type != Gst.MessageType.EOS:
        raise SystemExit(f"{name}: pipeline failed: {msg and msg.parse_error()}")

    def write(path, recs):
        with open(path, "wb") as f:
            for flag, data in recs:
                f.write(struct.pack(">IB", len(data), flag))
                f.write(data)

    write(os.path.join(outdir, f"{name}.tu"), tus)
    write(os.path.join(outdir, f"{name}.rtp"), pkts)
    with open(os.path.join(outdir, f"{name}.caps.txt"), "w") as f:
        f.write(caps[0] + "\n")
    mux = Gst.parse_launch(
        f"appsrc name=src format=time ! isofmp4mux ! filesink location={mp4}"
    )
    src = mux.get_by_name("src")
    src.set_property("caps", Gst.Caps.from_string(caps[0]))
    mux.set_state(Gst.State.PLAYING)
    dur = Gst.SECOND // 30
    for n, (key, d) in enumerate(tus):
        b = Gst.Buffer.new_wrapped(d)
        b.pts = b.dts = n * dur
        b.duration = dur
        if not key:
            b.set_flags(Gst.BufferFlags.DELTA_UNIT)
        src.emit("push-buffer", b)
    src.emit("end-of-stream")
    msg = mux.get_bus().timed_pop_filtered(
        60 * Gst.SECOND, Gst.MessageType.EOS | Gst.MessageType.ERROR
    )
    mux.set_state(Gst.State.NULL)
    if msg is None or msg.type != Gst.MessageType.EOS:
        raise SystemExit(f"{name}: mux failed: {msg and msg.parse_error()}")
    data = open(mp4, "rb").read()
    os.unlink(mp4)
    os.rmdir(tmp)
    i = data.find(b"av1C")
    if i < 4:
        raise SystemExit(f"{name}: no av1C box in mp4")
    size = struct.unpack(">I", data[i - 4 : i])[0]
    with open(os.path.join(outdir, f"{name}.av1c"), "wb") as f:
        f.write(data[i + 4 : i - 4 + size])
    c = Gst.Caps.from_string(caps[0])
    st = c.get_structure(0)
    st.set_value("codec_data", Gst.Buffer.new_wrapped(data[i + 4 : i - 4 + size]))
    with open(os.path.join(outdir, f"{name}.codec.txt"), "w") as f:
        f.write(GstPbutils.codec_utils_caps_get_mime_codec(c) + "\n")
    print(f"{name}: {len(tus)} TUs ({sum(k for k, _ in tus)} key), {len(pkts)} RTP packets")


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    for fx in FIXTURES:
        run(*fx, out)
