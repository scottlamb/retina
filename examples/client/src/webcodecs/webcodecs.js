class Decoder {
  constructor() {
    if (typeof VideoDecoder === "undefined") {
      throw new Error("VideoDecoder API is not supported in this browser");
    }
    this.decoder = new VideoDecoder({
      output: this.decodeEventOutput,
      error: this.decodeEventError,
    });
    const proto = window.location.protocol === "https:" ? "wss" : "ws";
    this.ws = new WebSocket(`${proto}://${window.location.host}/websocket`);
    this.ws.binaryType = "arraybuffer";
    this.ws.addEventListener("close", this.wsEventClose);
    this.ws.addEventListener("open", this.wsEventOpen);
    this.ws.addEventListener("error", this.wsEventError);
    this.ws.addEventListener("message", this.wsEventMessage);
    this.canvas = document.getElementById("canvas");
    this.ctx = this.canvas.getContext("2d");
    this.framesThisSecond = 0;
    this.fpsIntervalId = setInterval(this.logFps, 1000);
  }

  logFps = () => {
    console.log(`[decoder] fps: ${this.framesThisSecond}`);
    this.framesThisSecond = 0;
  };

  closeWithError(msg) {
    console.error(msg);
    clearInterval(this.fpsIntervalId);
    if (
      this.ws.readyState !== WebSocket.CLOSED &&
      this.ws.readyState !== WebSocket.CLOSING
    ) {
      this.ws.close(1000, msg);
    }
    if (this.decoder.state !== "closed") {
      this.decoder.close();
    }
  }

  wsEventClose = (ev) => {
    console.log(
      `[websocket] closed (code=${ev.code}${ev.reason ? ", reason=" + ev.reason : ""})`,
    );
    clearInterval(this.fpsIntervalId);
  };

  wsEventOpen = () => {
    console.log("[websocket] open");
  };

  wsEventError = () => {
    this.closeWithError("[websocket] error");
  };

  wsEventMessage = async (ev) => {
    if (!(ev.data instanceof ArrayBuffer)) {
      return;
    }

    const buf = new Uint8Array(ev.data);
    if (buf[0] === 0) {
      // Parameters. 1-byte type marker, RFC 6381 codec string, NUL byte, extra data blob.
      const nulIndex = buf.indexOf(0, 1);
      if (nulIndex === -1) {
        this.closeWithError(
          "[websocket] invalid parameters message: no NUL byte",
        );
        return;
      }
      const codec = new TextDecoder().decode(buf.slice(1, nulIndex));
      const description = buf.slice(nulIndex + 1);
      console.log(`[websocket] new parameters, codec=${codec}`);

      const config = { codec, description };
      const support = await VideoDecoder.isConfigSupported(config);
      if (!support.supported) {
        this.closeWithError(
          `[decoder] codec ${codec} is not supported by this browser`,
        );
        return;
      }

      this.decoder.configure(config);
    } else if (buf[0] === 1) {
      // Frame. 1-byte type marker, 64-bit timestamp in microseconds, 1-byte key boolean, frame data blob.
      const timestamp = Number(new DataView(buf.buffer).getBigUint64(1));
      const type = buf[9] === 1 ? "key" : "delta";
      const data = buf.slice(10);
      this.decoder.decode(
        new EncodedVideoChunk({
          type,
          timestamp,
          data: data,
        }),
      );
    } else if (buf[0] === 2) {
      // Skipped frames. 1-byte type marker, 64-bit count.
      const skipped = Number(new DataView(buf.buffer).getBigUint64(1));
      console.log(`Skipped ${skipped} frames`);
    } else {
      this.closeWithError(
        `[websocket] unexpected message type byte: ${buf[0]}`,
      );
      return;
    }
  };

  decodeEventOutput = (frame) => {
    if (
      frame.displayHeight != this.canvas.height ||
      frame.displayWidth != this.canvas.width
    ) {
      this.canvas.width = frame.displayWidth;
      this.canvas.height = frame.displayHeight;
    }
    this.ctx.drawImage(frame, 0, 0, frame.displayWidth, frame.displayHeight);
    frame.close();
    this.framesThisSecond++;
  };

  decodeEventError = (error) => {
    console.error("[decoder] error", error);
  };
}

function init() {
  console.log("[init] starting");
  try {
    new Decoder();
  } catch (e) {
    console.error("[init]", e.message);
  }
}

window.addEventListener("load", init);
