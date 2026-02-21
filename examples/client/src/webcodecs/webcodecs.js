class Decoder {
  constructor() {
    if (typeof VideoDecoder === "undefined") {
      throw new Error(
        window.isSecureContext
          ? "VideoDecoder API is not supported in this browser"
          : "VideoDecoder API requires a secure context (HTTPS or localhost)"
      );
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
    this.errorDiv = document.getElementById("error");
    this.closed = false;
    this.hasFrame = false;
    this.framesThisSecond = 0;
    // Serialize message handling: each message is processed only after the
    // previous one completes, so configure() always precedes decode() calls.
    this.msgChain = Promise.resolve();
    this.fpsIntervalId = setInterval(this.logFps, 1000);

    this.pipBtn = document.getElementById("pip-btn");
    this.pipVideo = null;
    const testVideo = document.createElement("video");
    if (
      document.pictureInPictureEnabled &&
      typeof testVideo.requestPictureInPicture === "function"
    ) {
      this.pipBtn.addEventListener("click", this.onPipClick);
    } else {
      this.pipBtn = null;
    }
  }

  logFps = () => {
    console.log(`[decoder] fps: ${this.framesThisSecond}`);
    this.framesThisSecond = 0;
  };

  closeWithError(msg) {
    if (this.closed) return;
    this.closed = true;
    console.error(msg);
    this.errorDiv.textContent = msg;
    this.errorDiv.style.display = "flex";
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

  wsEventMessage = (ev) => {
    this.msgChain = this.msgChain.then(() => this.handleMessage(ev));
  };

  handleMessage = async (ev) => {
    if (!(ev.data instanceof ArrayBuffer)) {
      return;
    }

    const buf = new Uint8Array(ev.data);
    if (buf[0] === 0) {
      // Parameters. 1-byte type marker, RFC 6381 codec string, NUL byte, u16 width, u16 height, extra data blob.
      const nulIndex = buf.indexOf(0, 1);
      if (nulIndex === -1) {
        this.closeWithError(
          "[websocket] invalid parameters message: no NUL byte",
        );
        return;
      }
      const codec = new TextDecoder().decode(buf.slice(1, nulIndex));
      const view = new DataView(buf.buffer, buf.byteOffset + nulIndex + 1);
      const codedWidth = view.getUint16(0);
      const codedHeight = view.getUint16(2);
      const description = buf.slice(nulIndex + 5);
      console.log(
        `[websocket] new parameters, codec=${codec} ${codedWidth}x${codedHeight}`,
      );

      const config = {
        codec,
        codedWidth,
        codedHeight,
        description,
        optimizeForLatency: true,
      };
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
      const timestamp = Number(new DataView(buf.buffer).getBigInt64(1));
      const type = buf[9] === 1 ? "key" : "delta";
      const data = buf.slice(10);
      if (this.decoder.state === "configured") {
        this.decoder.decode(
          new EncodedVideoChunk({
            type,
            timestamp,
            data: data,
          }),
        );
      }
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

  renderFrame(frame) {
    // Keep the canvas intrinsic size equal to the frame's native resolution.
    // CSS handles visual scaling (width/height: 100%) with letterboxing via
    // object-fit on the canvas. The captureStream() PiP window then inherits
    // the correct aspect ratio from the canvas's intrinsic dimensions.
    if (
      frame.displayWidth !== this.canvas.width ||
      frame.displayHeight !== this.canvas.height
    ) {
      this.canvas.width = frame.displayWidth;
      this.canvas.height = frame.displayHeight;
    }
    this.ctx.drawImage(frame, 0, 0);
  }

  onPipClick = async () => {
    try {
      if (document.pictureInPictureElement) {
        await document.exitPictureInPicture();
        this.pipBtn.textContent = "⧉ PiP";
      } else {
        if (this.pipVideo === null) {
          // Defer captureStream() until first use; calling it eagerly can
          // interfere with VideoDecoder initialization in Safari.
          this.pipVideo = document.createElement("video");
          this.pipVideo.muted = true;
          this.pipVideo.srcObject = this.canvas.captureStream();
          this.pipVideo.addEventListener("leavepictureinpicture", () => {
            this.pipBtn.textContent = "⧉ PiP";
          });
        }
        await this.pipVideo.play();
        await this.pipVideo.requestPictureInPicture();
        this.pipBtn.textContent = "✕ PiP";
      }
    } catch (e) {
      console.error("[pip]", e);
    }
  };

  decodeEventOutput = (frame) => {
    if (!this.hasFrame && this.pipBtn) {
      this.hasFrame = true;
      this.pipBtn.style.display = "block";
    }
    this.renderFrame(frame);
    frame.close();
    this.framesThisSecond++;
  };

  decodeEventError = (error) => {
    this.closeWithError(`[decoder] error: ${error}`);
  };
}

function init() {
  console.log("[init] starting");
  try {
    new Decoder();
  } catch (e) {
    console.error("[init]", e.message);
    const errorDiv = document.getElementById("error");
    errorDiv.textContent = e.message;
    errorDiv.style.display = "flex";
  }
}

window.addEventListener("load", init);
