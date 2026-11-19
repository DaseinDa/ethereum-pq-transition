"""Bounded read-only transport for PUBLIC execution materials on a local devnet.

This is availability transport, never an execution-validity or signing oracle.
The receiving Ream/geth pair must validate the complete payload with newPayloadV4.
No private keys, chain databases, Engine JWT or signing history are served.
"""
import argparse
import http.server
import json
import os
from pathlib import Path
import re
import socketserver
import threading

MAX_BYTES = 2 * 1024 * 1024
PATH = re.compile(r"/([0-9a-f]{64})\.json\Z")


class Server(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    request_queue_size = 8

    def __init__(self, address, directory):
        self.directory = directory.resolve(strict=True)
        self.workers = threading.BoundedSemaphore(4)
        super().__init__(address, Handler)

    def process_request(self, request, client_address):
        if not self.workers.acquire(blocking=False):
            self.shutdown_request(request)
            return
        try:
            super().process_request(request, client_address)
        except BaseException:
            self.workers.release()
            raise

    def process_request_thread(self, request, client_address):
        try:
            request.settimeout(3)
            super().process_request_thread(request, client_address)
        finally:
            self.workers.release()


class Handler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        match = PATH.fullmatch(self.path)
        if not match:
            self.send_error(404)
            return
        candidate = self.server.directory / (match[1] + ".json")
        try:
            # Do not follow symlinks out of the dedicated public materials store.
            fd = os.open(candidate, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
            with os.fdopen(fd, "rb") as source:
                import stat
                info = os.fstat(source.fileno())
                if not stat.S_ISREG(info.st_mode) or info.st_size > MAX_BYTES:
                    self.send_error(413)
                    return
                raw = source.read(MAX_BYTES + 1)
            if len(raw) > MAX_BYTES:
                self.send_error(413)
                return
            data = json.loads(raw)
            if data.get("blockHash") != "0x" + match[1]:
                self.send_error(409)
                return
        except (OSError, ValueError, AttributeError):
            self.send_error(404)
            return
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--directory", type=Path, required=True)
    p.add_argument("--port", type=int, required=True)
    a = p.parse_args()
    if not a.directory.is_absolute() or not 1024 <= a.port <= 65535:
        p.error("absolute dedicated public-material directory and explicit unprivileged port required")
    Server(("127.0.0.1", a.port), a.directory).serve_forever()


if __name__ == "__main__":
    main()
