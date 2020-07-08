from http.server import SimpleHTTPRequestHandler, HTTPServer
from cryptopal import hmac_sha1, insecure_compare, b
from urllib.parse import urlparse, parse_qs
from binascii import unhexlify

def verify(val, sig):
  key = 'you will never guess my key'
  return insecure_compare(hmac_sha1(b(key), b(val)), unhexlify(b(sig)))

class MyHTTPRequestHandler(SimpleHTTPRequestHandler):

  def do_GET(self):
    query = parse_qs(urlparse(self.path).query)
    filename, signature = query['file'][0], query['signature'][0]

    valid = verify(filename, signature)

    if not valid:
      self.send_response(500)
      self.end_headers()
    else:
      self.send_response(200)
      self.send_header("Content-Type", 'application/octet-stream')
      self.end_headers()
      self.wfile.write(open(filename))

if __name__ == '__main__':
  httpd = HTTPServer(('', 8181), MyHTTPRequestHandler)
  sa = httpd.socket.getsockname()
  print("Serving HTTP on", sa[0], "port", sa[1], "...")
  httpd.serve_forever()
