#!/bin/python

from collections import Counter, defaultdict
from Crypto.Cipher import AES
from Crypto.Util.number import long_to_bytes, bytes_to_long
from random import randint, shuffle
import itertools
import hashlib
from time import time, sleep

def random_bytes(n):
  return ''.join(chr(randint(0, 255)) for _ in range(n))

def xor(text, key):
  return ''.join([chr(ord(c1) ^ ord(c2)) for c1, c2 in zip(text, itertools.cycle(key))])

def chunk(s, bs):
  return [s[i:i + bs] for i in range(0, len(s), bs)]

def chunk_pp(s, bs):
  return map(lambda c: c.encode('hex'), chunk(s, bs))

def ichunk(s, bs):
  for i in xrange(0, len(s), bs):
    yield s[i:i + bs]

def pkcs7pad(s, bs):
  pad = bs - (len(s) % bs)
  return '%s%s' % (s, chr(pad) * pad)

def pkcs7unpad(s):
  pad = ord(s[-1])
  if s[-pad:] != chr(pad) * pad:
    raise PaddingException('Bad padding')
  return s[:-pad]

class PaddingException(Exception):
  pass

def pairwise(iterable):
    "s -> (s0,s1), (s1,s2), (s2, s3), ..."
    a, b = itertools.tee(iterable)
    next(b, None)
    return zip(a, b)

def score_english(msg):
  english = "etaonrishd .,\nlfcmugypwbvkjxqz-_!?'\"/1234567890*";
  #english = ' etaoinshrdlcumwfgypbvkjxqz'

  stats = Counter(filter(lambda c: c.lower() in english, msg))
  score = 0

  for c in msg:
    where = english.find(c)
    if where == -1:
      continue
    else:
      score += (len(english) - where) * 2

  return score, stats

def crack_single_char_xor(ciphertext):
  best_score, best_char = 0, '\x00'

  for char in map(chr, range(256)):
    xored = xor(ciphertext, char)
    score, _ = score_english(xored)

    if score > best_score:
      best_score, best_char = score, char

  return best_char

def hamming(str1, str2):
  return sum(bin(ord(c1) ^ ord(c2)).count('1') for c1, c2 in zip(str1, str2))

def find_xor_keysize(ciphertext):

  distances = {}

  for keysize in range(2, 40):
  
    dists = []
    for i in range(0, len(ciphertext) - keysize * 4, keysize):
  
      m1 = ciphertext[i:i+keysize]
      m2 = ciphertext[i+keysize:i+keysize*2]
      m3 = ciphertext[i+keysize*2:i+keysize*4]
      m4 = ciphertext[i+keysize*3:i+keysize*5]
  
      avg = (hamming(m1, m2) + hamming(m2, m3) + hamming(m3, m4) + hamming(m4, m1)) / 4.0
      dists.append(avg / keysize)
  
    distances[keysize] = sum(dists) / len(dists)
  
  return sorted(distances.items(), key=lambda x: x[1])

def find_xor_key(ciphertext, keysize):

  transposed = []
  for i in range(0, keysize):

    chars = ''

    for block in chunk(ciphertext, keysize):

      if i >= len(block):
        break

      chars += block[i]
  
    transposed.append(chars)
  
  key = ''
  for chars in transposed:
    key += crack_single_char_xor(chars)

  return key

def flip(ciphertext, oracle):
  for i in range(len(ciphertext)):
    payload = ciphertext[:i] + chr(ord(ciphertext[i]) + 1) + ciphertext[i + 1:]
    yield i, oracle(payload)

def oracle(ct):
  url = 'http:// /%s' % ct
  r = requests.get(url)
  return r

def detect_ecb(ciphertext):
  
  for bs in [16, 32, 8, 12, 24]:
    blocks = chunk(ciphertext, bs)
    stats = Counter(blocks)
    
    if stats.values() != [1]:
      break

  stats = [(b, c) for b, c in stats.iteritems() if c > 1]
  return stats

def detect_ecb2(ciphertext):

  for bs in [16, 32, 8, 12, 24]:

    blocks = chunk(ciphertext, bs)
    stats = defaultdict(lambda: 1)

    for i in range(1, len(blocks)):
      if blocks[i] == blocks[i - 1]:
        stats[blocks[i]] += 1

    if stats:
      break
  
  stats = [(b, c) for b, c in stats.iteritems() if c > 1]
  return stats

def find_blocksize(encryption_oracle):
  prev_size = 0

  for i in range(512):
    size = len(encryption_oracle('A'*i))

    if prev_size > 0 and size != prev_size:
      break

    prev_size = size

  return size - prev_size

def sizeof_pfxsfx(encryption_oracle, bs):

#  skip = []
#  blocks = chunk(encryption_oracle('', bs))
#  for i in range(1, len(blocks)):
#    if blocks[i] == blocks[i - 1]:
#      skip.append(blocks[i])
#  if skip:
#    raise Exception('this is fucked up')

  def indexof_pair(blocks):
    for i in range(1, len(blocks)):
      if blocks[i] == blocks[i - 1]:
        return i - 1
    return -1

  candidates = []
  for c in 'ABC':
    for n in range(bs * 3):
      blocks = chunk(encryption_oracle(c * n), bs)
      i = indexof_pair(blocks)
      if i >= 0:
        candidates.append((n, c, i, blocks))
        break

  n, c, i, base = max(candidates)

  prefix_size = 0

  if base[0] != base[i]:

    for m in range(bs * 2):
      x = chunk(encryption_oracle(c * (n + m)), bs)

      if x.count(base[i]) == 3:
        break

    prefix_size = (bs * i) - ((n + m) % bs)

  suffix_size = 0

  if base[-1] != base[i]:

    for m in range(bs * 2):
      x = chunk(encryption_oracle(c * (n + m)), bs)

      if len(x) > len(base):
        break

    suffix_size = ((len(x) - 1) * bs) - (prefix_size + n + m)

  return prefix_size, suffix_size, c

def decrypt_suffix(encryption_oracle, bs=None, prefix_size=None, suffix_size=None, char=None, verbose=False):

  if bs is None:
    bs = find_blocksize(encryption_oracle)

  if verbose:
    print '[+] blocksize: %d' % bs

  if prefix_size is None or suffix_size is None or char is None:
    prefix_size, suffix_size, char = sizeof_pfxsfx(encryption_oracle, bs)

  if verbose:
    print '[+] prefix_size: %d, suffix_size: %d, char: %s' % (prefix_size, suffix_size, char)

  ref_index = (prefix_size + suffix_size) / bs
  decrypted = ''

  for n in reversed(range(suffix_size + (bs - ((prefix_size + suffix_size) % bs)))):
    data = char * n
    ref_block = chunk(encryption_oracle(data), bs)[ref_index]

    for c in map(chr, range(256)):
      msg = '%s%s%s' % (data, ''.join(decrypted), c)

      if ref_block == chunk(encryption_oracle(msg), bs)[ref_index]:
        decrypted += c
        if verbose:
          print '%r' % decrypted
        break
    else:
      decrypted += '?'

  return decrypted[:suffix_size]

def encrypt_ecb(msg, key):
  return AES.new(key, mode=AES.MODE_ECB).encrypt(msg)

def decrypt_ecb(msg, key):
  return AES.new(key, mode=AES.MODE_ECB).decrypt(msg)

def encrypt_cbc(msg, key, iv):
  ct = iv
  result = ''
  for pt in chunk(msg, len(key)):
    ct = encrypt_ecb(xor(ct, pt), key)
    result += ct

  return iv + result

def decrypt_cbc(msg, key, iv=None):
  if iv:
    msg = iv + msg
  result = ''
  for prev_ct, ct in pairwise(chunk(msg, len(key))):
    result += xor(prev_ct, decrypt_ecb(ct, key))

  return result

class CTRCipher:
  def __init__(self, key, nonce):
    self.key = key
    self.nonce = nonce

  def encrypt(self, msg):
    def pack(n):
      return ''.join(chr((n >> i) & 0xFF) for i in range(0, 64, 8))
    
    block_count = 0
    result = ''

    for block in chunk(msg, len(self.key)):
    
      counter = pack(self.nonce) + pack(block_count)
      keystream = encrypt_ecb(counter, self.key)
      block_count += 1
    
      result += xor(block, keystream)

    return result

  def decrypt(self, msg):
    return self.encrypt(msg) 

# hash length extension
class SHA1:

  def __init__(self):
    self._h0, self._h1, self._h2, self._h3, self._h4 = 0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0

  def transform(self, chunk):
    lrot = lambda x, n: (x << n) | (x >> (32 - n))
    w = []

    for j in xrange(len(chunk) // 32):
        w.append(int(chunk[j * 32:j * 32 + 32], 2))

    for i in xrange(16, 80):
        w.append(lrot(w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16], 1)
            & 0xffffffff)

    a = self._h0
    b = self._h1
    c = self._h2
    d = self._h3
    e = self._h4

    for i in xrange(80):

        if i <= i <= 19:
            f, k = d ^ (b & (c ^ d)), 0x5a827999
        elif 20 <= i <= 39:
            f, k = b ^ c ^ d, 0x6ed9eba1
        elif 40 <= i <= 59:
            f, k = (b & c) | (d & (b | c)), 0x8f1bbcdc
        elif 60 <= i <= 79:
            f, k = b ^ c ^ d, 0xca62c1d6

        temp = lrot(a, 5) + f + e + k + w[i] & 0xffffffff
        a, b, c, d, e = temp, a, lrot(b, 30), c, d

    self._h0 = (self._h0 + a) & 0xffffffff
    self._h1 = (self._h1 + b) & 0xffffffff
    self._h2 = (self._h2 + c) & 0xffffffff
    self._h3 = (self._h3 + d) & 0xffffffff
    self._h4 = (self._h4 + e) & 0xffffffff

  def update(self, message):
    length = format(len(message) * 8, '064b')

    message = ''.join(format(ord(c), '08b') for c in message) + '1'
    while not len(message) % 512 == 448:
      message += '0'
    message += length

    for i in range(len(message) // 512):
      self.transform(message[i * 512:i * 512 + 512])

  def extend(self, append, original, digest, prefix_len):

    length = prefix_len + len(original) + 1
    while not length % 64 == 56:
      length += 1
    length += len(append)
    length += 8
    length = format(length * 8, '064b')

    message = ''.join(format(ord(c), '08b') for c in append) + '1'
    while not len(message) % 512 == 448:
      message += '0'
    message += length

    self._h0, self._h1, self._h2, self._h3, self._h4 = [int(digest[i:i + 8], 16) for i in range(0, len(digest), 8)]

    for i in range(len(message) // 512):
      self.transform(message[i * 512:i * 512 + 512])

    padded = original + '\x80'
    while not (prefix_len + len(padded)) % 64 == 56:
      padded += '\x00'
    padded += format((prefix_len + len(original)) * 8, '016x').decode('hex')

    return padded + append

  def hexdigest(self):
    return ''.join('%08x' % i for i in (self._h0, self._h1, self._h2, self._h3, self._h4))

  def digest(self):
    return hexdigest().decode('hex')

# HMAC
def hmac_sha1(key, msg):
  if len(key) > 64:
    key = hashlib.sha1(key).digest()
  if len(key) < 64:
    key += '\x00' * (64 - len(key))
  o_key_pad = xor('\x5c' * 64, key)
  i_key_pad = xor('\x36' * 64, key)
  return hashlib.sha1(o_key_pad + hashlib.sha1(i_key_pad + msg).digest()).digest()

def hmac_oracle_mock(msg, sig):
  key = 'you will never guess my key'
  sleep(randint(0, 5) / 1000)
  return insecure_compare(hmac_sha1(key, msg), sig)

import requests
def hmac_oracle(msg, sig):
  r = requests.get('http://127.0.0.1:8181/?file=%s&signature=%s' % (msg, sig.encode('hex')))
  return r.status_code == 200

def insecure_compare(s1, s2):
  for c1, c2 in zip(s1, s2):
    if c1 != c2:
      return False
    sleep(.005)
  return True

class Timing:
  def __enter__(self):
    self.t1 = time()
    return self

  def __exit__(self, exc_type, exc_value, traceback):
    self.time = time() - self.t1

def break_hmac():
  filename = '/etc/passwd'
  found = ''

  rounds = 10 
  while True:
    stats = Counter()
    for _ in range(rounds):
      for c in map(chr, range(256)):
        signature = found + c + '\x00' * (20 - 1 - len(found))
        with Timing() as timing:
          if hmac_oracle_mock(filename, signature):
            print 'found signature for %s is %r' % (filename, found)
            return found

        stats[c] += timing.time

    top5 = stats.most_common(5)
    print 'top 5: %r' % top5

    found += top5[0][0]
    print 'found so far: %r' % found

# Unit Tests
import unittest
class Tests(unittest.TestCase):

  def test_sha1_hash(self):
    for size in range(1000):
      data = random_bytes(size)
      
      sha = SHA1()
      sha.update(data)

      self.assertTrue(sha.hexdigest() == hashlib.sha1(data).hexdigest())

  def test_sha1_extend(self):
    def make_mac(msg):
      return hashlib.sha1(key + msg).hexdigest()
    
    def check_mac(msg, mac):
      return mac and mac == make_mac(msg)

    for key_size in range(30):
      key = random_bytes(key_size)

      for msg_size in range(60):
        for append_size in range(20):

          msg = random_bytes(msg_size)
          mac = make_mac(msg)

          append_msg = random_bytes(append_size)

          sha = SHA1()
          forged_msg = sha.extend(append_msg, msg, mac, key_size)
          forged_mac = sha.hexdigest()

          self.assertTrue(check_mac(forged_msg, forged_mac))

  def test_find_xor_keysize(self):
    for keysize in range(1, 40):
      key = random_bytes(keysize)
      ciphertext = xor(plaintext * 4, key)
      
      found_keysize = find_xor_keysize(ciphertext)[0][0]
      self.assertTrue(found_keysize % keysize == 0)

  def test_find_xor_key(self):
    for keysize in range(1, 40):
      key = random_bytes(keysize)
      ciphertext = xor(plaintext, key)

      found_keysize = find_xor_keysize(ciphertext)[0][0]
      found_key = find_xor_key(ciphertext, found_keysize)

      self.assertTrue(xor(ciphertext, found_key) == plaintext)
      
  def test_encrypt_decrypt_cbc(self):
    for bs in block_sizes:
      for msg_size in xrange(bs * 3):
        msg = random_bytes(msg_size)
        key = random_bytes(bs)
        iv = random_bytes(bs)
        
        enc = encrypt_cbc(pkcs7pad(msg, bs), key, iv)
        dec = pkcs7unpad(decrypt_cbc(enc, key))

        self.assertTrue(dec == msg)

  def test_find_blocksize(self):

    def encryption_oracle(s):
      return encrypt_ecb(pkcs7pad(s, bs), key)

    for bs in block_sizes:
      for _ in xrange(100):
        key = random_bytes(bs)

        self.assertTrue(bs == find_blocksize(encryption_oracle))
    

  def test_detect_ecb(self):

    for bs in block_sizes:
      for n in xrange(100):
        key = random_bytes(bs)
        blocks = ['A' * bs] * 2
        for _ in xrange(n):
          blocks.append(random_bytes(bs))
        shuffle(blocks)
        data = ''.join(blocks)

        if randint(0, 1) == 0:
          ct = encrypt_cbc(pkcs7pad(data, bs), key, random_bytes(bs))
          #print 'CBC ct: %s' % map(lambda s: s.encode('hex'), chunk(ct, bs))
          self.assertFalse(detect_ecb(ct))
        else:
          ct = encrypt_ecb(pkcs7pad(data, bs), key)
          #print 'ECB ct: %s' % map(lambda s: s.encode('hex'), chunk(ct, bs))
          self.assertTrue(detect_ecb(ct))

  def test_sizeof_pfxsfx(self):

    def encryption_oracle(s):
      data = '%s%s%s' % (pfx, s, sfx)
      return encrypt_ecb(pkcs7pad(data, bs), key)

    for bs in block_sizes:
      for max_size in xrange(0, bs * 3):
        key = random_bytes(bs)
        pfx = random_bytes(randint(0, max_size))
        sfx = random_bytes(randint(0, max_size))

        pfx_size, sfx_size, _ = sizeof_pfxsfx(encryption_oracle, bs)

        self.assertTrue((pfx_size, sfx_size) == (len(pfx), len(sfx)))

  def test_decrypt_suffix(self):

    def encryption_oracle(s):
      data = '%s%s%s' % (pfx, s, sfx)
      return encrypt_ecb(pkcs7pad(data, bs), key)

    for bs in block_sizes:
      for max_size in xrange(0, bs * 3):
        key = random_bytes(bs)
        pfx = random_bytes(randint(0, max_size))
        sfx = random_bytes(randint(0, max_size))

        decrypted = decrypt_suffix(encryption_oracle)

        self.assertTrue(decrypted == sfx)

  def test_pkcs7unpad(self):

    for bs in block_sizes:
      for msg_size in xrange(bs * 3):
        msg = random_bytes(msg_size)
        padded = pkcs7pad(msg, bs)
        unpadded = pkcs7unpad(padded)
        self.assertTrue(unpadded == msg)

        pad = ord(padded[-1])
        new = padded[-pad:] + chr(pad + 1) * pad
        with self.assertRaises(PaddingException):
          pkcs7unpad(new)

  def test_encrypt_decrypt_ctr(self):

    for bs in block_sizes:
      for msg_size in xrange(1, 1000):
        key = random_bytes(bs)
        msg = random_bytes(msg_size)

      self.assertTrue(CTRCipher(key, 0).decrypt(CTRCipher(key, 0).encrypt(msg)) == msg)

if __name__ == '__main__':
  plaintext = '''In 2071, roughly sixty years after an accident with a hyperspace gateway made the Earth uninhabitable, humanity has colonized most of the rocky planets and moons of the Solar System.\n Amid a rising crime rate, the Inter Solar System Police (ISSP) set up a legalized contract system, in which registered bounty hunters (also referred to as "Cowboys") chase criminals and bring them in alive in return for a reward.\n The series protagonists are bounty hunters working from the spaceship Bebop.\n The original crew are Spike Spiegel, an exiled former hitman of the criminal Red Dragon Syndicate, and his partner Jet Black, a former ISSP officer.\n They are later joined by Faye Valentine, an amnesiac con artist; Edward Wong, an eccentric girl skilled in hacking; and Ein, a genetically-engineered Pembroke Welsh Corgi with human-like intelligence.\n Over the course of the series, the team get involved in disastrous mishaps leaving them out of pocket, while often confronting faces and events from their past: these include Jet's reasons for leaving the ISSP, and Faye's past as a young woman from Earth injured in an accident and cryogenically frozen to save her life'''
  block_sizes = [16, 32]
  unittest.main()

# vim: ts=2 sw=2 sts=2 et fdm=marker bg=dark
