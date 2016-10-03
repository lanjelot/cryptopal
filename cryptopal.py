from collections import Counter, defaultdict
from Crypto.Cipher import AES
from Crypto.Util.number import long_to_bytes, bytes_to_long
from random import randint, shuffle
import itertools
import hashlib
from time import time, sleep
from threading import Thread
from Queue import Queue, Empty
import struct
import logging

# Utils {{{
def base36encode(number):
    if not isinstance(number, (int, long)):
        raise TypeError('number must be an integer')
    if number < 0:
        raise ValueError('number must be positive')

    alphabet, base36 = ['0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ', '']

    while number:
        number, i = divmod(number, 36)
        base36 = alphabet[i] + base36

    return base36 or alphabet[0]

def base36decode(number):
    return int(number, 36)

def random_bytes(n):
  return ''.join(chr(randint(0, 255)) for _ in range(n))

def random_printables(n):
  return ''.join(chr(randint(32, 126)) for _ in range(n))

def random_chars(n, charset='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789 '):
  return ''.join(charset[randint(0, len(charset)-1)] for _ in range(n))

def xor(text, key):
  return ''.join([chr(ord(c1) ^ ord(c2)) for c1, c2 in itertools.izip(text, itertools.cycle(key))])

def chunk(s, bs):
  return [s[i:i + bs] for i in range(0, len(s), bs)]

def chunk_pp(s, bs):
  return map(lambda c: c.encode('hex'), chunk(s, bs))

def ichunk(s, bs):
  for i in xrange(0, len(s), bs):
    yield s[i:i + bs]

def _long_to_bytes(n):
  s = '%x' % n
  s = s if len(s) % 2 == 0 else '0' + s
  return s.decode('hex')

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

def count_printable(msg):
  return len([c for c in msg if ord(c) >= 0x20 and ord(c) < 0x7f])

def byteflip(ciphertext, oracle):
  '''Flip only one bit in a byte'''

  for i in range(len(ciphertext)):
    payload = ciphertext[:i] + chr((ord(ciphertext[i]) + 1) % 256) + ciphertext[i + 1:]
    yield i, oracle(payload)

def bitflip(ciphertext, oracle):
  '''Flip every bit in a byte'''

  for i in range(len(ciphertext)):
    for n in range(7, 0, -1):
      payload = ciphertext[:i] + chr(ord(ciphertext[i]) ^ (1 << n)) + ciphertext[i + 1:]
      yield i, oracle(payload)

def bitflipall(ciphertext, oracle):
  '''Test all values in a byte
  ctext: 01001001
  flips: 00000000
         00000001
         00000010
         11111111 (255)
  '''
  for i in range(len(ciphertext)):
    for n in range(256):
      payload = ciphertext[:i] + chr(n) + ciphertext[i + 1:]
      yield i, oracle(payload)

# }}}

# XOR {{{
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

# }}}

# ECB {{{
def detect_ecb(ciphertext):
  for bs in [16, 32, 8, 12, 24]:
    blocks = chunk(ciphertext, bs)
    stats = Counter(blocks)
    
    if stats.values() != [1]:
      break

  stats = [(b, c) for b, c in stats.iteritems() if c > 1]
  return stats

def detect_ecb2(ciphertext):
  '''using defaultdict instead of Counter'''
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
    for n in range(bs, bs * 3):
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

def decrypt_suffix(encryption_oracle, bs=None, prefix_size=None, suffix_size=None, char=None, verbose=False, charset=None):
  if bs is None:
    bs = find_blocksize(encryption_oracle)

  if verbose:
    print '[+] blocksize: %d' % bs

  if prefix_size is None or suffix_size is None or char is None:
    prefix_size, suffix_size, char = sizeof_pfxsfx(encryption_oracle, bs)

  if charset is None:
    charset = map(chr, range(256))

  if verbose:
    print '[+] prefix_size: %d, suffix_size: %d, char: %s' % (prefix_size, suffix_size, char)

  ref_index = (prefix_size + suffix_size) / bs
  decrypted = ''

  for n in reversed(range(suffix_size + (bs - ((prefix_size + suffix_size) % bs)))):
    data = char * n
    ref_block = chunk(encryption_oracle(data), bs)[ref_index]

    for c in charset:
      msg = '%s%s%s' % (data, ''.join(decrypted), c)

      if ref_block == chunk(encryption_oracle(msg), bs)[ref_index]:
        decrypted += c
        if verbose:
          print '%r' % decrypted
        break
    else:
      decrypted += '?'

  return decrypted[:suffix_size]

# }}}

# Padding Oracle {{{
class PaddingOracle:
  '''Added multithreading to https://github.com/mwielgoszewski/python-paddingoracle'''

  def __init__(self, max_retries=5):
    self.max_retries = max_retries

  def pop_result(self):
    '''Ctrl-C friendly :)'''

    while True:
      try:
        return self.resultq.get_nowait()
      except Empty:
        sleep(.1)

  def encrypt(self, plaintext, block_size, iv=None):
    '''Encryption cannot be multithreaded'''

    plaintext = pkcs7pad(plaintext, block_size)

    if iv is None:
      iv = '\x00' * block_size

    encrypted = iv
    blocks = chunk(plaintext, block_size)
    self.resultq = Queue()

    block = iv
    for prev in blocks[::-1]:

      self.bust(block, block_size)

      _, inter = self.pop_result()
      block = xor(inter, prev)

      encrypted = block + encrypted

    return encrypted

  def decrypt(self, ciphertext, block_size):
    '''Decrypt each block in a thread'''

    decrypted = {}
    blocks = chunk(ciphertext, block_size)
    self.resultq = Queue()

    for block in blocks[1:]:
      t = Thread(target=self.bust, args=(block, block_size))
      t.daemon = True
      t.start()

    try:
      while True:
        block, inter = self.pop_result()
        idx = blocks.index(block)
        decrypted[idx] = xor(inter, blocks[idx - 1])

        logging.info('Decrypted block %d: %r' % (idx, decrypted[idx]))

        if len(decrypted) == len(blocks) - 1:
          break

    except KeyboardInterrupt:
      pass

    return ''.join(s for _, s in sorted(decrypted.iteritems()))

  def bust(self, block, block_size):
    logging.debug('Processing block %r', block)

    intermediate_bytes = bytearray(block_size)
    test_bytes = bytearray(block_size) + block

    retries = 0
    last_ok = 0
    while retries < self.max_retries:

      for byte_num in reversed(xrange(block_size)):

        r = 256
        if byte_num == block_size - 1 and last_ok > 0:
          r = last_ok

        for i in reversed(xrange(r)):

          test_bytes[byte_num] = i

          try:
            self.oracle(str(test_bytes))

            if byte_num == block_size - 1:
                last_ok = i

          except PaddingException:
            continue

          current_pad_byte = block_size - byte_num
          next_pad_byte = block_size - byte_num + 1
          decrypted_byte = test_bytes[byte_num] ^ current_pad_byte

          intermediate_bytes[byte_num] = decrypted_byte

          for k in xrange(byte_num, block_size):
            test_bytes[k] ^= current_pad_byte
            test_bytes[k] ^= next_pad_byte

          break

        else:
          logging.debug("byte %d not found, restarting" % byte_num)
          retries += 1

          break

      else:
        break

    else:
      raise RuntimeError('Could not decrypt byte %d in %r within '
                         'maximum allotted retries (%d)' % (
                         byte_num, block, self.max_retries))

    self.resultq.put((block, str(intermediate_bytes)))

# }}}

# CBC {{{
def encrypt_ecb(msg, key):
  return AES.new(key, mode=AES.MODE_ECB).encrypt(msg)

def decrypt_ecb(msg, key):
  return AES.new(key, mode=AES.MODE_ECB).decrypt(msg)

def encrypt_cbc(msg, key, iv):
  ct = iv
  result = ''
  for pt in chunk(msg, AES.block_size):
    ct = encrypt_ecb(xor(ct, pt), key)
    result += ct

  return iv + result

def decrypt_cbc(msg, key, iv=None):
  if iv:
    msg = iv + msg
  result = ''
  for prev_ct, ct in pairwise(chunk(msg, AES.block_size)):
    result += xor(prev_ct, decrypt_ecb(ct, key))

  return result

# }}}

# CTR {{{
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

# }}}

# MT19937 {{{
class MT19937:
  w, n, m, r = 32, 624, 397, 31
  a = 0x9908B0DF
  u = 11
  s, b = 7, 0x9d2c5680
  t, c = 15, 0xefc60000
  l = 18
  f = 1812433253

  def __init__(self, seed=None):
    self.index = MT19937.n + 1
    self.MT = [0] * MT19937.n

    lower_mask = (1 << MT19937.r) - 1
    upper_mask = (1 << MT19937.r)

    wbit_mask = (1 << MT19937.w) - 1  # lowest w bits mask

    if seed is not None:
      self.seed_mt(seed)

  def seed_mt(self, seed):
    self.index = MT19937.n
    self.MT[0] = seed
    for i in xrange(1, MT19937.n):
      self.MT[i] = to_int32(
        MT19937.f * (self.MT[i - 1] ^ (self.MT[i - 1] >> (MT19937.w - 2))) + i)

  def extract_number(self):
    if self.index >= MT19937.n:
      if self.index > MT19937.n:
        raise Exception('Generator was never seeded, index: %d' % self.index)

      self.twist()

    y = self.MT[self.index]
    y = y ^ y >> MT19937.u
    y = y ^ y << MT19937.s & MT19937.b
    y = y ^ y << MT19937.t & MT19937.c
    y = y ^ y >> MT19937.l

    self.index = self.index + 1

    return to_int32(y)

  def twist(self):
    for i in xrange(MT19937.n):
      y = to_int32((self.MT[i] & 0x80000000) +
                 (self.MT[(i + 1) % MT19937.n] & 0x7fffffff))

      self.MT[i] = self.MT[(i + MT19937.m) % MT19937.n] ^ y >> 1

      if y % 2 != 0:
        self.MT[i] = self.MT[i] ^ MT19937.b

    self.index = 0

  @staticmethod
  def untemper(y):
    def undo_right_shift_xor(y, s):
      z = 0
      for i in range(32):
        z = set_MSB(z, i, get_MSB(y, i) ^ get_MSB(z, i - s))
      return z

    def undo_left_shift_xor_and(y, s, k):
      z = 0
      for i in range(32):
       z = set_LSB(z, i, get_LSB(y, i) ^ (get_LSB(z, i - s) & get_LSB(k, i)))
      return z

    '''Invert the temper transform'''
    y = undo_right_shift_xor(y, MT19937.l)
    y = undo_left_shift_xor_and(y, MT19937.t, MT19937.c)
    y = undo_left_shift_xor_and(y, MT19937.s, MT19937.b)
    y = undo_right_shift_xor(y, MT19937.u)
    return y

def to_int32(x):
  ''' Get the 32 least significant bits'''
  return int(0xffffffff & x)

def get_MSB(x, n):
  '''Get the nth most significant bit'''
  if n < 0:
    return 0
  return (x >> (31 - n)) & 1

def set_MSB(x, n, b):
  '''Set the nth most significant bit'''
  return x | (b << (31 - n))

def get_LSB(x, n):
  '''Get the nth least significant bit'''
  if n < 0:
    return 0
  return (x >> n) & 1

def set_LSB(x, n, b):
  '''Set the nth least significant bit'''
  return x | (b << n)

def mt_encryptdecrypt(msg, key):
  mt = MT19937(key)

  if len(msg) == 0:
    return ''

  keystream = ''
  while len(keystream) < len(msg):
    keystream += struct.pack('<I', (mt.extract_number()))

  if len(keystream) > len(msg):
    keystream = keystream[:len(msg)]

  return xor(msg, keystream)

# }}}

# Hash Length Extension {{{
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

# }}}

# HMAC {{{
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

# }}}

# Unit Tests {{{
import unittest
class Tests(unittest.TestCase):

  # Utils {{{
  def test_pkcs7unpad(self):

    for bs in xrange(100):
      for msg_size in xrange(bs * 3):

        msg = random_bytes(msg_size)
        padded = pkcs7pad(msg, bs)
        unpadded = pkcs7unpad(padded)
        self.assertTrue(unpadded == msg)

        pad = ord(padded[-1])
        new = padded[-pad:] + chr(pad + 1) * pad
        with self.assertRaises(PaddingException):
          pkcs7unpad(new)
  # }}}

  # XOR {{{
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
  # }}}

  # ECB {{{
  def test_find_blocksize(self):

    def encryption_oracle(s):
      pt = pkcs7pad(s, AES.block_size)
      if mode == 'ECB':
        return encrypt_ecb(pt, key)
      elif mode == 'CBC':
        return encrypt_cbc(pt, key, iv)

    for mode in ['ECB', 'CBC']:
      for key_size in AES.key_size:
        for _ in xrange(100):
          key = random_bytes(key_size)
          iv = random_bytes(AES.block_size)

          self.assertTrue(AES.block_size == find_blocksize(encryption_oracle))

  def test_detect_ecb(self):
    '''https://cryptopals.com/sets/2/challenges/11'''

    def encryption_oracle(s, pfx_size, sfx_size):
      key = random_bytes(16)
      pfx = random_bytes(pfx_size)
      sfx = random_bytes(sfx_size)

      data = pkcs7pad(pfx + s + sfx, AES.block_size)

      blocks = chunk(data, AES.block_size)
      shuffle(blocks)

      data = ''.join(blocks)

      if randint(0, 1) == 0:
        return encrypt_cbc(data, key, random_bytes(AES.block_size)), 'CBC'
      else:
        return encrypt_ecb(data, key), 'ECB'

    for pfx_size, sfx_size in itertools.product(range(50), repeat=2):
      ct, mode = encryption_oracle('A' * AES.block_size * 3, pfx_size, sfx_size)

      stats = detect_ecb(ct)
      if stats:
        self.assertTrue(mode == 'ECB')

  def test_sizeof_pfxsfx(self):

    def encryption_oracle(s):
      data = '%s%s%s' % (pfx, s, sfx)
      return encrypt_ecb(pkcs7pad(data, AES.block_size), key)

    for key_size in AES.key_size:
      for max_size in xrange(0, AES.block_size * 3):
        key = random_bytes(key_size)
        pfx = random_bytes(randint(0, max_size))
        sfx = random_bytes(randint(0, max_size))

        pfx_size, sfx_size, _ = sizeof_pfxsfx(encryption_oracle, AES.block_size)

        self.assertTrue((pfx_size, sfx_size) == (len(pfx), len(sfx)))

  def test_decrypt_suffix(self):
    '''https://cryptopals.com/sets/2/challenges/14'''

    def encryption_oracle(s):
      data = '%s%s%s' % (pfx, s, sfx)
      return encrypt_ecb(pkcs7pad(data, AES.block_size), key)

    for key_size in AES.key_size:
      for max_size in xrange(0, AES.block_size * 3):
        key = random_bytes(key_size)
        pfx = random_bytes(randint(0, max_size))
        sfx = random_bytes(randint(0, max_size))

        decrypted = decrypt_suffix(encryption_oracle)

        self.assertTrue(decrypted == sfx)
  # }}}

  # Padding Oracle {{{
  def test_padding_oracle_encrypt(self):
    key='YELLOW SUBMARINE'

    def oracle_decrypt(data):
      try:
        _ = pkcs7unpad(decrypt_cbc(data, key))
      except PaddingException:
        return 'error'

    class PadBuster(PaddingOracle):
      def oracle(self, data):
        if oracle_decrypt(data) == 'error':
          raise PaddingException

    padbuster = PadBuster()

    for i in xrange(10):
      msg = random_bytes(i * AES.block_size + randint(1, AES.block_size))
      forged = padbuster.encrypt(msg, AES.block_size)

      self.assertTrue(pkcs7unpad(decrypt_cbc(forged, key)) == msg)

  def test_padding_oracle_decrypt(self):
    key='YELLOW SUBMARINE'

    def oracle_decrypt(data):
      try:
        _ = pkcs7unpad(decrypt_cbc(data, key))
      except PaddingException:
        return 'error'

    class PadBuster(PaddingOracle):
      def oracle(self, data):
        if oracle_decrypt(data) == 'error':
          raise PaddingException

    padbuster = PadBuster()

    for i in xrange(10):
      msg = random_bytes(i * AES.block_size + randint(1, AES.block_size))
      ct = encrypt_cbc(pkcs7pad(msg, AES.block_size), key, random_bytes(AES.block_size))
      pt = padbuster.decrypt(ct, AES.block_size)
      self.assertTrue(pkcs7unpad(pt) == msg)
  # }}}

  # CBC {{{
  # TODO add tests with other algorithms (e.g. DES)
  def test_encrypt_decrypt_cbc(self):
    for key_size in AES.key_size:
      for msg_size in xrange(AES.block_size * 3):
        msg = random_bytes(msg_size)
        key = random_bytes(key_size)
        iv = random_bytes(AES.block_size)
        enc = encrypt_cbc(pkcs7pad(msg, AES.block_size), key, iv)
        dec = pkcs7unpad(decrypt_cbc(enc, key))

        self.assertTrue(dec == msg)
  # }}}

  # CTR {{{
  def test_encrypt_decrypt_ctr(self):

    for key_size in AES.key_size:
      for msg_size in xrange(1, 1000):
        key = random_bytes(key_size)
        msg = random_bytes(msg_size)

      self.assertTrue(CTRCipher(key, 0).decrypt(CTRCipher(key, 0).encrypt(msg)) == msg)
  # }}}

  # MT19937 {{{
  def test_mt19937(self):
    '''https://cryptopals.com/sets/3/challenges/21'''
    mt1, mt2 = MT19937(), MT19937()

    seed = randint(0, 100)

    mt1.seed_mt(seed)
    mt2.seed_mt(seed)

    for _ in xrange(10**6):
      self.assertTrue(mt1.extract_number() == mt2.extract_number())

  def test_mt19937_crack(self):
    '''https://cryptopals.com/sets/3/challenges/22'''
    seed1 = randint(40, 1000)
    first = MT19937(seed1).extract_number()

    for seed2 in xrange(1000, 0, -1):
      if MT19937(seed2).extract_number() == first:
        break

    self.assertTrue(seed2 == seed1)

  def test_mt19937_clone(self):
    '''https://cryptopals.com/sets/3/challenges/23'''

    for _ in xrange(100):
      mt = MT19937(randint(0, 10**9))

      MT = [0] * 624
      for i in range(624):
        MT[i] = MT19937.untemper(mt.extract_number())

      mt2 = MT19937(0)
      mt2.MT = MT

      for i in range(1000):
        a = mt.extract_number()
        b = mt2.extract_number()

        self.assertTrue(a == b)

  def test_mt19937_encryptdecrypt(self):
    for msg_size in range(1000):
      msg = random_bytes(msg_size)
      key = randint(0, 0xffff)

      ct = mt_encryptdecrypt(msg, key)
      pt = mt_encryptdecrypt(ct, key)

      self.assertTrue(pt == msg)

  def test_mt19937_break(self):
    '''https://cryptopals.com/sets/3/challenges/24'''

    # break PRNG stream cipher (recover key (16-bit seed)
    key = randint(0, 0xffff)
    prefix = random_bytes(randint(0, 20))

    def encryption_oracle(s):
      return mt_encryptdecrypt(prefix + s, key)

    pt = 'A' * 14
    ct = encryption_oracle(pt)

    pfx_size = len(ct) - len(pt)

    for k in range(0x10000):
      s = mt_encryptdecrypt('A' * len(ct), k)

      if s[pfx_size:] == ct[pfx_size:]:
        break

    self.assertTrue(k == key)

    # password reset token
    secret_seed = randint(40, 1000)
    token = mt_encryptdecrypt('A' * 14, secret_seed)

    best_score = 0
    best_seed = 0

    for seed in xrange(1000, 0, -1):
      score = count_printable(mt_encryptdecrypt(token, seed))

      if score > best_score:
        best_score = score
        best_seed = seed

    self.assertTrue(best_seed == secret_seed)
  # }}}

  # Hash Length Extension {{{
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
  # }}}

# }}}

if __name__ == '__main__':
  plaintext = '''In 2071, roughly sixty years after an accident with a hyperspace gateway made the Earth uninhabitable, humanity has colonized most of the rocky planets and moons of the Solar System.\n Amid a rising crime rate, the Inter Solar System Police (ISSP) set up a legalized contract system, in which registered bounty hunters (also referred to as "Cowboys") chase criminals and bring them in alive in return for a reward.\n The series protagonists are bounty hunters working from the spaceship Bebop.\n The original crew are Spike Spiegel, an exiled former hitman of the criminal Red Dragon Syndicate, and his partner Jet Black, a former ISSP officer.\n They are later joined by Faye Valentine, an amnesiac con artist; Edward Wong, an eccentric girl skilled in hacking; and Ein, a genetically-engineered Pembroke Welsh Corgi with human-like intelligence.\n Over the course of the series, the team get involved in disastrous mishaps leaving them out of pocket, while often confronting faces and events from their past: these include Jet's reasons for leaving the ISSP, and Faye's past as a young woman from Earth injured in an accident and cryogenically frozen to save her life'''
  unittest.main()

# vim: ts=2 sw=2 sts=2 et fdm=marker bg=dark
