# Copyright (C) 2016 Sebastien MACKE
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License version 2, as published by the
# Free Software Foundation
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
# details (http://www.gnu.org/licenses/gpl.txt).

__author__  = 'Sebastien Macke'
__email__   = 'lanjelot@gmail.com'
__url__     = 'https://github.com/lanjelot/cryptopal'
__twitter__ = 'https://twitter.com/lanjelot'
__version__ = '0.0'
__license__ = 'GPLv2'

from collections import Counter, defaultdict
from Crypto.Cipher import AES
from Crypto.Util.number import long_to_bytes, bytes_to_long, getPrime as get_prime
from Crypto.PublicKey.RSA import inverse
from random import randint, shuffle
import itertools
import hashlib
import hmac
from time import time, sleep
from threading import Thread
from Queue import Queue, Empty
import struct
import logging
import string
import requests
from requests.packages.urllib3.exceptions import InsecureRequestWarning
requests.packages.urllib3.disable_warnings(InsecureRequestWarning)
from operator import mul
from urllib import unquote
from gmpy2 import iroot

# Utils {{{
def b64d(s):
  '''Lenient base64 decode'''

  if '%' in s:
    s = unquote(s)

  if '_' in s or '-' in s:
    s = s.replace('_', '/')
    s = s.replace('-', '+')

  l = len(s) % 4
  if l != 0:
    s += '='* (4 - l)

  return s.decode('base64')

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

class Timing:
  def __enter__(self):
    self.t1 = time()
    return self

  def __exit__(self, exc_type, exc_value, traceback):
    self.time = time() - self.t1

def pairwise(iterable):
    "s -> (s0,s1), (s1,s2), (s2, s3), ..."
    a, b = itertools.tee(iterable)
    next(b, None)
    return zip(a, b)

def score_english(msg, english="etaonrishd .,\nlfcmugypwbvkjxqz-_!?'\"/1234567890*"):

  stats = Counter(filter(lambda c: c.lower() in english, msg))
  score = 0

  for c in msg:
    where = english.find(c)
    if where == -1:
      #continue
      score -= len(english)
    else:
      #score += (len(english) - where) * 2
      score += len(english) - where

  #return score, stats
  return score / len(msg), stats

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
  '''Test all possible values in a byte
  ctext: 01001001
  tests: 00000000
         00000001
         00000010
         11111111 (255)
  '''
  for i in range(len(ciphertext)):
    for n in range(256):
      payload = ciphertext[:i] + chr(n) + ciphertext[i + 1:]
      yield i, oracle(payload)

def sha256(s):
  return hashlib.sha256(s).digest()

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

def transpose(text, size):
  '''[[1,2,3], [1,2,3], [1,2,3]] => [[1,1,1], [2,2,2], [3,3,3]]'''
  transposed = []

  for i in range(size):
    chars = ''
    for block in chunk(text, size):
      if i >= len(block):
        break

      chars += block[i]

    transposed.append(chars)

  return transposed

def find_xor_key(ciphertext, keysize):
  transposed = transpose(ciphertext, keysize)

  key = ''
  for chars in transposed:
    key += crack_single_char_xor(chars)

  return key

def break_xor_contains_key(ciphertext, plaintext_prefix):
  '''Recover xor key when plaintext contains it.  Given ciphertext must end with the key
and plaintext_prefix must be some known text that the plaintext starts with.
Based on https://teamrocketist.github.io/2017/09/18/Crypto-CSAW-CTF-2017-Another-Xor/
  '''

  key_prefix = xor(plaintext_prefix, ciphertext)

  def guess_key_offset():
    '''find where key may start in plaintext'''
    possible = []

    for i in range(len(plaintext_prefix), len(ciphertext)):
      s = xor(ciphertext[i:i+len(plaintext_prefix)], key_prefix)

      score, _ = score_english(s, english='etaonrishd .,lfcmugypwbvkjxqz-')
      possible.append([i, score, s])

    possible = sorted(possible, key=lambda x: x[1], reverse=True)[:5]
    possible = sorted(possible, key=lambda x: x[0])

    return possible

  for key_offset, _, _ in guess_key_offset():
    key_len = len(ciphertext) - key_offset
    key = key_prefix.ljust(key_len, '\x00')

    while True:
      plaintext = ''
      for i in range(len(ciphertext)):
        if key[i % key_len] != '\x00':
          plaintext += xor(ciphertext[i], key[i % key_len])
        else:
          plaintext += '\x00'

      new_key = key_prefix + plaintext[key_offset+len(key_prefix):key_offset+key_len]
      if new_key == key:
        break

      key = new_key
      if '\x00' not in key:
        yield key

# }}}

# ECB {{{
def detect_ecb(ciphertext):
  '''counts identical blocks'''
  for bs in [32, 24, 16, 12, 8]:
    blocks = chunk(ciphertext, bs)
    stats = Counter(blocks)
    
    if stats.values() != [1]:
      break

  stats = [(b, c) for b, c in stats.iteritems() if c > 1]
  return stats

def detect_ecb2(ciphertext):
  '''using defaultdict instead of Counter'''
  for bs in [32, 24, 16, 12, 8]:
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

# Padding Oracle {{{
class PaddingOracle(object):
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

  def decrypt(self, ciphertext, block_size, multithread=True):
    '''Decrypt each block in a thread'''

    decrypted = {}
    blocks = chunk(ciphertext, block_size)
    self.resultq = Queue()

    for block in blocks[1:]:
      if multithread:
        t = Thread(target=self.bust, args=(block, block_size))
        t.daemon = True
        t.start()
      else:
        self.bust(block, block_size)

    try:
      while True:
        block, inter = self.pop_result()
        logging.debug('block: %r, inter: %r' % (block, inter))
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

  def edit(self, ciphertext, offset, newtext):
    '''seek into the ciphertext and re-encrypt with different plaintext (faster than edit2)'''
    newct = self.encrypt('A' * offset + newtext)[offset:]
    return ciphertext[:offset] + newct + ciphertext[offset + len(newtext):]

  def edit2(self, ciphertext, offset, newtext):
    '''seek into the ciphertext, decrypt and re-encrypt with different plaintext'''
    pt = self.decrypt(ciphertext[:offset])
    return self.encrypt(pt + newtext) + ciphertext[offset + len(newtext):]

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

    self.index += 1

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
  '''Get the 32 least significant bits'''
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

def get_bit(n, b):
    '''Return the b-th rightmost bit of n'''
    return ((1 << b) & n) >> b

def set_bit(n, b, x):
    '''Return n with the b-th rightmost bit set to x'''
    if x == 0:
      return ~(1 << b) & n

    if x == 1:
      return (1 << b) | n

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
  '''https://cryptopals.com/sets/4/challenges/31'''
  if len(key) > 64:
    key = hashlib.sha1(key).digest()
  if len(key) < 64:
    key += '\x00' * (64 - len(key))
  o_key_pad = xor('\x5c' * 64, key)
  i_key_pad = xor('\x36' * 64, key)
  return hashlib.sha1(o_key_pad + hashlib.sha1(i_key_pad + msg).digest()).digest()

def insecure_compare(s1, s2):
  for c1, c2 in zip(s1, s2):
    if c1 != c2:
      return False
    sleep(.005)
  return True

def hmac_oracle_mock(msg, sig):
  key = 'you will never guess my key'
  sleep(randint(0, 5) / 1000)
  return insecure_compare(hmac_sha1(key, msg), sig)

def hmac_oracle(msg, sig):
  r = requests.get('http://127.0.0.1:8181/?file=%s&signature=%s' % (msg, sig.encode('hex')))
  return r.status_code == 200

# attack takes too long to be in unit tests
def break_hmac():
  '''https://cryptopals.com/sets/4/challenges/32'''
  filename = '/etc/passwd'
  found = ''

  rounds = 10 
  while True:
    stats = Counter()
    for _ in range(rounds):
      for c in map(chr, range(256)):
        signature = found + c + '\x00' * (20 - 1 - len(found))
        with Timing() as timing:
          #if hmac_oracle(filename, signature): # needs hmac_break_server.py running
          if hmac_oracle_mock(filename, signature):
            print 'found signature for %s is %r' % (filename, found)
            return found

        stats[c] += timing.time

    top5 = stats.most_common(5)
    print 'top 5: %r' % top5

    found += top5[0][0]
    print 'found so far: %r' % found

# }}}

# Diffie-Hellman {{{
def keygen_dh(p, g):
    privkey = bytes_to_long(random_bytes(16)) % p
    pubkey = pow(g, privkey, p)

    return privkey, pubkey

def derivekey(s):
    return hashlib.sha1('%x' % s).digest()[:16]

class DH_Peer:
  def __init__(self, p, g):
    self.p, self.g = p, g
    self.privkey, self.pubkey = keygen_dh(self.p, self.g)

  def compute_sharedkey(self, peer_pubkey):
    secret = pow(peer_pubkey, self.privkey, self.p)
    self.sharedkey = derivekey(secret)

  def encrypt(self, msg):
    return encrypt_cbc(msg, self.sharedkey, random_bytes(16))

  def decrypt(self, msg):
    return decrypt_cbc(msg, self.sharedkey)

def mitm_dh_p(p, g):
  A = DH_Peer(p, g)

  # A->M sends p, g, pubkey
  M = DH_Peer(p, g)

  # M->B sends p, g, p (instead of A.pubkey)
  B = DH_Peer(p, g)
  B.compute_sharedkey(p)

  # B->M sends pubkey (but M doesnt care)
  M.compute_sharedkey(p)

  # M->A sends p (instead of B.pubkey)
  A.compute_sharedkey(p)

  return A, B, M

def mitm_dh_fakeg(p, g, fake_g):
  A = DH_Peer(p, g)

  # A->M sends p, g (but M doesnt care and sends back fake_g to A)

  # M->A sends p, fake_g
  A = DH_Peer(p, fake_g)

  # A->M sends p, fake_g, A.pubkey
  M = DH_Peer(p, fake_g)

  # M->B sends p, fake_g, A.pubkey
  B = DH_Peer(p, fake_g)
  B.compute_sharedkey(A.pubkey)

  # B->M sends B.pubkey
  M.compute_sharedkey(B.pubkey)

  # M->A sends B.pubkey
  A.compute_sharedkey(B.pubkey)

  if fake_g == p -1:
    if A.pubkey == p - 1 and B.pubkey == p - 1:
      M.sharedkey = derivekey(p - 1)
    else:
      M.sharedkey = derivekey(1)

  return A, B, M

def is_mitm(A, B, M):
  '''confirm M can encrypt and decrypt any message between A and B'''

  assert A.sharedkey == B.sharedkey
  assert M.sharedkey == B.sharedkey

  pt1 = random_bytes(AES.block_size)
  pt2 = random_bytes(AES.block_size)

  # A->M
  ct1 = A.encrypt(pt1)
  assert M.decrypt(ct1) == pt1

  # M->B
  ct1 = M.encrypt(pt1)
  assert B.decrypt(ct1) == pt1

  # B->M
  ct2 = B.encrypt(pt2)
  assert M.decrypt(ct2) == pt2

  # M->A
  ct2 = M.encrypt(pt2)
  assert A.decrypt(ct2) == pt2

  return True

# }}}

# SRP {{{
class SRP_Peer:
  def __init__(self, email, password, N=0xffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746c08ca237327ffffffffffffffff, g=2, k=3):
    self.N = N
    self.g = g
    self.k = k

    self.email = email
    self.password = password

    self.privkey, self.pubkey = keygen_dh(self.N, self.g)

  def sign_salt(self):
    return hmac.new(self.K, self.salt, hashlib.sha256).hexdigest()

def compute_u(server_pubkey, client_pubkey):
  return bytes_to_long(sha256(str(server_pubkey) + str(client_pubkey)))

class SRP_Client(SRP_Peer):
  def compute_sharedkey(self, salt, server_pubkey):
    self.salt = salt

    u = compute_u(server_pubkey, self.pubkey)
    x = bytes_to_long(sha256(self.salt + self.password))
    gx = pow(self.g, x, self.N)
    S = pow(server_pubkey - self.k * gx, self.privkey + u * x, self.N)

    self.K = sha256(str(S))

  def compute_sharedkey_bypass(self, salt, server_pubkey):
    self.salt = salt
    self.K = sha256('0')

  def compute_sharedkey_simplified(self, salt, server_pubkey, u):
    self.salt = salt

    # this time u is provided by the server
    x = bytes_to_long(sha256(self.salt + self.password))
    S = pow(server_pubkey, self.privkey + u * x, self.N)

    self.K = sha256(str(S))

class SRP_Server(SRP_Peer):
  def compute_sharedkey(self, email, client_pubkey): # aka. recv_login()
    assert self.email == email

    self.salt = random_bytes(4)

    x = bytes_to_long(sha256(self.salt + self.password))
    v = pow(self.g, x, self.N)

    self.pubkey = (self.k * v + self.pubkey) % self.N
    u = compute_u(self.pubkey, client_pubkey)

    vu = pow(v, u, self.N)
    S = pow(client_pubkey * vu, self.privkey, self.N)

    self.K = sha256(str(S))

  def compute_sharedkey_simplified(self, email, client_pubkey):
    assert self.email == email

    self.salt = random_bytes(4)

    x = bytes_to_long(sha256(self.salt + self.password))
    v = pow(self.g, x, self.N)

    self.pubkey = pow(self.g, self.privkey, self.N) # this time the server pubkey doesn't depend on the password
    self.u = bytes_to_long(random_bytes(16)) # this time u is a 128 bit random number

    vu = pow(v, self.u, self.N)
    S = pow(client_pubkey * vu, self.privkey, self.N)

    self.K = sha256(str(S))

  def check_mac(self, mac):
    return self.sign_salt() == mac

def srp_normal():
  email = 'client@example.com'
  password = 'Welcome123'

  server = SRP_Server(email, password)
  client = SRP_Client(email, password)

  server.compute_sharedkey(client.email, client.pubkey) # (C.login, C.pubkey) -> S
  client.compute_sharedkey(server.salt, server.pubkey) # (S.salt, S.pubkey) -> C

  return server, client

def srp_bypass(fake_pubkey):
  email = 'client@example.com'
  password = 'St0ngP@ssw0rd'

  server = SRP_Server(email, password)
  client = SRP_Client(email, 'idontneedapassword')

  server.compute_sharedkey(client.email, fake_pubkey) # (C.login, 0) -> S (or N, N*2 ...)
  client.compute_sharedkey_bypass(server.salt, server.pubkey) # (S.salt, S.pubkey) -> C

  return server, client

def srp_mitm():
  email = 'client@example.com'
  password = random_chars(4, charset='0123456789')

  server = SRP_Server(email, 'iwilljustcrackit')
  client = SRP_Client(email, password)

  server.compute_sharedkey_simplified(client.email, client.pubkey) # (C.login, C.pubkey) -> S
  client.compute_sharedkey_simplified(server.salt, server.pubkey, server.u) # (S.salt, S.pubkey, S.u) -> C

  return server, client

def srp_crack_password(server, client_g, client_N, client_pubkey, mac):
  for pw in itertools.imap(lambda p: ''.join(p), itertools.product('0123456789', repeat=4)):
    x = bytes_to_long(sha256(server.salt + pw))
    v = pow(client_g, x, client_N)
    vu = pow(v, server.u, client_N)

    S = pow(client_pubkey * vu, server.privkey, client_N)
    K = sha256(str(S))

    if hmac.new(K, server.salt, hashlib.sha256).hexdigest() == mac:
      return pw

# }}}

# RSA {{{
def bit_length(x):
  return x.bit_length()
  #return len(bin(x)[2:])

def byte_length(x):
  return bit_length(x) // 8

def egcd(a, b):
  if b == 0:
    return (1, 0)

  assert a > 0 and b > 0

  q, r = divmod(a, b)
  s, t = egcd(b, r)

  return t, s - q * t

def invmod(x, y):
  return inverse(x, y)

def _invmod(x, y):
  ax, by = egcd(x, y)
  while ax < 0:
    ax += y
  return ax

def gen_prime_given_e(bitlen, e):
  while True:
    p = get_prime(bitlen)
    if p % e != 1:
      return p

def keygen_rsa(bitlen, e):
  assert bitlen % 2 == 0
  pqlen = bitlen // 2

  while True:
    p = gen_prime_given_e(pqlen, e)
    q = gen_prime_given_e(pqlen, e)
    n = p * q

    phi = (p - 1) * (q - 1)

    d = invmod(e, phi)
    if bit_length(n) == bitlen and (d * e) % phi == 1:
      return (n, e), (n, d)

def encrypt_rsa(pubkey, msg):
    n, e = pubkey
    return pow(msg, e, n)

def decrypt_rsa(privkey, msg):
    n, d = privkey
    return pow(msg, d, n)

def rsa_broadcast_attack(pairs, exponent=3):
  ns = [n for n, c in pairs]
  cs = [c for n, c in pairs]

  N = reduce(mul, ns)

  ms = []
  for n in ns:
    ms.append(N // n)

  res = 0
  for c, m, n in zip(cs, ms, ns):
    res += c * m * inverse(m, n)

  res %= N
  rec, _ = iroot(res, exponent)

  return long_to_bytes(rec)

def rsa_unpadded_message_attack(ct, modulus, exponent=3):
  while True:
    rec, e = iroot(ct, exponent)
    if e:
      break

    ct += modulus

  return long_to_bytes(rec)

def rsa_unpadded_decryption_oracle(decryption_oracle, pubkey, ct):
  N, e = pubkey

  pt2 = 42 # random.randrange(1, N)
  ct2 = encrypt_rsa(pubkey, pt2)
  pt3 = decryption_oracle((ct2 * ct) % N)

  pt = (pt3 * invmod(pt2, N)) % N
  return long_to_bytes(pt)

ASN1_SHA1 = '\x30\x21\x30\x09\x06\x05\x2b\x0e\x03\x02\x1a\x05\x00\x04\x14'

def rsa_bleichenbacher_e3_signature_forgery(msg):
  modlen = 1024 / 8 # attack for a 1024-bit modulus

  block = '\x00\x01\xff\x00' + ASN1_SHA1 + hashlib.sha1(msg).digest()
  block += '\x7f' * (modlen - 4 - len(ASN1_SHA1) - 20) # right-pad to approx half the interval

  sig, _ = iroot(bytes_to_long(block), 3)
  return long_to_bytes(sig)

def rsa_bleichenbacher_e3_signature_forgery_easy(msg, modulus_size=1024):
  '''using easy suffix computation '''
  '''https://blog.filippo.io/bleichenbacher-06-signature-forgery-in-python-rsa/ '''
  '''https://grocid.net/2016/06/05/backdoorctf16-baby/'''

  suffix = '\x00' + ASN1_SHA1 + hashlib.sha1(msg).digest()

  assert bytes_to_long(suffix) % 2 == 1 # easy suffix computation only works with odd target
  sig_suffix = 1

  for b in range(len(suffix) * 8):
    if get_bit(sig_suffix ** 3, b) != get_bit(bytes_to_long(suffix), b):
      sig_suffix = set_bit(sig_suffix, b, 1)

  assert long_to_bytes(sig_suffix ** 3).endswith(suffix)

  while True:
    prefix = '\x00\x01' + random_bytes(modulus_size / 8 - 2)
    sig_prefix, _ = iroot(bytes_to_long(prefix), 3)
    sig = long_to_bytes(sig_prefix)[:-len(suffix)] + long_to_bytes(sig_suffix)

    if '\x00' not in long_to_bytes(bytes_to_long(sig) ** 3)[:-len(suffix)]:
      return sig

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

  def test_break_xor_contains_key(self):
    key = 'A quart jar of oil mixed with zinc oxide makes a very bright paint|'

    for size in range(5, len(key) - 5):
      plaintext = random_chars(size, '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~ ') + key
      ciphertext = xor(plaintext, key)

      for k in break_xor_contains_key(ciphertext, plaintext[:5]):
        if xor(ciphertext, k) == plaintext:
          break
      else:
        self.fail()

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

  # CBC {{{
  # TODO add tests with other algorithms (e.g. DES)
  def test_cbc_encrypt_decrypt(self):
    for key_size in AES.key_size:
      for msg_size in xrange(AES.block_size * 3):
        msg = random_bytes(msg_size)
        key = random_bytes(key_size)
        iv = random_bytes(AES.block_size)

        enc = encrypt_cbc(pkcs7pad(msg, AES.block_size), key, iv)
        dec = pkcs7unpad(decrypt_cbc(enc, key))

        self.assertTrue(dec == msg)

  def test_cbc_ivkey_recover(self):
    '''Recover the key from CBC with IV=Key '''
    '''https://cryptopals.com/sets/4/challenges/27'''

    for msg_size in xrange(100):

      key = random_bytes(AES.block_size) # key must be same length as iv

      def leak(s):
        dec = decrypt_cbc(s, key, iv=key)

        if any(x for x in dec if x not in string.printable):
          raise ValueError('non compliant message: %s' % dec)

      pt = random_printables(msg_size)
      ct = encrypt_cbc(pt, key, iv=key)

      c0 = chunk(ct, AES.block_size)[0]
      payload = c0 + '\x00' * AES.block_size + c0

      try:
        leak(payload)
      except ValueError as e:
        decrypted = chunk(e.message[23:], AES.block_size)
        recovered = xor(decrypted[0], decrypted[2])

      self.assertTrue(key == recovered)

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

  # CTR {{{
  def test_ctr_encrypt_decrypt(self):
    '''https://cryptopals.com/sets/3/challenges/18'''

    for key_size in AES.key_size:
      for msg_size in xrange(1, 100):
        key = random_bytes(key_size)
        msg = random_bytes(msg_size)

      self.assertTrue(CTRCipher(key, 0).decrypt(CTRCipher(key, 0).encrypt(msg)) == msg)

  def test_ctr_edit(self):
    key = random_bytes(16)
    nonce = int(random_bytes(8).encode('hex'), 16)

    msg_size = 100
    msg = random_bytes(msg_size)

    for offset in xrange(msg_size):
      newtext_size = randint(1, msg_size - offset)
      newtext = random_bytes(newtext_size)

      ctr = CTRCipher(key, nonce)
      ct = ctr.encrypt(msg)

      newct = ctr.edit(ct, offset, newtext)
      pt = ctr.decrypt(newct)

      new_msg = msg[:offset] + newtext + msg[offset + newtext_size:]

      self.assertTrue(pt == new_msg)

  def test_ctr_break_edit(self):
    '''Break "random access read/write" AES CTR '''
    '''https://cryptopals.com/sets/4/challenges/25'''

    key = random_bytes(16)
    nonce = int(random_bytes(8).encode('hex'), 16)

    ctr = CTRCipher(key, nonce)
    ciphertext = ctr.encrypt(plaintext)

    recovered = ctr.edit(ciphertext, 0, ciphertext)
    self.assertTrue(plaintext == recovered)

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
    '''Crack an MT19937 seed '''
    '''https://cryptopals.com/sets/3/challenges/22'''

    seed1 = randint(40, 1000)
    first = MT19937(seed1).extract_number()

    for seed2 in xrange(1000, 0, -1):
      if MT19937(seed2).extract_number() == first:
        break

    self.assertTrue(seed2 == seed1)

  def test_mt19937_clone(self):
    '''Clone an MT19937 RNG from its output '''
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
    '''Break an MT19937 stream cipher '''
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
    '''https://cryptopals.com/sets/4/challenges/28'''

    for size in range(1000):
      data = random_bytes(size)

      sha = SHA1()
      sha.update(data)

      self.assertTrue(sha.hexdigest() == hashlib.sha1(data).hexdigest())

  def test_sha1_extend(self):
    '''https://cryptopals.com/sets/4/challenges/29'''

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

  # Diffie-Hellman {{{
  def test_dh(self):
    '''https://cryptopals.com/sets/5/challenges/33'''

    A = DH_Peer(p, g)
    B = DH_Peer(p, g)

    B.compute_sharedkey(A.pubkey) # A sends pubkey to B
    A.compute_sharedkey(B.pubkey) # B sends pubkey to A

    self.assertTrue(B.sharedkey == A.sharedkey)

    pt1 = random_bytes(AES.block_size)
    pt2 = random_bytes(AES.block_size)

    ct1 = A.encrypt(pt1)
    ct2 = B.encrypt(pt2)

    self.assertTrue(A.decrypt(ct2) == pt2)
    self.assertTrue(B.decrypt(ct1) == pt1)

  def test_dh_mitm_p(self):
    '''mitm via sending p as A.pubkey and B.pubkey '''
    '''https://cryptopals.com/sets/5/challenges/34'''

    A, B, M = mitm_dh_p(p, g)

    self.assertTrue(M.sharedkey == A.sharedkey)
    self.assertTrue(M.sharedkey == B.sharedkey)
    self.assertTrue(is_mitm(A, B, M))

  def test_dh_mitm_fakeg(self):
    '''mitm via malicious g '''
    '''https://cryptopals.com/sets/5/challenges/35'''

    # g = p
    # pubkey will always be 0 whatever privkey is
    # because pubkey = pow(p, privkey, p) => 0
    # and so sharedkey will always be 0
    # because sharedkey = pow(pubkey, privkey, p) => 0
    A, B, M = mitm_dh_fakeg(p, g, p)

    self.assertTrue(A.sharedkey == derivekey(0))
    self.assertTrue(B.sharedkey == derivekey(0))
    self.assertTrue(is_mitm(A, B, M))

    # g = 1
    # pubkey will always be 1 whatever privkey is
    # because pubkey = pow(1, privkey, p) => 1
    # and so sharedkey will always be 1
    # because sharedkey = pow(1, privkey, p) => 1
    A, B, M = mitm_dh_fakeg(p, g, 1)

    self.assertTrue(A.sharedkey == derivekey(1))
    self.assertTrue(B.sharedkey == derivekey(1))
    self.assertTrue(is_mitm(A, B, M))

    # g = p - 1
    # pubkey will always be p - 1 or 1
    # because pubkey = pow(p - 1, privkey, p) => p - 1 or 1
    # and so sharedkey will always be p - 1 or 1
    # because sharedkey = pow(p - 1, privkey, p) => p - 1 or 1
    A, B, M = mitm_dh_fakeg(p, g, p - 1)

    self.assertTrue((A.sharedkey == derivekey(p - 1) and B.sharedkey == derivekey(p - 1)) or (A.sharedkey == derivekey(1) and B.sharedkey == derivekey(1)))
    self.assertTrue(is_mitm(A, B, M))

  # }}}

  # SRP {{{
  def test_srp_normal(self):
    '''https://cryptopals.com/sets/5/challenges/36'''

    server, client = srp_normal()
    self.assertTrue(server.check_mac(client.sign_salt()) == True)

  def test_srp_bypass(self):
    '''client sends 0 as its pubkey (or N, N*2, etc.) '''
    '''https://cryptopals.com/sets/5/challenges/37'''

    for fake_pubkey in [0, p, p*2]:
      server, client = srp_bypass(fake_pubkey)
      self.assertTrue(server.check_mac(client.sign_salt()) == True)

      # both sides now have
      self.assertTrue(server.K == sha256('0'))
      self.assertTrue(client.K == sha256('0'))

  def test_srp_mitm(self):
    '''mitm can crack client's password offline '''
    '''https://cryptopals.com/sets/5/challenges/38'''

    server, client = srp_mitm()
    mac = client.sign_salt()
    found = srp_crack_password(server, client.g, client.N, client.pubkey, mac)

    self.assertTrue(found == client.password)

  # }}}

  # RSA {{{
  def test_rsa_encryptdecrypt(self):
    for key_size in [1024, 2048]: # bigger key sizes take forever
      for msg_size in range(1, 50):
        pubkey, privkey = keygen_rsa(key_size, 0x10001)

        pt = bytes_to_long(random_bytes(msg_size))
        ct = encrypt_rsa(pubkey, pt)

        self.assertTrue(decrypt_rsa(privkey, ct) == pt)

  def test_rsa_broadcast(self):
    '''standard E=3 RSA broadcast attack with plaintext smaller than any modulus '''
    '''https://cryptopals.com/sets/5/challenges/40'''

    exponent = 3
    msg = 'this is a secret message'

    pairs = []
    for _ in range(3):
      (n, e), _ = keygen_rsa(1024, exponent)
      ct = encrypt_rsa((n, e), bytes_to_long(msg))

      pairs.append((n, ct))

    rec = rsa_broadcast_attack(pairs)
    self.assertTrue(rec == msg)

  def test_rsa_broadcast_icectf(self):
    '''Special case where a standard broadcast attack will not work because plaintext is bigger than any of the provided modulus. '''
    '''Every individual RSA encryption loses some information, but when enough pubkeys and ciphertexts are gathered, the plaintext can be "magically" recovered. '''
    '''http://blog.atx.name/icectf/#Agents'''

    exponent = 3
    ns = []

    for _ in range(200):
      (n, e), _ = keygen_rsa(1024, exponent)
      ns.append(n)

    # making sure msg is bigger than the biggest modulus
    msg = 'the secret msg is '
    while not bytes_to_long(msg) > max(ns):
      msg += random_chars(1)
    msg += random_chars(1000)

    pairs = []
    for n in ns:
      ct = encrypt_rsa((n, exponent), bytes_to_long(msg))
      pairs.append((n, ct))

    rec = rsa_broadcast_attack(pairs)
    self.assertTrue(rec == msg)

  def test_rsa_unpadded_message_attack(self):
    '''small message and small exponent '''
    '''http://blog.atx.name/icectf/#RSA3'''
    exponent = 3
    msg = 'this is the secret message'

    pt = bytes_to_long(msg)

    (n, e), _ = keygen_rsa(1024, exponent)
    ct = encrypt_rsa((n, e), pt)

    self.assertTrue(pt < n) # msg must be smaller than modulus

    rec = rsa_unpadded_message_attack(ct, n, exponent)
    self.assertTrue(rec == msg)

  def test_rsa_unpadded_decryption_oracle(self):
    '''https://cryptopals.com/sets/6/challenges/41'''

    ciphers = []
    def decrypt_once(ct):
      '''the decryption oracle'''
      if ct in ciphers:
        return None

      ciphers.append(ct)
      return decrypt_rsa(privkey, ct)

    pubkey, privkey = keygen_rsa(1024, 3)

    msg = 'this is a secret message'
    pt = bytes_to_long(msg)

    assert pt < pubkey[0] # msg must be smaller than modulus

    ct = encrypt_rsa(pubkey, pt)

    assert decrypt_once(ct) == pt
    assert decrypt_once(ct) is None

    rec = rsa_unpadded_decryption_oracle(decrypt_once, pubkey, ct)
    self.assertTrue(rec == msg)

  def test_rsa_bleichenbacher_e3_signature_forgery(self):
    '''https://cryptopals.com/sets/6/challenges/42 '''
    '''OpenSSL and NSS used to be vulnerable, this attack broke Firefox's TLS certificate validation several years ago'''

    def pkcs1_sign(msg):
      h = hashlib.sha1(msg).digest()
      npad = modlen - 2 - 1 - len(ASN1_SHA1 + h)
      block = '\x00\x01' + ('\xff' * npad) + '\x00' + ASN1_SHA1 + h

      return long_to_bytes(decrypt_rsa((n, d), bytes_to_long(block)))

    def pkcs1_verify_bad(msg, sig):
      cube = long_to_bytes(encrypt_rsa((n, 3), bytes_to_long(sig)))

      if cube[:2] != '\x01\xff':
        return False

      return '\x00' + ASN1_SHA1 + hashlib.sha1(msg).digest() in cube

    modlen = 1024 / 8

    for msg_size in range(50):
      _, (n, d) = keygen_rsa(1024, 3)
      msg = random_chars(msg_size)

      sig_legit = pkcs1_sign(msg)
      sig_forged = rsa_bleichenbacher_e3_signature_forgery(msg)

      self.assertTrue(pkcs1_verify_bad(msg, sig_legit))
      self.assertTrue(pkcs1_verify_bad(msg, sig_forged))

  def test_rsa_bleichenbacher_e3_signature_forgery_easy(self):
    '''python-rsa CVE-2016-1494'''

    def pkcs1_verify_bad(msg, sig):
      cube = long_to_bytes(bytes_to_long(sig) ** 3)

      if cube[0] != '\x01':
        return False

      if cube[-36:] != '\x00' + ASN1_SHA1 + hashlib.sha1(msg).digest():
        return False

      return True

    def random_msg():
      while True:
        msg = random_chars(10)
        if bytes_to_long(hashlib.sha1(msg).digest()) % 2 == 0:
          continue
        return msg

    msg = random_msg()
    sig = rsa_bleichenbacher_e3_signature_forgery_easy(msg)

    self.assertTrue(pkcs1_verify_bad(msg, sig))

  # }}}

# }}}

if __name__ == '__main__':
  plaintext = '''In 2071, roughly sixty years after an accident with a hyperspace gateway made the Earth uninhabitable, humanity has colonized most of the rocky planets and moons of the Solar System.\n Amid a rising crime rate, the Inter Solar System Police (ISSP) set up a legalized contract system, in which registered bounty hunters (also referred to as "Cowboys") chase criminals and bring them in alive in return for a reward.\n The series protagonists are bounty hunters working from the spaceship Bebop.\n The original crew are Spike Spiegel, an exiled former hitman of the criminal Red Dragon Syndicate, and his partner Jet Black, a former ISSP officer.\n They are later joined by Faye Valentine, an amnesiac con artist; Edward Wong, an eccentric girl skilled in hacking; and Ein, a genetically-engineered Pembroke Welsh Corgi with human-like intelligence.\n Over the course of the series, the team get involved in disastrous mishaps leaving them out of pocket, while often confronting faces and events from their past: these include Jet's reasons for leaving the ISSP, and Faye's past as a young woman from Earth injured in an accident and cryogenically frozen to save her life'''

  p = 0xffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746c08ca237327ffffffffffffffff
  g = 2

  unittest.main()

# vim: ts=2 sw=2 sts=2 et fdm=marker bg=dark
