
from pure25519.basic import (bytes_to_clamped_scalar,
                             bytes_to_scalar, scalar_to_bytes,
                             bytes_to_element, Base, L)
import pure25519.config

import hashlib, binascii

def H(m):
    return hashlib.sha512(m).digest()

def publickey(seed):
    # turn first half of SHA512(seed) into scalar, then into point
    assert len(seed) == 32
    a = bytes_to_clamped_scalar(H(seed)[:32])
    A = Base.scalarmult(a)
    
    if 'pk' in pure25519.config.verbose:
        print(f'H(seed):    {H(seed)[:32].hex()}')
        print(f"a:          {hex(a)[2:]}")

    return A.to_bytes()

def Hint(m):
    h = H(m)
    return int(binascii.hexlify(h[::-1]), 16)

def signature(m,sk,pk):
    assert len(sk) == 32 # seed
    assert len(pk) == 32
    h = H(sk[:32])
    a_bytes, inter = h[:32], h[32:]
    a = bytes_to_clamped_scalar(a_bytes)
    r = Hint(inter + m)
    R = Base.scalarmult(r)
    R_bytes = R.to_bytes()
    x = Hint(R_bytes + pk + m)
    S = (r + x * a)

    if 'sign' in pure25519.config.verbose:
        print('h      :', h.hex())
        print('a_bytes:', a_bytes.hex())
        print('inter:  ', inter.hex())
        print('a:      ', hex(a)[2:])
        print('r:      ', hex(r)[2:])
        print('R_bytes:', R_bytes.hex())
        print('x:      ', hex(x)[2:])
        print('a:      ', hex(a)[2:])
        print('S:      ', hex(S)[2:])
        print('S%L:    ', (S%L).to_bytes(32, 'little').hex())
        print('S%L:    ', scalar_to_bytes(S).hex())

    return R_bytes + scalar_to_bytes(S)

def checkvalid(s, m, pk):
    if len(s) != 64: raise Exception("signature length is wrong")
    if len(pk) != 32: raise Exception("public-key length is wrong")
    R = bytes_to_element(s[:32])
    A = bytes_to_element(pk)
    S = bytes_to_scalar(s[32:])
    h = Hint(s[:32] + pk + m)
    v1 = Base.scalarmult(S)
    v2 = R.add(A.scalarmult(h))
    
    if 'open' in pure25519.config.verbose:
        print('R:      ', R.to_bytes().hex())
        print('A:      ', A.to_bytes().hex())
        print('S:      ', S.to_bytes(32, 'little').hex())
        print('m:      ', m.hex())
        print('h:      ', h.to_bytes(64, 'little').hex())
        print('v1:     ', v1.to_bytes().hex())
        print('v1:     ', v1.to_bytes().hex())
        print('v2:     ', v2.to_bytes().hex())

    return v1==v2

# wrappers

import os

def create_signing_key():
    seed = os.urandom(32)
    return seed
def create_verifying_key(signing_key):
    return publickey(signing_key)

def sign(skbytes, msg):
    """Return just the signature, given the message and just the secret
    key."""
    if len(skbytes) != 32:
        raise ValueError("Bad signing key length %d" % len(skbytes))
    vkbytes = create_verifying_key(skbytes)
    sig = signature(msg, skbytes, vkbytes)
    return sig

def verify(vkbytes, sig, msg):
    if len(vkbytes) != 32:
        raise ValueError("Bad verifying key length %d" % len(vkbytes))
    if len(sig) != 64:
        raise ValueError("Bad signature length %d" % len(sig))
    rc = checkvalid(sig, msg, vkbytes)
    if not rc:
        raise ValueError("rc != 0", rc)
    return True
