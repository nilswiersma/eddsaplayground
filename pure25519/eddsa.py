import pure25519.config

import binascii, hashlib, itertools

import sys

Q = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493

def inv(x):
    return pow(x, Q-2, Q)

d = -121665 * inv(121666)
I = pow(2,(Q-1)//4,Q)

def xrecover(y):
    xx = (y*y-1) * inv(d*y*y+1)
    x = pow(xx,(Q+3)//8,Q)
    if (x*x - xx) % Q != 0: x = (x*I) % Q
    if x % 2 != 0: x = Q-x
    return x

By = 4 * inv(5)
Bx = xrecover(By)
B = [Bx % Q,By % Q]

# Extended Coordinates: x=X/Z, y=Y/Z, x*y=T/Z
# http://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html

def xform_affine_to_extended(pt):
    (x, y) = pt
    return (x%Q, y%Q, 1, (x*y)%Q) # (X,Y,Z,T)

def xform_extended_to_affine(pt):
    (x, y, z, _) = pt
    return ((x*inv(z))%Q, (y*inv(z))%Q)

def double_element(pt): # extended->extended
    # dbl-2008-hwcd
    if pure25519.config.spa:
        print('D', end='', file=pure25519.config.spa_file)

    (X1, Y1, Z1, _) = pt
    A = (X1*X1)
    B = (Y1*Y1)
    C = (2*Z1*Z1)
    D = (-A) % Q
    J = (X1+Y1) % Q
    E = (J*J-A-B) % Q
    G = (D+B) % Q
    F = (G-C) % Q
    H = (D-B) % Q
    X3 = (E*F) % Q
    Y3 = (G*H) % Q
    Z3 = (F*G) % Q
    T3 = (E*H) % Q

    if 'double' in pure25519.config.verbose:
        print('double')
        print('X3:        ', X3.to_bytes(32, 'little').hex())
        print('Y3:        ', Y3.to_bytes(32, 'little').hex())
        print('Z3:        ', Z3.to_bytes(32, 'little').hex())
        print('T3:        ', T3.to_bytes(32, 'little').hex())
    return (X3, Y3, Z3, T3)

def add_elements(pt1, pt2): # extended->extended
    # add-2008-hwcd-3 . Slightly slower than add-2008-hwcd-4, but -3 is
    # unified, so it's safe for general-purpose addition
    if pure25519.config.spa:
        print('A', end='', file=pure25519.config.spa_file)

    (X1, Y1, Z1, T1) = pt1
    (X2, Y2, Z2, T2) = pt2
    A = ((Y1-X1)*(Y2-X2)) % Q
    B = ((Y1+X1)*(Y2+X2)) % Q
    C = T1*(2*d)*T2 % Q
    D = Z1*2*Z2 % Q
    E = (B-A) % Q
    F = (D-C) % Q
    G = (D+C) % Q
    H = (B+A) % Q
    X3 = (E*F) % Q
    Y3 = (G*H) % Q
    T3 = (E*H) % Q
    Z3 = (F*G) % Q
    return (X3, Y3, Z3, T3)

def scalarmult_element_safe_slow(pt, n):
    # this form is slightly slower, but tolerates arbitrary points, including
    # those which are not in the main 1*L subgroup. This includes points of
    # order 1 (the neutral element Zero), 2, 4, and 8.
    assert n >= 0
    if n==0:
        return xform_affine_to_extended((0,1))
    _ = double_element(scalarmult_element_safe_slow(pt, n>>1))
    return add_elements(_, pt) if n&1 else _

def _add_elements_nonunfied(pt1, pt2): # extended->extended
    # add-2008-hwcd-4 : NOT unified, only for pt1!=pt2. About 10% faster than
    # the (unified) add-2008-hwcd-3, and safe to use inside scalarmult if you
    # aren't using points of order 1/2/4/8
    if pure25519.config.spa:
        print('A', end='', file=pure25519.config.spa_file)

    (X1, Y1, Z1, T1) = pt1
    (X2, Y2, Z2, T2) = pt2
    A = ((Y1-X1)*(Y2+X2)) % Q
    B = ((Y1+X1)*(Y2-X2)) % Q
    C = (Z1*2*T2) % Q
    D = (T1*2*Z2) % Q
    E = (D+C) % Q
    F = (B-A) % Q
    G = (B+A) % Q
    H = (D-C) % Q
    X3 = (E*F) % Q
    Y3 = (G*H) % Q
    Z3 = (F*G) % Q
    T3 = (E*H) % Q

    if 'add' in pure25519.config.verbose:
        print('add')
        print('X3:        ', X3.to_bytes(32, 'little').hex())
        print('Y3:        ', Y3.to_bytes(32, 'little').hex())
        print('Z3:        ', Z3.to_bytes(32, 'little').hex())
        print('T3:        ', T3.to_bytes(32, 'little').hex())

    return (X3, Y3, Z3, T3)

def scalarmult_element(pt, n): # extended->extended
    # This form only works properly when given points that are a member of
    # the main 1*L subgroup. It will give incorrect answers when called with
    # the points of order 1/2/4/8, including point Zero. (it will also work
    # properly when given points of order 2*L/4*L/8*L)
    assert n >= 0
    if n==0:
        return xform_affine_to_extended((0,1))
    _ = double_element(scalarmult_element(pt, n>>1))
    return _add_elements_nonunfied(_, pt) if n&1 else _

# points are encoded as 32-bytes little-endian, b255 is sign, b2b1b0 are 0

def encodepoint(P):
    x = P[0]
    y = P[1]
    # MSB of output equals x.b0 (=x&1)
    # rest of output is little-endian y
    assert 0 <= y < (1<<255) # always < 0x7fff..ff
    if x & 1:
        y += 1<<255
    return binascii.unhexlify("%064x" % y)[::-1]

def isoncurve(P):
    x = P[0]
    y = P[1]
    return (-x*x + y*y - 1 - d*x*x*y*y) % Q == 0

class NotOnCurve(Exception):
    pass

def decodepoint(s):
    unclamped = int(binascii.hexlify(s[:32][::-1]), 16)
    clamp = (1 << 255) - 1
    y = unclamped & clamp # clear MSB
    x = xrecover(y)
    if bool(x & 1) != bool(unclamped & (1<<255)): x = Q-x
    P = [x,y]
    if not isoncurve(P): raise NotOnCurve("decoding point that is not on curve")
    return P

# scalars are encoded as 32-bytes little-endian

def bytes_to_scalar(s):
    assert len(s) == 32, len(s)
    return int(binascii.hexlify(s[::-1]), 16)

def bytes_to_clamped_scalar(s):
    # Ed25519 private keys clamp the scalar to ensure two things:
    #   1: integer value is in L/2 .. L, to avoid small-logarithm
    #      non-wraparaound
    #   2: low-order 3 bits are zero, so a small-subgroup attack won't learn
    #      any information
    # set the top two bits to 01, and the bottom three to 000
    a_unclamped = bytes_to_scalar(s)
    AND_CLAMP = (1<<254) - 1 - 7
    OR_CLAMP = (1<<254)
    a_clamped = (a_unclamped & AND_CLAMP) | OR_CLAMP
    return a_clamped

def random_scalar(entropy_f): # 0..L-1 inclusive
    # reduce the bias to a safe level by generating 256 extra bits
    oversized = int(binascii.hexlify(entropy_f(32+32)), 16)
    return oversized % L

def password_to_scalar(pw):
    oversized = hashlib.sha512(pw).digest()
    return int(binascii.hexlify(oversized), 16) % L

def scalar_to_bytes(y):
    y = y % L
    assert 0 <= y < 2**256
    return binascii.unhexlify("%064x" % y)[::-1]

# Elements, of various orders

def is_extended_zero(XYTZ):
    # catch Zero
    (X, Y, Z, T) = XYTZ
    Y = Y % Q
    Z = Z % Q
    if X==0 and Y==Z and Y!=0:
        return True
    return False

class ElementOfUnknownGroup:
    # This is used for points of order 2,4,8,2*L,4*L,8*L
    def __init__(self, XYTZ):
        assert isinstance(XYTZ, tuple)
        assert len(XYTZ) == 4
        self.XYTZ = XYTZ

    def add(self, other):
        if not isinstance(other, ElementOfUnknownGroup):
            raise TypeError("elements can only be added to other elements")
        sum_XYTZ = add_elements(self.XYTZ, other.XYTZ)
        if is_extended_zero(sum_XYTZ):
            return Zero
        return ElementOfUnknownGroup(sum_XYTZ)

    def scalarmult(self, s):
        if pure25519.config.spa:
            print('ElementOfUnknownGroup.scalarmult', file=pure25519.config.spa_file)
        if 'scalarmult' in pure25519.config.verbose:
            print('ElementOfUnknownGroup.scalarmult')
        if isinstance(s, ElementOfUnknownGroup):
            raise TypeError("elements cannot be multiplied together")
        assert s >= 0
        product = scalarmult_element_safe_slow(self.XYTZ, s)
        ret = ElementOfUnknownGroup(product)
        if pure25519.config.spa:
            print('', file=pure25519.config.spa_file)
        return ret

    def to_bytes(self):
        return encodepoint(xform_extended_to_affine(self.XYTZ))
    def __eq__(self, other):
        return self.to_bytes() == other.to_bytes()
    def __ne__(self, other):
        return not self == other

class Element(ElementOfUnknownGroup):
    # this only holds elements in the main 1*L subgroup. It never holds Zero,
    # or elements of order 1/2/4/8, or 2*L/4*L/8*L.

    def add(self, other):
        if not isinstance(other, ElementOfUnknownGroup):
            raise TypeError("elements can only be added to other elements")
        sum_element = ElementOfUnknownGroup.add(self, other)
        if sum_element is Zero:
            return sum_element
        if isinstance(other, Element):
            # adding two subgroup elements results in another subgroup
            # element, or Zero, and we've already excluded Zero
            return Element(sum_element.XYTZ)
        # not necessarily a subgroup member, so assume not
        return sum_element

    def scalarmult(self, s):
        if pure25519.config.spa:
            print('Element.scalarmult', file=pure25519.config.spa_file)
        if 'scalarmult' in pure25519.config.verbose:
            print('Element.scalarmult')
        if isinstance(s, ElementOfUnknownGroup):
            raise TypeError("elements cannot be multiplied together")
        # scalarmult of subgroup members can be done modulo the subgroup
        # order, and using the faster non-unified function.
        if 'scalarmult' in pure25519.config.verbose:
            print('s//L:      ', s//L)
            print('s:         ', s.to_bytes(32, 'little').hex())
        s = s % L
        if 'scalarmult' in pure25519.config.verbose:
            print('s%L:       ', s.to_bytes(32, 'little').hex())
            # print('bin(s):', bin(s)[2:])
        # scalarmult(s=0) gets you Zero
        if s == 0:
            return Zero
        # scalarmult(s=1) gets you self, which is a subgroup member
        # scalarmult(s<grouporder) gets you a different subgroup member
        ret = Element(scalarmult_element(self.XYTZ, s))
        if 'scalarmult' in pure25519.config.verbose:
            (X1, Y1, Z1, T1) = self.XYTZ
            print('X1:        ', X1.to_bytes(32, 'little').hex())
            print('Y1:        ', Y1.to_bytes(32, 'little').hex())
            print('Z1:        ', Z1.to_bytes(32, 'little').hex())
            print('T1:        ', T1.to_bytes(32, 'little').hex())
            print('s:         ', s.to_bytes(32, 'little').hex())
            print('ret:       ', ret.to_bytes().hex())

        # ret_it = Element(scalarmult_element_it(self.XYTZ, s))
        # if 'scalarmult' in pure25519.config.verbose:
        #     print('ret_it:    ', ret_it.to_bytes().hex())

        # ret_it_swap,_ = scalarmult_element_it_swap(self.XYTZ, s)
        # ret_it_swap = Element(ret_it_swap)
        # if 'scalarmult' in pure25519.config.verbose:
        #     print('ret_it_swp:', ret_it_swap.to_bytes().hex())

        if pure25519.config.spa:
            print('\nswap\n', end='', file=pure25519.config.spa_file)
        ret_swap,_ = scalarmult_element_swap(self.XYTZ, s)
        ret_swap = Element(ret_swap)
        if 'scalarmult' in pure25519.config.verbose:
            print('ret_swap:  ', ret_swap.to_bytes().hex())

        if pure25519.config.spa:
            print('', file=pure25519.config.spa_file)
        return ret

    # negation and subtraction only make sense for the main subgroup
    def negate(self):
        # slow. Prefer e.scalarmult(-pw) to e.scalarmult(pw).negate()
        return Element(scalarmult_element(self.XYTZ, L-2))
    def subtract(self, other):
        return self.add(other.negate())

class _ZeroElement(ElementOfUnknownGroup):
    def add(self, other):
        return other # zero+anything = anything
    def scalarmult(self, s):
        if 'scalarmult' in pure25519.config.verbose:
            print('_ZeroElement.scalarmult')
        return self # zero*anything = zero
    def negate(self):
        return self # -zero = zero
    def subtract(self, other):
        return self.add(other.negate())


Base = Element(xform_affine_to_extended(B))
Zero = _ZeroElement(xform_affine_to_extended((0,1))) # the neutral (identity) element

_zero_bytes = Zero.to_bytes()


def arbitrary_element(seed): # unknown DL
    # TODO: if we don't need uniformity, maybe use just sha256 here?
    hseed = hashlib.sha512(seed).digest()
    y = int(binascii.hexlify(hseed), 16) % Q

    # we try successive Y values until we find a valid point
    for plus in itertools.count(0):
        y_plus = (y + plus) % Q
        x = xrecover(y_plus)
        Pa = [x,y_plus] # no attempt to use both "positive" and "negative" X

        # only about 50% of Y coordinates map to valid curve points (I think
        # the other half give you points on the "twist").
        if not isoncurve(Pa):
            continue

        P = ElementOfUnknownGroup(xform_affine_to_extended(Pa))
        # even if the point is on our curve, it may not be in our particular
        # (order=L) subgroup. The curve has order 8*L, so an arbitrary point
        # could have order 1,2,4,8,1*L,2*L,4*L,8*L (everything which divides
        # the group order).

        # [I MAY BE COMPLETELY WRONG ABOUT THIS, but my brief statistical
        # tests suggest it's not too far off] There are phi(x) points with
        # order x, so:
        #  1 element of order 1: [(x=0,y=1)=Zero]
        #  1 element of order 2 [(x=0,y=-1)]
        #  2 elements of order 4
        #  4 elements of order 8
        #  L-1 elements of order L (including Base)
        #  L-1 elements of order 2*L
        #  2*(L-1) elements of order 4*L
        #  4*(L-1) elements of order 8*L

        # So 50% of random points will have order 8*L, 25% will have order
        # 4*L, 13% order 2*L, and 13% will have our desired order 1*L (and a
        # vanishingly small fraction will have 1/2/4/8). If we multiply any
        # of the 8*L points by 2, we're sure to get an 4*L point (and
        # multiplying a 4*L point by 2 gives us a 2*L point, and so on).
        # Multiplying a 1*L point by 2 gives us a different 1*L point. So
        # multiplying by 8 gets us from almost any point into a uniform point
        # on the correct 1*L subgroup.

        P8 = P.scalarmult(8)

        # if we got really unlucky and picked one of the 8 low-order points,
        # multiplying by 8 will get us to the identity (Zero), which we check
        # for explicitly.
        if is_extended_zero(P8.XYTZ):
            continue

        # Test that we're finally in the right group. We want to scalarmult
        # by L, and we want to *not* use the trick in Group.scalarmult()
        # which does x%L, because that would bypass the check we care about.
        # P is still an _ElementOfUnknownGroup, which doesn't use x%L because
        # that's not correct for points outside the main group.
        assert is_extended_zero(P8.scalarmult(L).XYTZ)

        return Element(P8.XYTZ)
    # never reached

def bytes_to_unknown_group_element(bytes):
    # this accepts all elements, including Zero and wrong-subgroup ones
    if bytes == _zero_bytes:
        return Zero
    XYTZ = xform_affine_to_extended(decodepoint(bytes))
    return ElementOfUnknownGroup(XYTZ)

def bytes_to_element(bytes):
    # this strictly only accepts elements in the right subgroup
    P = bytes_to_unknown_group_element(bytes)
    if P is Zero:
        raise ValueError("element was Zero")
    if not is_extended_zero(P.scalarmult(L).XYTZ):
        raise ValueError("element is not in the right group")
    # the point is in the expected 1*L subgroup, not in the 2/4/8 groups,
    # or in the 2*L/4*L/8*L groups. Promote it to a correct-group Element.
    return Element(P.XYTZ)

def H(m):
    return hashlib.sha512(m).digest()

def publickey(seed):
    # turn first half of SHA512(seed) into scalar, then into point
    assert len(seed) == 32
    a = bytes_to_clamped_scalar(H(seed)[:32])
    if 'pk' in pure25519.config.verbose:
        print(f'H(seed):    {H(seed)[:32].hex()}')
        print(f"clamped(a): {a.to_bytes(32, 'little').hex()}")
    A = Base.scalarmult(a)
    

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


# Added by me below

def scalarmult_element_it(pt, n): # extended->extended
    # iterative version of `scalarmult_element(pt, n)`
    ret = xform_affine_to_extended((0,1))
    for i in f'{n:0252b}':
        ret = double_element(ret)
        if i == '1':
            ret = _add_elements_nonunfied(ret, pt)
    return ret

def scalarmult_element_swap(pt, n): # extended->extended
    # swap version of `scalarmult_element(pt, n)`
    # https://github.com/21dotco/two1-python/blob/master/two1/crypto/ecdsa_python.py#L31
    assert n >= 0
    if n==0:
        return xform_affine_to_extended((0,1)), pt

    r0, p = scalarmult_element_swap(pt, n>>1)

    if n & 1:
        r0 = _add_elements_nonunfied(r0, p)
        p = double_element(p)
        return r0, p
    else:
        p = _add_elements_nonunfied(r0, p)
        r0 = double_element(r0)
        return r0, p

def scalarmult_element_it_swap(pt, n): # extended->extended
    # iterative swap version of `scalarmult_element(pt, n)`
    # https://github.com/21dotco/two1-python/blob/master/two1/crypto/ecdsa_python.py#L31
    r0 = xform_affine_to_extended((0,1))
    p = pt
    for i in f'{n:0252b}':
        if i == '1':
            r0 = _add_elements_nonunfied(r0, p)
            p = double_element(p)
        else:
            p = _add_elements_nonunfied(r0, p)
            r0 = double_element(r0)
    return r0,p
