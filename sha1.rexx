/* REXX */
/* SHA-1 implementation in REXX
   $VER: 1
   $AUTHOR: Iggy Drougge
   Notes:
   1. It is REXX, hence it is slow.
   2. Based on pseudocode found on Wikipedia: https://en.wikipedia.org/wiki/SHA-1#Examples_and_pseudocode
   3. Debug help and inspiration from http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA1.pdf
   4. Further inspiration from https://tools.ietf.org/html/rfc3174
*/
/* Note 1: All variables are unsigned 32-bit quantities and wrap modulo 232 when calculating, except for
        ml, the message length, which is a 64-bit quantity, and
        hh, the message digest, which is a 160-bit quantity.
Note 2: All constants in this pseudo code are in big endian.
        Within each word, the most significant byte is stored in the leftmost byte position */
numeric digits 20
DEBUG=0
message='The quick brown fox jumps over the lazy dog'
message='This is a test for theory of computation'
message='abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq'
message='abcde'
message='abc'

/* Initialize variables: */
h0 = '67452301'x
h1 = 'EFCDAB89'x
h2 = '98BADCFE'x
h3 = '10325476'x
h4 = 'C3D2E1F0'x

/* ml = message length in bits (always a multiple of the number of bits in a character). */
ml = length(message)*8
/* Pre-processing:
   append the bit '1' to the message e.g. by adding 0x80 if message length is a multiple of 8 bits. */
message = message || '10000000'b
padml = ml + 8
if padml>448 then do
	padlength = 512 - (padml // 512)
	message = message || copies('00'x,padlength/8)
	message = message || copies('00'x,448/8)
end
else do
	message=left(message,448/8,'00'x)
end
/* append ml, in a 64-bit big-endian integer. Thus, the total length is a multiple of 512 bits. */
message = message || right(d2c(ml),64/8,'00'x)
ml=length(message)*8

/* Process the message in successive 512-bit chunks:
   break message into 512-bit chunks */
chunk:
/* for each chunk
   break chunk into sixteen 32-bit big-endian words w[i], 0 ≤ i ≤ 15 */
do i = 0 to 15 while message~=''
	parse var message with 1 w.i +4 message
	if DEBUG then say 'W['left(i,2)']=' c2x(w.i)
end
/* Extend the sixteen 32-bit words into eighty 32-bit words:
   for i from 16 to 79
        w[i] = (w[i-3] xor w[i-8] xor w[i-14] xor w[i-16]) leftrotate 1 */
do i = 16 to 79
	j=i-3
	k=i-8
	l=i-14
	m=i-16
	w.i = bitxor(w.j,w.k)
	w.i = bitxor(w.i,w.l)
	w.i = bitxor(w.i,w.m)
	w.i = bitrol(w.i,1)
end
/* Initialize hash value for this chunk: */
a = h0
b = h1
c = h2
d = h3
e = h4

if DEBUG then say '        A        B        C        D        E     '
/* Main loop:
   for i from 0 to 79 */
do i = 0 to 79
    select
	/* if 0 ≤ i ≤ 19 then 
	   f = (b and c) or ((not b) and d)
       k = 0x5A827999 */
    	when i < 20 then do
			f = bitor(bitand(b,c),(bitand(bitnot(b),d))) 
			k = '5A827999'x
		end
	/* else if 20 ≤ i ≤ 39
       f = b xor c xor d
       k = 0x6ED9EBA1 */
		when i < 40 then do
			f = bitxor(bitxor(b,c),d)
			k = '6ED9EBA1'x
		end
	/* else if 40 ≤ i ≤ 59
       f = (b and c) or (b and d) or (c and d) 
       k = 0x8F1BBCDC */
		when i < 60 then do
			f = bitor(bitor(bitand(b,c),bitand(b,d)),bitand(c,d))
			k = '8F1BBCDC'x
		end
	/* else if 60 ≤ i ≤ 79
       f = b xor c xor d
       k = 0xCA62C1D6 */
		when i < 80 then do
			f = bitxor(bitxor(b,c),d)
			k = 'CA62C1D6'x
		end
		otherwise exit 20
	end
	/* temp = (a leftrotate 5) + f + e + k + w[i] */
	temp = bitrol(a,5)
	temp = c2d(temp)
	ftemp=f
	etemp=e
	ftemp=c2d(ftemp)
	etemp=c2d(etemp)
	temp = temp + ftemp
	temp = temp // 2**32
	temp = temp + etemp
	temp = temp // 2**32
	temp = temp + c2d(k)
	temp = temp // (2**32)
	temp = temp + c2d(w.i)
	temp = temp // (2**32)
	temp = right(d2c(temp),4,'0'x)
	e = d
    d = c
    /* c = b leftrotate 30 */
    c = bitrol(b,30)
    b = a
    a = temp

    if DEBUG then say 't='(left,i,2) c2x(a) c2x(b) c2x(c) c2x(d) c2x(e)
end
/* Add this chunk's hash to result so far:
    h0 = h0 + a
    h1 = h1 + b 
    h2 = h2 + c
    h3 = h3 + d
    h4 = h4 + e */
h0 = c2d(h0) + c2d(a)
h1 = c2d(h1) + c2d(b)
h2 = c2d(h2) + c2d(c)
h3 = c2d(h3) + c2d(d)
h4 = c2d(h4) + c2d(e)
h0 = h0 // (2**32)
h1 = h1 // (2**32)
h2 = h2 // (2**32)
h3 = h3 // (2**32)
h4 = h4 // (2**32)
h0 = d2c(h0)
h1 = d2c(h1)
h2 = d2c(h2)
h3 = d2c(h3)
h4 = d2c(h4)

ml = ml - 512
if ml > 0 then signal chunk

/* Produce the final hash value (big-endian) as a 160 bit number:
   hh = (h0 leftshift 128) or 
        (h1 leftshift 96)  or 
        (h2 leftshift 64)  or 
        (h3 leftshift 32)  or h4 */
hh = h0 || h1 || h2 || h3 || h4
say c2x(hh)
exit

byteswap: procedure
parse arg a +1 b +1 c +1 d +1
return d || c || b || a

c2b: procedure
return x2b(c2x(arg(1)))

b2c: procedure
return x2c(b2x(arg(1)))

bitnot: procedure
return b2c(translate(c2b(arg(1)),10,01))

bitrol: procedure
return b2c(right(c2b(arg(1)),32-arg(2),0) || left(c2b(arg(1)),arg(2)))
