;;; This is a CL implementation of Minisign verification with no dependencies.
;;; We don't support the legacy format and don't enforce comment length limits.
;;; It provides a single function, `verify', which returns the comments
;;; associated with the signature if the signature is valid and signals the
;;; condition `verification-error' if the signature is malformed or invalid. For
;;; portability reasons, input and output are based on octets, not characters.
;;;
;;; You may wonder why this exists, and especially why it implements crypto
;;; primitives from scratch; isn't that bad? The reason is that Common Lisp has
;;; a notorious bootstrapping problem where package managers such as Quicklisp
;;; must ensure authenticity before they can install packages that could do so.
;;; Full-blown cryptographic libraries are too bulky to vendor with the package
;;; manager (and might end up becoming outdated there) or require FFI (which is
;;; its own can of worms), whereas this is a single small and portable file that
;;; can be vendored with ease.
;;;
;;; In this usecase, there are no secrets to be kept, no randomness to ensure,
;;; and no side-channels to cover; all that matters is that the signature scheme
;;; is secure, easy to implement with the base language, and has established
;;; signing tools so that you don't have to implement that (much harder) part.
;;;
;;; Minisign satisfies these requirements; it's an established simple format
;;; based (through libsodium) on Blake2b-512 and Ed25519, both of which are easy
;;; to implement off their respective RFCs.
;;;
;;; Keep in mind that Blake2b-512 makes heavy use of 64-bit arithmetic, which is
;;; very fast on SBCL but much slower on many other implementations. We provide
;;; an alternative implementation based on split 32-bit arithmetic, but on
;;; 32-bit platforms, even that might be slow, so consider keeping your
;;; bootstrapping data in the low megabyte range.
(cl:defpackage #:semz.minisign-verify
  (:use #:cl)
  (:export #:verification-error
           #:verify))
(cl:in-package #:semz.minisign-verify)

(defparameter *use-split-blake-p*
  #+(or sbcl abcl) nil
  #-(or sbcl abcl) t
  "If true, use an implementation of Blake2b-512 that's based on split 32-bit
arithmetic. This can significantly improve performance on many implementations.")

(define-condition verification-error (simple-error) ()
  (:documentation "Signalled when verification fails, for whatever reason."))

(defun die (msg &rest args)
  (error 'verification-error :format-control msg :format-arguments args))

(deftype ub8 ()
  '(unsigned-byte 8))

(deftype ub64 ()
  '(unsigned-byte 64))

(deftype buffer (&optional (length '*))
  `(simple-array ub8 (,length)))

(defmacro get-le (n data offset)
  (check-type n integer)
  `(logior ,@(loop :for i :from 0 :below n
                   :collect `(ash (aref ,data (+ ,offset ,i)) ,(* 8 i)))))

(declaim (ftype (function (ub64 ub64) ub64) ub64+)
         (ftype (function (ub64 (integer 0 63)) ub64) rotr64)
         (inline ub64+ rotr64))

(defun ub64+ (x y)
  (declare (type ub64 x y))
  (ldb (byte 64 0) (+ x y)))

(defun rotr64 (x y)
  (declare (type ub64 x)
           (type (integer 0 63) y))
  (logior (ldb (byte 64 0) (ash x (- y)))
          (ldb (byte 64 0) (ash x (- 64 y)))))

;;; Macros to support 32-bit split implementations of 64-bit arithmetic.
(defmacro ub64+/s (destl desth src1l src1h src2l src2h)
  (let ((sum (gensym)))
    `(let ((,sum (+ ,src1l ,src2l)))
       (declare (type (unsigned-byte 33) ,sum))
       (psetf ,destl (ldb (byte 32 0) ,sum)
              ,desth (ldb (byte 32 0) (+ ,src1h ,src2h (ash ,sum -32)))))))

(defmacro rotr64/s (destl desth xl xh rot)
  ;; We only need constants, which lets us swap high/low at compilation time.
  (check-type rot (integer 0 63))
  (when (> rot 32)
    (rotatef destl desth)
    (decf rot 32))
  `(psetf ,destl (logior (ash ,xl ,(- rot)) (ash (ldb (byte ,rot 0) ,xh) ,(- 32 rot)))
          ,desth (logior (ash ,xh ,(- rot)) (ash (ldb (byte ,rot 0) ,xl) ,(- 32 rot)))))


;;;; Blake2b-512 (keyless)
;;;
;;; Used to hash the actual data, so this is the only performance-relevant part.
;;; This implementation is directly based on the one in RFC 7693, but uses
;;; variables instead of a 16-element array for temporaries. The split
;;; arithmetic version is a direct translation of the generic 64-bit code.

(defparameter *blake2b-init-vector*
  (map '(simple-array ub64 (8)) #'identity
       '(#x6A09E667F3BCC908 #xBB67AE8584CAA73B
         #x3C6EF372FE94F82B #xA54FF53A5F1D36F1
         #x510E527FADE682D1 #x9B05688C2B3E6C1F
         #x1F83D9ABFB41BD6B #x5BE0CD19137E2179)))

(defparameter *blake2b-sigma*
  (let* ((a (make-array '(12 16) :element-type 'ub8))
         (str "
         SIGMA[0] |  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 |
         SIGMA[1] | 14 10  4  8  9 15 13  6  1 12  0  2 11  7  5  3 |
         SIGMA[2] | 11  8 12  0  5  2 15 13 10 14  3  6  7  1  9  4 |
         SIGMA[3] |  7  9  3  1 13 12 11 14  2  6  5 10  4  0 15  8 |
         SIGMA[4] |  9  0  5  7  2  4 10 15 14  1 11 12  6  8  3 13 |
         SIGMA[5] |  2 12  6 10  0 11  8  3  4 13  7  5 15 14  1  9 |
         SIGMA[6] | 12  5  1 15 14 13  4 10  0  7  6  3  9  2  8 11 |
         SIGMA[7] | 13 11  7 14 12  1  3  9  5  0 15  4  8  6  2 10 |
         SIGMA[8] |  6 15 14  9 11  3  0  8 12  2 13  7  1  4 10  5 |
         SIGMA[9] | 10  2  8  4  7  6  1  5 15 11  9 14  3 12 13  0 |")
         (pos 0))
    (dotimes (i 10)
      (setf pos (+ 3 (position #\] str :start pos)))
      (dotimes (j 16)
        (multiple-value-bind (int new-pos)
            (parse-integer str :start pos :junk-allowed t)
          (setf (aref a i j) int
                pos new-pos))))
    (dotimes (j 16)   (setf (aref a 10 j) (aref a 0 j)))
    (dotimes (j 16 a) (setf (aref a 11 j) (aref a 1 j)))))

(defstruct b2b
  ;; Input buffer and its fill pointer.
  (b (make-array 128 :element-type 'ub8 :initial-element 0)
   :type (simple-array ub8 (128)))
  (fp 0 :type (integer 0 128))
  ;; Hash state.
  (h (let ((a (subseq *blake2b-init-vector* 0)))
       (setf (aref a 0) (logxor (aref a 0) #x01010000 (ash 0 8) 64))
       a)
   :type (simple-array ub64 (8)))
  ;; Number of bytes hashed so far.
  (count 0 :type (integer 0 *)))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *blake-vars*
    '(v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15))
  (defparameter *blake-var-decls*
    (loop :for v :in *blake-vars*
          :for i :from 0
          :collect (if (< i 8)
                       `(,v (aref (b2b-h ctx) ,i))
                       `(,v (aref (the (simple-array ub64 (8)) *blake2b-init-vector*)
                                  ,(- i 8)))))))

(defun blake2b-compress (ctx lastp)
  (declare (optimize speed))
  (let ((sigma *blake2b-sigma*)
        (m (make-array 16 :element-type 'ub64))
        . #.*blake-var-decls*)
    (declare (type (simple-array ub8 (12 16)) sigma)
             (type ub64 . #.*blake-vars*)
             (dynamic-extent m))
    (setf v12 (logxor v12 (ldb (byte 64  0) (b2b-count ctx)))
          v13 (logxor v13 (ldb (byte 64 64) (b2b-count ctx))))
    (when lastp
      (setf v14 (ldb (byte 64 0) (lognot v14))))

    (dotimes (i 16)
      (setf (aref m i) (get-le 8 (b2b-b ctx) (* 8 i))))
    (dotimes (i 12)
      (macrolet ((mix (a b c d j)
                   (labels ((v (i) (elt *blake-vars* i))
                            (msig (j) `(aref m (aref sigma i ,j)))
                            (r (i1 i2 i3 rot add)
                              `(setf ,(v i1) (ub64+ ,add (ub64+ ,(v i1) ,(v i2)))
                                     ,(v i3) (rotr64 (logxor ,(v i3) ,(v i1))
                                                     ,rot))))
                     `(progn
                        ,(r a b d 32 (msig (+ j 0)))
                        ,(r c d b 24 0)
                        ,(r a b d 16 (msig (+ j 1)))
                        ,(r c d b 63 0)))))
        (mix 0 4  8 12  0)
        (mix 1 5  9 13  2)
        (mix 2 6 10 14  4)
        (mix 3 7 11 15  6)
        (mix 0 5 10 15  8)
        (mix 1 6 11 12 10)
        (mix 2 7  8 13 12)
        (mix 3 4  9 14 14)))
    (progn . #.(loop :for i :from 0 :below 8
                     :collect `(setf (aref (b2b-h ctx) ,i)
                                     (logxor (aref (b2b-h ctx) ,i)
                                             ,(elt *blake-vars* i)
                                             ,(elt *blake-vars* (+ i 8))))))
    nil))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *blake-vars/half*
    '(v0l v0h v1l v1h v2l v2h v3l v3h v4l v4h v5l v5h v6l v6h v7l v7h v8l v8h
      v9l v9h v10l v10h v11l v11h v12l v12h v13l v13h v14l v14h v15l v15h))
  (defparameter *blake-var-decls/half*
    (loop :for v :in *blake-vars/half*
          :for i :from 0
          :collect `(,v
                     (ldb (byte 32 ,(* 32 (mod i 2)))
                          ,(if (< i 16)
                               `(aref (b2b-h ctx) ,(floor i 2))
                               `(aref (the (simple-array ub64 (8)) *blake2b-init-vector*)
                                      ,(- (floor i 2) 8))))))))

(deftype ub32 ()
  '(unsigned-byte 32))

;;; Drop-in replacement for blake2b-compress which uses 32-bit arithmetic.
(defun blake2b-compress/split (ctx lastp)
  (declare (optimize speed))
  (let ((sigma *blake2b-sigma*)
        (m (make-array 32 :element-type 'ub32))
        . #.*blake-var-decls/half*)
    (declare (type (simple-array ub8 (12 16)) sigma)
             (type ub32 . #.*blake-vars/half*)
             (dynamic-extent m))
    (setf v12l (logxor v12l (ldb (byte 32  0) (b2b-count ctx)))
          v12h (logxor v12h (ldb (byte 32 32) (b2b-count ctx)))
          v13l (logxor v13l (ldb (byte 32 64) (b2b-count ctx)))
          v13h (logxor v13h (ldb (byte 32 96) (b2b-count ctx))))
    (when lastp
      (setf v14l (ldb (byte 32 0) (lognot v14l))
            v14h (ldb (byte 32 0) (lognot v14h))))

    (dotimes (i 32)
      (setf (aref m i) (get-le 4 (b2b-b ctx) (* 4 i))))
    (dotimes (i 12)
      (macrolet ((mix (a b c d j)
                   (labels ((vl (i) (elt *blake-vars/half* (+ i i)))
                            (vh (i) (elt *blake-vars/half* (+ i i 1)))
                            (msigl (j) `(aref m (+ (* 2 (aref sigma i ,j)) 0)))
                            (msigh (j) `(aref m (+ (* 2 (aref sigma i ,j)) 1)))
                            (r (i1 i2 i3 rot add-index)
                              (let ((xl (gensym)) (xh (gensym)))
                                `(let ((,xl 0) (,xh 0))
                                   (declare (type ub32 ,xl ,xh))
                                   (ub64+/s ,xl ,xh ,(vl i1) ,(vh i1) ,(vl i2) ,(vh i2))
                                   (ub64+/s ,(vl i1) ,(vh i1) ,xl ,xh
                                            ,(if add-index (msigl add-index) 0)
                                            ,(if add-index (msigh add-index) 0))
                                   (setf ,xl (logxor ,(vl i3) ,(vl i1))
                                         ,xh (logxor ,(vh i3) ,(vh i1)))
                                   (rotr64/s ,(vl i3) ,(vh i3) ,xl ,xh ,rot)))))
                     `(progn
                        ,(r a b d 32 (+ j 0))
                        ,(r c d b 24 nil)
                        ,(r a b d 16 (+ j 1))
                        ,(r c d b 63 nil)))))
        (mix 0 4  8 12  0)
        (mix 1 5  9 13  2)
        (mix 2 6 10 14  4)
        (mix 3 7 11 15  6)
        (mix 0 5 10 15  8)
        (mix 1 6 11 12 10)
        (mix 2 7  8 13 12)
        (mix 3 4  9 14 14)))
    (progn
      . #.(loop :for i :from 0 :below 8
                :collect `(setf (aref (b2b-h ctx) ,i)
                                (logxor (aref (b2b-h ctx) ,i)
                                        (logior (ash ,(elt *blake-vars/half* (+ i i)) 0)
                                                (ash ,(elt *blake-vars/half* (+ i i 1)) 32))
                                        (logior (ash ,(elt *blake-vars/half* (+ 16 i i)) 0)
                                                (ash ,(elt *blake-vars/half* (+ 16 i i 1)) 32))))))
    nil))

(defun blake2b-update (ctx data start end)
  (assert (<= 0 start end (length data)))
  (dotimes (i (- end start))
    (when (= (b2b-fp ctx) 128)
      (incf (b2b-count ctx) 128)
      (if *use-split-blake-p*
          (blake2b-compress/split ctx nil)
          (blake2b-compress ctx nil))
      (setf (b2b-fp ctx) 0))
    (setf (aref (b2b-b ctx) (b2b-fp ctx)) (aref data (+ start i)))
    (incf (b2b-fp ctx))))

(defun blake2b-final (ctx)
  (incf (b2b-count ctx) (b2b-fp ctx))
  (fill (b2b-b ctx) 0 :start (b2b-fp ctx))
  (blake2b-compress ctx t)
  (let ((result (make-array 64 :element-type 'ub8)))
    (dotimes (i 64 result)
      (setf (aref result i)
            (logand (ash (aref (b2b-h ctx) (ash i -3))
                         (* -8 (logand i 7)))
                    #xFF)))))

(defun blake2b (data start end)
  (let ((ctx (make-b2b)))
    (blake2b-update ctx data start end)
    (blake2b-final ctx)))


;;;; SHA-512
;;;
;;; Required for Ed25519, but the longest thing we ever hash is the trusted
;;; comment field, so performance is irrelevant. Directly based on RFC 6234.

(defparameter *sha-512-iv*
  (let ((a (make-array 8 :element-type 'ub64))
        (str "
         H(0)0 = 6a09e667f3bcc908
         H(0)1 = bb67ae8584caa73b
         H(0)2 = 3c6ef372fe94f82b
         H(0)3 = a54ff53a5f1d36f1
         H(0)4 = 510e527fade682d1
         H(0)5 = 9b05688c2b3e6c1f
         H(0)6 = 1f83d9abfb41bd6b
         H(0)7 = 5be0cd19137e2179")
        (pos 0))
    (dotimes (i 8 a)
      (setf pos (1+ (position #\= str :start pos)))
      (multiple-value-bind (int new-pos)
          (parse-integer str :start pos :radix 16 :junk-allowed t)
        (setf (aref a i) int
              pos new-pos)))))

(defparameter *sha-512-k*
  (let ((a (make-array 80 :element-type 'ub64))
        (str "
   428a2f98d728ae22 7137449123ef65cd b5c0fbcfec4d3b2f e9b5dba58189dbbc
   3956c25bf348b538 59f111f1b605d019 923f82a4af194f9b ab1c5ed5da6d8118
   d807aa98a3030242 12835b0145706fbe 243185be4ee4b28c 550c7dc3d5ffb4e2
   72be5d74f27b896f 80deb1fe3b1696b1 9bdc06a725c71235 c19bf174cf692694
   e49b69c19ef14ad2 efbe4786384f25e3 0fc19dc68b8cd5b5 240ca1cc77ac9c65
   2de92c6f592b0275 4a7484aa6ea6e483 5cb0a9dcbd41fbd4 76f988da831153b5
   983e5152ee66dfab a831c66d2db43210 b00327c898fb213f bf597fc7beef0ee4
   c6e00bf33da88fc2 d5a79147930aa725 06ca6351e003826f 142929670a0e6e70
   27b70a8546d22ffc 2e1b21385c26c926 4d2c6dfc5ac42aed 53380d139d95b3df
   650a73548baf63de 766a0abb3c77b2a8 81c2c92e47edaee6 92722c851482353b
   a2bfe8a14cf10364 a81a664bbc423001 c24b8b70d0f89791 c76c51a30654be30
   d192e819d6ef5218 d69906245565a910 f40e35855771202a 106aa07032bbd1b8
   19a4c116b8d2d0c8 1e376c085141ab53 2748774cdf8eeb99 34b0bcb5e19b48a8
   391c0cb3c5c95a63 4ed8aa4ae3418acb 5b9cca4f7763e373 682e6ff3d6b2b8a3
   748f82ee5defb2fc 78a5636f43172f60 84c87814a1f0ab72 8cc702081a6439ec
   90befffa23631e28 a4506cebde82bde9 bef9a3f7b2c67915 c67178f2e372532b
   ca273eceea26619c d186b8c721c0c207 eada7dd6cde0eb1e f57d4f7fee6ed178
   06f067aa72176fba 0a637dc5a2c898a6 113f9804bef90dae 1b710b35131c471b
   28db77f523047d84 32caab7b40c72493 3c9ebe0a15c9bebc 431d67c49c100d4c
   4cc5d4becb3e42b6 597f299cfc657e2a 5fcb6fab3ad6faec 6c44198c4a475817")
        (pos 0))
    (dotimes (i 80 a)
      (multiple-value-bind (int new-pos)
          (parse-integer str :start pos :radix 16 :junk-allowed t)
        (setf (aref a i) int
              pos (+ 1 new-pos))))))

(defstruct s512
  (b (make-array 128 :element-type 'ub8 :initial-element 0)
   :type (buffer 128))
  (fp 0 :type (integer 0 1024))
  (h (subseq *sha-512-iv* 0)
   :type (simple-array ub64 (8)))
  ;; SHA-512 uses bit length, but we store it in bytes and multiply at the end.
  (count 0 :type (integer 0 *)))

(defun sha-512-compress (ctx)
  (flet ((ch  (x y z) (logxor (logand x y) (logandc1 x z)))
         (maj (x y z) (logxor (logand x y) (logand   x z) (logand y z)))
         (bsig0 (x)   (logxor (rotr64 x 28) (rotr64 x 34) (rotr64 x 39)))
         (bsig1 (x)   (logxor (rotr64 x 14) (rotr64 x 18) (rotr64 x 41)))
         (ssig0 (x)   (logxor (rotr64 x  1) (rotr64 x  8) (ash x -7)))
         (ssig1 (x)   (logxor (rotr64 x 19) (rotr64 x 61) (ash x -6))))
    (declare (inline ch maj bsig0 bsig1 ssig0 ssig1)
             (ftype (function (ub64) ub64) bsig0 bsig1 ssig0 ssig1)
             (ftype (function (ub64 ub64 ub64) ub64) ch maj))
    (let ((w (make-array 80 :element-type 'ub64))
          (k *sha-512-k*))
      (declare (type (simple-array ub64 (*)) w k))
      (dotimes (i 16)
        (setf (aref w i)
              (logior . #.(loop :for j :from 0 :below 8
                                :collect `(ash (aref (s512-b ctx) (+ (* 8 i) ,j)) (* 8 (- 7 ,j)))))))
      (loop :for i :from 16 :below 80 :do
        (setf (aref w i)
              (ub64+ (ub64+ (ssig1 (aref w (- i 2)))
                            (aref w (- i 7)))
                     (ub64+ (ssig0 (aref w (- i 15)))
                            (aref w (- i 16))))))
      (let #.(loop :for v :in '(a b c d e f g h)
                   :for i :from 0
                   :collect `(,v (aref (s512-h ctx) ,i)))
        (declare (type ub64 a b c d e f g h))
        (dotimes (i 80)
          (let ((t1 (ub64+ (ub64+ h (bsig1 e))
                           (ub64+ (ub64+ (ch e f g)
                                         (aref k i))
                                  (aref w i))))
                (t2 (ub64+ (bsig0 a)
                           (maj a b c))))
            (shiftf h g f e (ub64+ d t1))
            (shiftf d c b a (ub64+ t1 t2))))
        (setf . #.(loop :for v :in '(a b c d e f g h)
                        :for i :from 0
                        :collect `(aref (s512-h ctx) ,i)
                        :collect `(ub64+ ,v (aref (s512-h ctx) ,i))))))))

(defun sha-512-update (ctx data start end)
  (assert (<= 0 start end (length data)))
  (dotimes (i (- end start))
    (when (= (s512-fp ctx) 128)
      (incf (s512-count ctx) 128)
      (sha-512-compress ctx)
      (setf (s512-fp ctx) 0))
    (setf (aref (s512-b ctx) (s512-fp ctx)) (aref data (+ start i)))
    (incf (s512-fp ctx))))

(defun sha-512-final (ctx)
  (let* ((byte-length (+ (s512-count ctx) (s512-fp ctx)))
         (bit-length (* 8 byte-length))
         (fp (s512-fp ctx)))
    ;; Should never happen; we only hash tiny data.
    (assert (< bit-length (expt 2 128)))
    ;; The appended 1 bit always occupies its own byte; if that #x80 byte
    ;; doesn't fit, start a new block and make it fit.
    (when (= fp 128)
      (sha-512-compress ctx)
      (setf fp 0))
    (setf (aref (s512-b ctx) fp) #x80)
    (incf fp)
    ;; Zero out the block for padding purposes.
    (fill (s512-b ctx) 0 :start fp)
    ;; If the length doesn't fit, pad for one more block.
    (when (> (+ fp 16) 128)
       (sha-512-compress ctx)
       (fill (s512-b ctx) 0))
    ;; Set length and finish.
    (setf . #.(loop :for i :from 0 :below 8
                    :collect `(aref (s512-b ctx) ,(- 127 i))
                    :collect `(ldb (byte 8 ,(* 8 i)) (* byte-length 8))))
    (sha-512-compress ctx))

  (let ((result (make-array 64 :element-type 'ub8)))
    (dotimes (i 8 result)
      (dotimes (j 8)
        (setf (aref result (+ (* 8 i) j))
              (ldb (byte 8 (* 8 (- 7 j)))
                   (aref (s512-h ctx) i)))))))

(defun sha-512 (data start end)
  (let ((ctx (make-s512)))
    (sha-512-update ctx data start end)
    (sha-512-final ctx)))


;;;; Ed25519
;;;
;;; The actual signature scheme. Based on RFC 8032; I tried to keep the formulae
;;; as similar to the original formatting as possible.

(defconstant +p+ (- (expt 2 255) 19))
(defconstant +L+ (+ (expt 2 252) 27742317777372353535851937790883648493))
(defconstant +d+ 37095705934669439343138083508754565189542113879843219016388785533085940283555)
(defconstant +Bx+ 15112221349535400772501151409588531511454012693041857206046113283949847762202)
(defconstant +By+ 46316835694926478169428394003475163141307993866256225615783033603165251855960)

(defun modp+ (&rest args) (mod (apply #'+ args) +p+))
(defun modp- (&rest args) (mod (apply #'- args) +p+))
(defun modp* (&rest args) (mod (apply #'* args) +p+))

(defun modpexpt (x n)
  ;; Standard square & multiply; at all times, the result is a*x^n mod p.
  (let ((a 1))
    (loop :while (> n 0) :do
      (if (evenp n)
          (setf x (modp* x x)
                n (floor n 2))
          (setf a (modp* a x)
                n (- n 1))))
    a))

;;; A point in homogeneous coordinates. (X:Y:Z:T) => x=X/Z, y=Y/Z, T=xyZ=XY/Z.
;;; The neutral point is (0,1), i.e. (0:1:1:0) (or (0:Z:Z:0) for Z /= 0).
(defstruct hpt
  (x 0 :type (integer 0 *))
  (y 1 :type (integer 0 *))
  (z 1 :type (integer 0 *))
  (t 0 :type (integer 0 *)))

(defun pt= (p1 p2)
  ;; Note the cross multiplication.
  (and (= (modp* (hpt-x p1) (hpt-z p2))
          (modp* (hpt-x p2) (hpt-z p1)))
       (= (modp* (hpt-y p1) (hpt-z p2))
          (modp* (hpt-y p2) (hpt-z p1)))))

(defun pt+ (p1 p2)
  (let* ((x1 (hpt-x p1)) (y1 (hpt-y p1)) (z1 (hpt-z p1)) (t1 (hpt-t p1))
         (x2 (hpt-x p2)) (y2 (hpt-y p2)) (z2 (hpt-z p2)) (t2 (hpt-t p2))
         (a (modp* (modp- y1 x1) (modp- y2 x2)))
         (b (modp* (modp+ y1 x1) (modp+ y2 x2)))
         (c (modp* t1 2 +d+ t2))
         (d (modp* z1 2 z2))
         (e (modp- b a))
         (f (modp- d c))
         (g (modp+ d c))
         (h (modp+ b a)))
    ;; The RFC lists this in XYTZ order for some reason.
    (make-hpt :x (modp* e f)
              :y (modp* g h)
              :t (modp* e h)
              :z (modp* f g))))

(defun pt* (n p)
  (check-type p hpt)
  ;; Standard square & multiply; at all times, the result is a+n*p.
  (let ((a (make-hpt)))
    (loop :while (> n 0) :do
      (if (evenp n)
          (setf p (pt+ p p)
                n (/ n 2))
          (setf a (pt+ a p)
                n (- n 1))))
    a))

(defun parse-ed25519-point (pt)
  (check-type pt (buffer 32))
  (let ((y (ldb (byte 255 0) (get-le 32 pt 0)))
        (x0 (ldb (byte 1 7) (aref pt 31))))
    (unless (< y +p+)
      (die "Invalid curve point."))
    (let* ((y2 (modp* y y))
           (u (modp+ y2 -1))
           (v (modp+ (modp* +d+ y2) 1))
           (x-cand (modp* u (modpexpt v 3)
                          (modpexpt (modp* u (modpexpt v 7))
                                    (/ (- +p+ 5) 8))))
           (vx2 (modp* v x-cand x-cand))
           (x (cond
                ((= vx2 u) x-cand)
                ((= vx2 (modp- u)) (modp* x-cand (modpexpt 2 (/ (- +p+ 1) 4))))
                (t (die "Point doesn't lie on the curve.")))))
      (cond
        ((and (= x0 1) (= x 0))
         (die "Point doesn't lie on the curve."))
        ((/= x0 (mod x 2))
         (setf x (modp- x))
         (make-hpt :x x :y y :z 1 :t (modp* x y)))
        (t (make-hpt :x x :y y :z 1 :t (modp* x y)))))))

(defun ed25519-verify (message signature pubkey)
  (check-type message buffer)
  (check-type signature (buffer 64))
  (check-type pubkey (buffer 32))
  (let ((r (parse-ed25519-point (subseq signature 0 32)))
        (s (get-le 32 signature 32))
        (a (parse-ed25519-point pubkey)))
    (unless (< s +L+)
      (die "Invalid integer S."))
    ;; By §5.1, dom2(F,C) is the empty string and PH(M) = M. For R and A, we
    ;; simply reuse the (unique) serialization from the input.
    (let* ((buf (concatenate 'buffer #() (subseq signature 0 32) pubkey message))
           (k (get-le 64 (sha-512 buf 0 (length buf)) 0)))
      (pt= (pt* s (make-hpt :x +Bx+ :y +By+ :z 1 :t (modp* +Bx+ +By+)))
           (pt+ r (pt* k a))))))


;;;; Base64 decoding
;;;
;;; Old faithful. Minisign uses short and junkless base64, so we keep it simple.

(defun decode-b64 (data)
  (check-type data buffer)
  (let ((n (length data)))
    (unless (zerop (mod n 4))
      (die "Invalid base64 length."))
    (let* ((translated
             (map 'buffer (lambda (c)
                            (cond ((<= #x41 c #x5A) (- c #x41))        ; A-Z
                                  ((<= #x61 c #x7A) (+ 26 (- c #x61))) ; a-z
                                  ((<= #x30 c #x39) (+ 52 (- c #x30))) ; 0-9
                                  ((= c #x2B) 62)                      ; +
                                  ((= c #x2F) 63)                      ; /
                                  ((= c #x3D) 255)                     ; =
                                  (t (die "Invalid base64 data."))))
                  data))
           (pad (position 255 translated)))
      (unless (or (null pad)
                  (= pad (- n 1))
                  (and (= pad (- n 2)) (= 255 (aref translated (- n 1)))))
        (die "Invalid base64 padding."))
      ;; Simplifies padding handling.
      (setf translated (substitute 0 255 translated))
      (let ((result (make-array (* 3/4 n) :element-type 'ub8))
            (out 0))
        (loop :for i :from 0 :below n :by 4
              :for tr = (logior (ash (aref translated (+ i 0)) 18)
                                (ash (aref translated (+ i 1)) 12)
                                (ash (aref translated (+ i 2))  6)
                                (ash (aref translated (+ i 3))  0))
              :do (setf (aref result (+ out 0)) (ldb (byte 8 16) tr))
                  (setf (aref result (+ out 1)) (ldb (byte 8  8) tr))
                  (setf (aref result (+ out 2)) (ldb (byte 8  0) tr))
                  (incf out 3))
        ;; The number of padding = characters coincides with the number of bytes
        ;; to remove at the end.
        (subseq result 0 (- (length result)
                            (- n (or pad n))))))))


;;;; The actual application code

(defun checksum-data (data)
  (if (streamp data)
      (let ((buf (make-array (expt 2 13) :element-type 'ub8))
            (ctx (make-b2b)))
        (loop :for end = (read-sequence buf data)
              :until (zerop end)
              :do (blake2b-update ctx buf 0 end))
        (blake2b-final ctx))
      (let ((buf (coerce data 'buffer)))
        (blake2b buf 0 (length buf)))))

(defun positions (item vector start end)
  (loop :for i :from start :below end
        :when (eql (aref vector i) item) :collect i))

(defun lines (data)
  ;; We operate on bytes to avoid any text encoding shenanigans.
  (let ((breaks (positions 10 data 0 (length data))))
    (mapcar (lambda (start end)
              (subseq data start
                      ;; Strip trailing carriage returns like Minisign does it.
                      (let ((last-non-cr (position-if (lambda (x) (/= x 13)) data
                                                      :start start :end end
                                                      :from-end t)))
                        (if (null last-non-cr)
                            start
                            (+ last-non-cr 1)))))
            (cons 0 (mapcar #'1+ breaks))
            (concatenate 'list breaks (list (length data))))))

;;; Adapted from Alexandria.
(defun starts-with-subseq (prefix seq)
  (let ((prefix-length (length prefix))
        (seq-length (length seq)))
    (and (<= prefix-length seq-length)
         (not (mismatch prefix seq :end2 prefix-length)))))

(defparameter *untrusted-prefix*
  ;; "untrusted comment: "
  (coerce #(117 110 116 114 117 115 116 101 100
            32 99 111 109 109 101 110 116 58 32)
          'buffer))

(defparameter *trusted-prefix*
  ;; "trusted comment: "
  (coerce #(116 114 117 115 116 101 100
            32 99 111 109 109 101 110 116 58 32)
          'buffer))

(defun parse-signature (signature)
  (let ((lines (lines signature)))
    (unless (>= (length lines) 4)
      (die "Too few lines; is this really a minisign signature?"))
    (unless (starts-with-subseq *untrusted-prefix* (elt lines 0))
      (die "Can't find untrusted comment."))
    (unless (starts-with-subseq *trusted-prefix* (elt lines 2))
      (die "Can't find trusted comment."))

    (let ((untrusted (subseq (elt lines 0) (length *untrusted-prefix*)))
          (sig-data (decode-b64 (elt lines 1)))
          (trusted (subseq (elt lines 2) (length *trusted-prefix*)))
          (global-sig (decode-b64 (elt lines 3))))
      (unless (= (length sig-data) (+ 2 8 64))
        (die "Invalid signature length."))
      (unless (= (length global-sig) 64)
        (die "Invalid global signature length."))
      (unless (equalp (subseq sig-data 0 2) #(69 68))
        (die "Unsupported signature algorithm: ~2,'0x ~2,'0x"
             (aref sig-data 0) (aref sig-data 1)))

      (values global-sig (subseq sig-data 10) (subseq sig-data 2 10) trusted untrusted))))

(defun parse-pubkey (pubkey)
  (let ((lines (lines pubkey)))
    (unless (>= (length lines) 2)
      (die "Too few lines; is this really a minisign public key?"))
    (unless (starts-with-subseq *untrusted-prefix* (elt lines 0))
      (die "Can't find untrusted comment."))

    (let ((data (decode-b64 (elt lines 1))))
      (unless (= (length data) (+ 2 8 32))
        (die "Invalid public key length."))
      (unless (equalp (subseq data 0 2) #(69 100))
        (die "Unsupported signature algorithm: ~2,'0x ~2,'0x"
             (aref data 0) (aref data 1)))

      (values (subseq data 10) (subseq data 2 10)))))

(defun verify (data signature pubkey)
  "Returns the trusted and untrusted comments of SIGNATURE if SIGNATURE is a valid
Minisign signature for DATA with respect to PUBKEY; signals VERIFICATION-ERROR
otherwise, including when SIGNATURE or PUBKEY are malformed.

DATA is a sequence or stream of octets. Stream data is read and used entirely.

SIGNATURE is the content of a Minisign signature file (as a sequence of octets).

PUBKEY is either the content of a Minisign public key file (as a sequence of
octets) or a function.

If PUBKEY is a function, it is called with the key ID (an array of 8 octets)
specified in SIGNATURE and must return either the content of an appropriate
Minisign public key file (which will then be used) or NIL (which will signal a
VERIFICATION-ERROR). This option allows the use of multiple public keys."
  (if (streamp data)
      (unless (subtypep (stream-element-type data) 'ub8)
        (error 'type-error :expected-type 'ub8 :datum (stream-element-type data)))
      (setf data (coerce data 'buffer)))

  (multiple-value-bind (global-sig data-sig used-key-id trusted untrusted)
      (handler-bind ((verification-error (lambda (c) (die "Can't parse signature: ~a" c))))
        (parse-signature (coerce signature 'buffer)))

    (when (functionp pubkey)
      (setf pubkey (or (funcall pubkey used-key-id)
                       (die "Unrecognized key ID: ~{~2,'0x~}" (coerce used-key-id 'list)))))
    (setf pubkey (coerce pubkey 'buffer))

    (multiple-value-bind (pubkey key-id)
        (handler-bind ((verification-error (lambda (c) (die "Can't parse public key: ~a" c))))
          (parse-pubkey pubkey))

      (unless (equalp key-id used-key-id)
        (die "Key ID doesn't match."))
      (unless (ed25519-verify (concatenate 'buffer data-sig trusted) global-sig pubkey)
        (die "Global signature doesn't match."))
      (unless (ed25519-verify (checksum-data data) data-sig pubkey)
        (die "Data signature doesn't match."))

      (values trusted untrusted))))
