;; Rough 1st attempt to implement DecodeBitMasks from p.6983 of ARMv8 Architecture Manual
;; - finds 5332 viable combinations

(define verbose (make-parameter #f))

(define-record bits (size value))
(record-writer (record-type-descriptor bits)
  (lambda (r p wr)
    (fprintf p "~v,'0b" (bits-size r) (val r))))

;; mask it when we reference value for now
(define (val x)
  (logand (bits-value x)
    (1- (ash 1 (bits-size x)))))

(define (concat a b)
  (make-bits (+ (bits-size a) (bits-size b))
    (logor (ash (val a) (bits-size b)) (val b))))

(define (NOT a)
  (make-bits (bits-size a) (lognot (val a))))

(define (AND a b)
  (make-bits (max (bits-size a) (bits-size b))
    (logand (val a) (val b))))

(define (OR a b)
  (make-bits (max (bits-size a) (bits-size b))
    (logor (val a) (val b))))

(define (ZeroExtend x n)
  (assert (>= n (bits-size x)))
  (concat (Zeros (- n (bits-size x))) x))

(define (Zeros n) (make-bits n 0))
(define (Ones n) (make-bits n (1- (ash 1 n))))

(define (Replicate64 x)
  (let-values ([(div mod) (div-and-mod 64 (bits-size x))])
    (assert (zero? mod))
    (let Rep ([r x] [n div])
      (if (= n 1)
          r
          (Rep (concat r x) (- n 1))))))

(define (ROR x shift)
  (assert (>= shift 0))
  (if (zero? shift)
      x
      (let* ([N (bits-size x)]
             [m (modulo shift N)]
             [result (OR (LSR x m) (LSL x (- N m)))]
             [carry_out "ignored"])
        result)))

(define (LSL x shift)
  (define N (bits-size x))
  (assert (>= shift 0))
  (if (zero? shift)
      x
      (let* ([shift (min shift N)]
             [extended_x (concat x (Zeros shift))]
             [result (make-bits N (val extended_x))])
        result)))

(define (LSR x shift)
  (define N (bits-size x))
  (assert (>= shift 0))
  (if (zero? shift)
      x
      (let* ([shift (min shift N)]
             [extended_x (ZeroExtend x (+ shift N))]
             [result (make-bits N (quotient (val extended_x) (expt 2 shift)))])
        result)))

;; note we only care about 1st return value
(define M 64) ;; aka datasize

(define (lognot64 x) (bitwise-xor (1- (ash 1 64)) x))

#;
(trace-define-syntax trace-let*
  (syntax-rules ()
    [(_ ([var expr] ...) b0 b1 ...)
     (let* ([var
             (let ([val expr])
               (printf "~10s = ~s\n" 'var val)
               val)]
            ...)
       b0 b1 ...)]))

;; For andi:
;;  N = bit 22    for 32-bit, N must be 0
;;  immr = 6 bits
;;  imms = 6 bits
;;  immediate? is #t
(define (decode-bit-mask immN imms immr immediate?)
  (let* ([immN (make-bits 1 immN)]
         [imms (make-bits 6 imms)]
         [immr (make-bits 6 immr)]
         [len (1- (bitwise-length (val (concat immN (NOT imms)))))]
         [_ (assert (> len 1))] ;; else undefined
         [_ (assert (>= M len))]
         [levels (ZeroExtend (Ones len) 6)]
         [_ (when immediate?
              (assert
               (not (= (val (AND imms levels)) (val levels)))))] ;; undefined
         [S (val (AND imms levels))]
         [R (val (AND immr levels))]
         [diff (- S R)]
         [esize (ash 1 len)]
         [d (val (make-bits len diff))]
         [welem (ZeroExtend (Ones (+ S 1)) esize)]
         [telem (ZeroExtend (Ones (+ d 1)) esize)]
         [wmask (Replicate64 (ROR welem R))]
         [tmask (Replicate64 telem)])
    ;; andi ignores tmask
    (values wmask #; tmask)))

(define (explore)
  (let ([ht (make-hashtable values =)])
    (do ([n 0 (+ n 1)]) ((> n 1))
      (do ([i 0 (+ i 1)]) ((= i 64))
        (do ([j 0 (+ j 1)]) ((= j 64))
          (guard
           (c [else
               (when (verbose)
                 (printf ";; (decode-bit-mask ~s ~s ~s #t) is disallowed\n" n i j))])
           (hashtable-update! ht (val (decode-bit-mask n i j #t))
             (lambda (prev)
               (cons (list n j i) ; (n j i) instead of (n i j) as bitmask is encoded as N:imms:immr instead of N:immr:imms 
                 prev))
             '())))))
    ht))

(define (dump ht)
  (vector-for-each
   (lambda (cell)
     (printf "~64,'0b =~:{ ~a ~6,'0b ~6,'0b~}\n" (car cell) (cdr cell)))
   (vector-sort
    (lambda (c1 c2)
      (< (car c1) (car c2)))
    (hashtable-cells ht)))
  (printf "~s unique values\n" (hashtable-size ht)))

(define (generate-lookup ht)
  (let ([new (make-hashtable values =)])
    (vector-for-each
     (lambda (cell)
       (hashtable-set! new (car cell)
         (apply
          (lambda (n i j)
            (fxlogor (fxsll n 12) (fxsll i 6) j))
          (cadr cell))))
     (hashtable-cells ht))
    new))

;; immediate table would be 130 Kb
;; convert hashtable to vector of #(key0 val0 key1 val1 ...)
;; sorted so we can binary search for key
(define (compact1 ht)
  (let* ([len (hashtable-size ht)]
         [v (make-vector (* 2 len))]
         [cells
          (vector-sort (lambda (a b) (< (car a) (car b)))
            (hashtable-cells ht))])
    (do ([i 0 (+ i 1)]) ((= i len))
      (let ([j (* i 2)] [cell (vector-ref cells i)])
        (vector-set! v j (car cell))
        (vector-set! v (+ j 1) (cdr cell))))
    v))

;; immediate table would be 133 Kb
;; store the bit patterns together, but shifted over
;;       key -> (lo-13-bits val)
;;   NOT key -> (hi-13-bits val)
(define (compact2 ht)
  (let ([new (make-hashtable values =)])
    (vector-for-each
     (lambda (cell)
       (let* ([key (car cell)]
              [~key (lognot64 key)])
         (assert (hashtable-ref ht ~key #f))
         (cond
          [(hashtable-ref new ~key #f) =>
           (lambda (pr)
             (set-cdr! pr (cdr cell)))]
          [else
           (hashtable-set! new key (cons (cdr cell) #f))])))
     (hashtable-cells ht))
    (vector-for-each
     (lambda (cell)
       (let ([p (cdr cell)])
         (set-cdr! cell (fxlogor (fxsll (cdr p) 13) (car p)))))
     (hashtable-cells new))
    new))

;; immediate table would be 60Kb
(define (compact3 ht)
  (compact1 (compact2 ht)))

;; search is way way way faster than search4, so the 60Kb table may be worth it
(define (search3 v imm)
  (define (lo13 n) (#3%fxlogand n (1- (ash 1 13))))
  (define (hi13 n) (lo13 (#3%fxsrl n 13)))
  (define (seek imm)
    (let go ([lo 0] [hi (#3%vector-length v)])
      (let* ([mid (#3%fx/ (#3%fx+ lo hi) 2)]
             [mid (if (#3%fxeven? mid) mid (#3%fx- mid 1))]
             [val (#3%vector-ref v mid)])
        (cond
         [(#3%< imm val) (and (#3%fx< mid hi) (go lo mid))]
         [(#3%> imm val) (and (#3%fx< lo mid) (go mid hi))]
         [else (#3%vector-ref v (#3%fx+ mid 1))]))))
  (cond
   [(seek imm) => lo13]
   [(seek (lognot64 imm)) => hi13]
   [else #f]))

;; delta compress the keys
;; immediate table would be 42Kb, but would take more work to search
;; because we'd be stuck with linear search
(define (compact4 ht)
  (let* ([v (compact3 ht)] [len (vector-length v)])
    (let lp ([i 0] [prev 0])
      (unless (fx= i len)
        (let ([key (vector-ref v i)])
          (vector-set! v i (- key prev))
          (lp (+ i 2) key))))
    v))

;; very slow for miss, either due to generic = or due to linear search
;; might be able to split up into two tables to handle the 2324 keys that
;; are fixnums separately from the non-fixnums,
;;  e.g., store the 2324 + 2324 negated = 4648 we could get via fixnum compare
;;        where we just know whether to project out the high or low bits [37Kb]
;;        and store the 684 bignum exceptions in a hashtable [22Kb]
(define (search4 v imm)
  (let ([~imm (lognot64 imm)]
        [len (vector-length v)])
    (let lp ([i 0] [key 0])
      (and (#3%fx< i len)
           (let* ([delta (#3%vector-ref v i)]
                  [key (#3%+ key delta)])
             (cond
              [(= key imm)
               (#3%fxlogand (1- (ash 1 13)) (#3%vector-ref v (#3%fx+ i 1)))]
              [(= key ~imm)
               (#3%fxlogand (1- (ash 1 13)) (#3%fxsrl (#3%vector-ref v (#3%fx+ i 1)) 13))]
              [else (lp (#3%fx+ i 2) key)]))))))

(define (find-related ht)
  (let ([rel (make-hashtable values =)])
    (vector-for-each
     (lambda (cell)
       (let ([flipped (hashtable-ref ht (lognot64 (car cell)) #f)])
         (when flipped
           (hashtable-set! rel (car cell)
             (append (cdr cell) (map (lambda (x) (list 'NOT x)) flipped))))))
     (hashtable-cells ht))
    rel))

(printf "To run this, try:

(decode-bit-mask 1 20 13 #t)
(decode-bit-mask 0 3 63 #t)

or

(dump (explore))

or

(define L (generate-lookup (explore)))
(define C1 (compact1 L))
(define C2 (compact2 L))
(define C3 (compact3 L))
(define C4 (compact4 L))

or

(regen) ; to regenerate tmp-lookup-table
")

(define (regen) 
  (with-output-to-file "tmp-lookup-table.ss"
    (lambda ()
      (printf ";; generated by decode-bit-masks.ss\n")
      (pretty-print `(quote ,(compact3 (generate-lookup (explore))))))
    (quote replace)))
