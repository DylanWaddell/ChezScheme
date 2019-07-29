;;; arm64.ss
;;; Copyright 1984-2017 Cisco Systems, Inc.
;;;
;;; Licensed under the Apache License, Version 2.0 (the "License");
;;; you may not use this file except in compliance with the License.
;;; You may obtain a copy of the License at
;;;
;;; http://www.apache.org/licenses/LICENSE-2.0
;;;
;;; Unless required by applicable law or agreed to in writing, software
;;; distributed under the License is distributed on an "AS IS" BASIS,
;;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;;; See the License for the specific language governing permissions and
;;; limitations under the License.


;;; SECTION 1: registers
;;; ABI:
;;;  Register usage:
;;;   r0-r7:   arguments and returns
;;;   r8:      syscalls
;;;   r9-r15:  temporary values, caller save
;;;   r16-r18: (avoid) intra-procedure-call and platform values
;;;   r19-r28: callee save
;;;   r29:     (avoid) frame register
;;;   r30:     (avoid) link register
;;;   r31:     stack pointer or zero register by context
;;;  Floating point:
;;;   v0-v7:   argument
;;;   v8-v15:  callee save
;;;   v16-v31: caller save


(define-registers
  (reserved
    [%tc   %r19                 #t 19]
    [%sfp  %r20                 #t 20]
    [%ap   %r21                 #t 21]
    [%esp  %r22                 #t 22]
    [%eap  %r23                 #t 23]
    [%trap %r24                 #t 24]
    [%ratmp %r9                 #f 9])  ; return address temp. TODO see if reservation of this register can be avoided.
                                        ; currently being used in asm-move to handle large displacements.
                                        ; see asm-helper-jump definition and comment for more details.
  (allocable
    [%ac0  %r25                 #t 25]  ; required order: ac0, xp, ts, td, other ...
    [%xp   %r27                 #t 27]
    [%ts   %r16  %ip0           #f 16]
    [%td   %r17  %ip1           #f 17]
    [%ac1  %r26                 #t 26]
    [%cp   %r28                 #t 28]
    #;[%yp]
    #;[%ret]
    [    %r0  %Carg1 %Cretval   #f  0]
    [    %r1  %Carg2            #f  1]
    [    %r2  %Carg3            #f  2]
    [    %r3  %Carg4            #f  3]
    [    %r4  %Carg5            #f  4]
    [    %r5  %Carg6            #f  5]
    [    %r6  %Carg7            #f  6]
    [    %r7  %Carg8            #f  7]
    [    %lr                    #f 30]
  )


  (machine-dependent
    [%sp                            #t 31]
    ; [%pc                         #f 15]
    [%Cfparg1 %Cfpretval      %v0   #f  0] ; < 32: low bit goes in D, N, or M bit, high bits go in Vd, Vn, Vm
    [%Cfparg2                 %v1   #f  1]
    [%Cfparg3                 %v2   #f  2]
    [%Cfparg4                 %v3   #f  3]
    [%Cfparg5                 %v4   #f  4]
    [%Cfparg6                 %v5   #f  5]
    [%Cfparg7                 %v6   #f  6]
    [%Cfparg8                 %v7   #f  7]
    [%flreg1                  %v16  #f 16]
    [%flreg2                  %v17  #f 17]
    [%zeroreg            %x31 %rsp  #f 31]
    ))

;;; SECTION 2: instructions
(module (md-handle-jump) ; also sets primitive handlers
  (import asm-module)

  (define-syntax seq
    (lambda (x)
      (syntax-case x ()
        [(_ e ... ex)
         (with-syntax ([(t ...) (generate-temporaries #'(e ...))])
           #'(let ([t e] ...)
               (with-values ex
                 (case-lambda
                   [(x*) (cons* t ... x*)]
                   [(x* p) (values (cons* t ... x*) p)]))))])))

  ; don't bother with literal@? check since lvalues can't be literals
  (define lmem? mref?)

  (define mem?
    (lambda (x)
      (or (lmem? x) (literal@? x))))

  (define imm-logical?
    (lambda (x)
      (nanopass-case (L15c Triv) x
        [(immediate ,imm) (and (ax-logical-immediate imm) #t)]
        [else #f])))

  (define imm->logical-imm
    (lambda (x)
      (nanopass-case (L15c Triv) x
        [(immediate ,imm)
         (cond
           [(ax-logical-immediate imm) =>
            (lambda (x)
              (with-output-language (L15d Triv) `(immediate ,x)))]
           [else #f])]
        [else #f])))

  (define imm-arith?
    (lambda (x)
      (nanopass-case (L15c Triv) x
        [(immediate ,imm) (and (fixnum? imm) (#%$fxu< imm #x1000) #t)]
        [else #f])))

  (define imm-shift-count?
    (lambda (x)
      (nanopass-case (L15c Triv) x
        [(immediate ,imm) (shift-count? imm)]
        [else #f])))

  (define imm-unsigned8?
    (lambda (x)
      (nanopass-case (L15c Triv) x
        [(immediate ,imm) (unsigned8? imm)]
        [else #f])))

  (define imm-unsigned12?
    (lambda (x)
      (nanopass-case (L15c Triv) x
        [(immediate ,imm) (unsigned12? imm)]
        [else #f])))

  (define imm-constant?
    (lambda (x)
      (nanopass-case (L15c Triv) x
        [(immediate ,imm) #t]
        [else #f])))

  (define uword8?
    (lambda (imm)
      (and (fixnum? imm) ($fxu< imm (expt 2 10)) (not (fxlogtest imm #b11)))))

  (define imm-uword8?
    ;; immediate is a nonnegative 8-bit word offset
    ;; effectively 8-bit unsigned left-shifted by 2
    (lambda (x)
      (nanopass-case (L15c Triv) x
        [(immediate ,imm) (uword8? imm)]
        [else #f])))


  (define-pass imm->negate-imm : (L15c Triv) (ir) -> (L15d Triv) ()
    (Triv : Triv (ir) -> Triv ()
      [(immediate ,imm) `(immediate ,(- imm))]
      [else (sorry! who "~s is not an immediate" ir)]))

  (define-pass imm->lognot-imm : (L15c Triv) (ir) -> (L15d Triv) ()
    (Triv : Triv (ir) -> Triv ()
      [(immediate ,imm) `(immediate ,(lognot imm))]
      [else (sorry! who "~s is not an immediate" ir)]))

  (define lvalue->ur
    (lambda (x k)
      (if (mref? x)
          (let ([u (make-tmp 'u)])
            (seq
              (set-ur=mref u x)
              (k u)))
          (k x))))

  (define mref->mref
    (lambda (a k)
      (define return
        (lambda (x0 x1 imm)
          ; arm load & store instructions support index or offset but not both
          (safe-assert (or (eq? x1 %zero) (eqv? imm 0)))
          (k (with-output-language (L15d Triv) `(mref ,x0 ,x1 ,imm)))))
      (nanopass-case (L15c Triv) a
        [(mref ,lvalue0 ,lvalue1 ,imm)
         (lvalue->ur lvalue0
           (lambda (x0)
             (lvalue->ur lvalue1
               (lambda (x1)
                 (cond
                   [(and (eq? x1 %zero) (or (unsigned12? imm) (unsigned12? (- imm))))
                    (return x0 %zero imm)]
                   [else
                    (let ([u (make-tmp 'u)])
                      (seq
                        (build-set! ,u (immediate ,imm))
                        (if (eq? x1 %zero)
                            (return x0 u 0)
                            (seq
                              (build-set! ,u (asm ,null-info ,(asm-add #f) ,u ,x1))
                              (return x0 u 0)))))])))))])))

  (define mem->mem
    (lambda (a k)
      (cond
        [(literal@? a)
         (let ([u (make-tmp 'u)])
           (seq
             (build-set! ,u ,(literal@->literal a))
             (k (with-output-language (L15d Lvalue) `(mref ,u ,%zero 0)))))]
        [else (mref->mref a k)])))

  (define-syntax coercible?
    (syntax-rules ()
      [(_ ?a ?aty*)
       (let ([a ?a] [aty* ?aty*])
         (or (memq 'ur aty*)
             (and (memq 'logimm aty*) (imm-logical? a))
             (and (memq 'arithimm aty*) (imm-arith? a))
             (and (memq 'shift-count aty*) (imm-shift-count? a))
             (and (memq 'unsigned8 aty*) (imm-unsigned8? a))
             (and (memq 'unsigned12 aty*) (imm-unsigned12? a))
             (and (memq 'imm-constant aty*) (imm-constant? a))
             (and (memq 'uword8 aty*) (imm-uword8? a))
             (and (memq 'mem aty*) (mem? a))))]))

  (define-syntax coerce-opnd ; passes k something compatible with aty*
    (syntax-rules ()
      [(_ ?a ?aty* ?k)
       (let ([a ?a] [aty* ?aty*] [k ?k])
         (cond
           [(and (memq 'mem aty*) (mem? a)) (mem->mem a k)]
           [(and (memq 'logimm aty*) (imm->logical-imm a)) => k]
           [(and (memq 'arithimm aty*) (imm-arith? a)) (k (imm->imm a))]
           [(and (memq 'shift-count aty*) (imm-shift-count? a)) (k (imm->imm a))]
           [(and (memq 'unsigned8 aty*) (imm-unsigned8? a)) (k (imm->imm a))]
           [(and (memq 'unsigned12 aty*) (imm-unsigned12? a)) (k (imm->imm a))]
           [(and (memq 'imm-constant aty*) (imm-constant? a)) (k (imm->imm a))]
           [(and (memq 'uword8 aty*) (imm-uword8? a)) (k (imm->imm a))]
           [(memq 'ur aty*)
            (cond
              [(ur? a) (k a)]
              [(imm? a)
               (let ([u (make-tmp 'u)])
                 (seq
                   (build-set! ,u ,(imm->imm a))
                   (k u)))]
              [(mem? a)
               (mem->mem a
                 (lambda (a)
                   (let ([u (make-tmp 'u)])
                     (seq
                       (build-set! ,u ,a)
                       (k u)))))]
              [else (sorry! 'coerce-opnd "unexpected operand ~s" a)])]
           [else (sorry! 'coerce-opnd "cannot coerce ~s to ~s" a aty*)]))]))

  (define set-ur=mref
    (lambda (ur mref)
      (mref->mref mref
        (lambda (mref)
          (build-set! ,ur ,mref)))))

  (define md-handle-jump
    (lambda (t)
      (with-output-language (L15d Tail)
        (define long-form
          (lambda (e)
            (let ([tmp (make-tmp 'utmp)])
              (values
                (in-context Effect `(set! ,(make-live-info) ,tmp ,e))
                `(jump ,tmp)))))
        (nanopass-case (L15c Triv) t
          [,lvalue
           (if (mem? lvalue)
               (mem->mem lvalue long-form)
               (long-form (in-context Triv `,lvalue)))]
          [(literal ,info)
           (guard (and (not (info-literal-indirect? info))
                       (memq (info-literal-type info) '(entry library-code))))
           ; NB: really need to use unspillable or mark %ip (aka %ts) killed here but can't without extending jump syntax
           (values '() `(jump (literal ,info)))]
          [(label-ref ,l ,offset)
           (long-form (in-context Triv `(label-ref ,l ,offset)))]
          [else (long-form t)]))))

  (define-syntax define-instruction
    (lambda (x)
      (define make-value-clause
        (lambda (fmt)
          (syntax-case fmt (mem ur)
            [(op (c mem) (a ur))
             #`(lambda (c a)
                 (if (lmem? c)
                     (coerce-opnd a '(ur)
                       (lambda (a)
                         (mem->mem c
                           (lambda (c)
                             (rhs c a)))))
                     (next c a)))]
            [(op (c ur) (a aty ...) ...)
             #`(lambda (c a ...)
                 (if (and (coercible? a '(aty ...)) ...)
                     #,(let f ([a* #'(a ...)] [aty** #'((aty ...) ...)])
                         (if (null? a*)
                             #'(if (ur? c)
                                   (rhs c a ...)
                                   (let ([u (make-tmp 'u)])
                                     (seq
                                       (rhs u a ...)
                                       (mref->mref c
                                         (lambda (c)
                                           (build-set! ,c ,u))))))
                             #`(coerce-opnd #,(car a*) '#,(car aty**)
                                 (lambda (#,(car a*)) #,(f (cdr a*) (cdr aty**))))))
                     (next c a ...)))])))

      (define-who make-pred-clause
        (lambda (fmt)
          (syntax-case fmt ()
            [(op (a aty ...) ...)
             #`(lambda (a ...)
                 (if (and (coercible? a '(aty ...)) ...)
                     #,(let f ([a* #'(a ...)] [aty** #'((aty ...) ...)])
                         (if (null? a*)
                             #'(rhs a ...)
                             #`(coerce-opnd #,(car a*) '#,(car aty**)
                                 (lambda (#,(car a*)) #,(f (cdr a*) (cdr aty**))))))
                     (next a ...)))])))

      (define-who make-effect-clause
        (lambda (fmt)
          (syntax-case fmt ()
            [(op (a aty ...) ...)
             #`(lambda (a ...)
                 (if (and (coercible? a '(aty ...)) ...)
                     #,(let f ([a* #'(a ...)] [aty** #'((aty ...) ...)])
                         (if (null? a*)
                             #'(rhs a ...)
                             #`(coerce-opnd #,(car a*) '#,(car aty**)
                                 (lambda (#,(car a*)) #,(f (cdr a*) (cdr aty**))))))
                     (next a ...)))])))

      (syntax-case x (definitions)
        [(k context (sym ...) (definitions defn ...) [(op (a aty ...) ...) ?rhs0 ?rhs1 ...] ...)
         ; potentially unnecessary level of checking, but the big thing is to make sure
         ; the number of operands expected is the same on every clause of define-intruction
         (and (not (null? #'(op ...)))
              (andmap identifier? #'(sym ...))
              (andmap identifier? #'(op ...))
              (andmap identifier? #'(a ... ...))
              (andmap identifier? #'(aty ... ... ...)))
         (with-implicit (k info return with-output-language)
           (with-syntax ([((opnd* ...) . ignore) #'((a ...) ...)])
             (define make-proc
               (lambda (make-clause)
                 (let f ([op* #'(op ...)]
                         [fmt* #'((op (a aty ...) ...) ...)]
                         [arg* #'((a ...) ...)]
                         [rhs* #'((?rhs0 ?rhs1 ...) ...)])
                   (if (null? op*)
                       #'(lambda (opnd* ...)
                           (sorry! name "no match found for ~s" (list opnd* ...)))
                       #`(let ([next #,(f (cdr op*) (cdr fmt*) (cdr arg*) (cdr rhs*))]
                               [rhs (lambda #,(car arg*)
                                      (let ([#,(car op*) name])
                                        #,@(car rhs*)))])
                           #,(make-clause (car fmt*)))))))
             (unless (let ([a** #'((a ...) ...)])
                       (let* ([a* (car a**)] [len (length a*)])
                         (andmap (lambda (a*) (fx= (length a*) len)) (cdr a**))))
               (syntax-error x "mismatched instruction arities"))
             (cond
               [(free-identifier=? #'context #'value)
                #`(let ([fvalue (lambda (name)
                                  (lambda (info opnd* ...)
                                    defn ...
                                    (with-output-language (L15d Effect)
                                      (#,(make-proc make-value-clause) opnd* ...))))])
                    (begin
                      (safe-assert (eq? (primitive-type (%primitive sym)) 'value))
                      (primitive-handler-set! (%primitive sym) (fvalue 'sym)))
                    ...)]
               [(free-identifier=? #'context #'pred)
                #`(let ([fpred (lambda (name)
                                 (lambda (info opnd* ...)
                                   defn ...
                                   (with-output-language (L15d Pred)
                                     (#,(make-proc make-pred-clause) opnd* ...))))])
                    (begin
                      (safe-assert (eq? (primitive-type (%primitive sym)) 'pred))
                      (primitive-handler-set! (%primitive sym) (fpred 'sym)))
                    ...)]
               [(free-identifier=? #'context #'effect)
                #`(let ([feffect (lambda (name)
                                   (lambda (info opnd* ...)
                                     defn ...
                                     (with-output-language (L15d Effect)
                                       (#,(make-proc make-effect-clause) opnd* ...))))])
                    (begin
                      (safe-assert (eq? (primitive-type (%primitive sym)) 'effect))
                      (primitive-handler-set! (%primitive sym) (feffect 'sym)))
                    ...)]
               [else (syntax-error #'context "unrecognized context")])))]
        [(k context (sym ...) cl ...) #'(k context (sym ...) (definitions) cl ...)]
        [(k context sym cl ...) (identifier? #'sym) #'(k context (sym) (definitions) cl ...)])))

  (define info-cc-eq (make-info-condition-code 'eq? #f #t))
  (define asm-eq (asm-relop info-cc-eq))

  ; x is not the same as z in any clause that follows a clause where (x z)
  ; and y is coercible to one of its types, however:
  ; WARNING: do not assume that if x isn't the same as z then x is independent
  ; of z, since x might be an mref with z as it's base or index


  (define-instruction value (-)
    [(op (z ur) (x ur) (y arithimm))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-sub #f) ,x ,y))]
    [(op (z ur) (x ur) (y ur))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-sub #f) ,x ,y))])

  (define-instruction value (-/ovfl -/eq)
    [(op (z ur) (x ur) (y arithimm))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-sub #t) ,x ,y))]
    [(op (z ur) (x ur) (y ur))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-sub #t) ,x ,y))])

  (define-instruction value (+)
    [(op (z ur) (x ur) (y arithimm))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-add #f) ,x ,y))]
    [(op (z ur) (x arithimm) (y ur))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-add #f) ,y ,x))]
    [(op (z ur) (x ur) (y ur))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-add #f) ,x ,y))])

  (define-instruction value (+/ovfl +/carry)
    [(op (z ur) (x ur) (y arithimm))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-add #t) ,x ,y))]
    [(op (z ur) (x arithimm) (y ur))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-add #t) ,y ,x))]
    [(op (z ur) (x ur) (y ur))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-add #t) ,x ,y))])

  (define-instruction value (*)
    [(op (z ur) (x ur) (y ur)) ; no immediates for arm64
     `(set! ,(make-live-info) ,z (asm ,info ,asm-mul ,x ,y))])

  (define-instruction value (*/ovfl)
    [(op (z ur) (x ur) (y ur))
      (let ([u (make-tmp 'u)])
        (seq
          `(set! ,(make-live-info) ,u (asm ,null-info ,asm-smulh ,x ,y))
          `(set! ,(make-live-info) ,z (asm ,null-info ,asm-mul ,x ,y))
          `(asm ,null-info ,(asm-cmp/shift 63 'sra) ,u ,z)))])

  (define-instruction value (/)
     [(op (z ur) (x ur) (y ur))
     `(set! ,(make-live-info) ,z (asm ,info ,asm-sdiv ,x ,y))])

  (define-instruction value (logand)
    [(op (z ur) (x ur) (y logimm))
     `(set! ,(make-live-info) ,z (asm ,info ,asm-logand ,x ,y))]
    [(op (z ur) (x logimm) (y ur))
     `(set! ,(make-live-info) ,z (asm ,info ,asm-logand ,y ,x))]
    [(op (z ur) (x ur) (y ur))
     `(set! ,(make-live-info) ,z (asm ,info ,asm-logand ,x ,y))])

  (let ()
    (define select-op (lambda (op) (if (eq? op 'logor) asm-logor asm-logxor)))
    (define-instruction value (logor logxor)
      [(op (z ur) (x logimm) (y ur))
       `(set! ,(make-live-info) ,z (asm ,info ,(select-op op) ,y ,x))]
      [(op (z ur) (x ur) (y logimm ur))
       `(set! ,(make-live-info) ,z (asm ,info ,(select-op op) ,x ,y))]))

  (define-instruction value (lognot)
    [(op (z ur) (x ur))
     `(set! ,(make-live-info) ,z (asm ,info ,asm-lognot ,x))])

  (define-instruction value (sll srl sra)
    [(op (z ur) (x ur) (y ur shift-count))
     `(set! ,(make-live-info) ,z (asm ,info ,(asm-shiftop op) ,x ,y))])

  (define-instruction value (move)
    [(op (z mem) (x ur))
     `(set! ,(make-live-info) ,z ,x)]
    [(op (z ur) (x ur mem imm))
     `(set! ,(make-live-info) ,z ,x)])

  (define-instruction value lea1
    ; NB: would be simpler if offset were explicit operand
    ; NB: why not one version of lea with %zero for y in lea1 case?
    [(op (z ur) (x ur))
     (begin
       (let ([offset (info-lea-offset info)] [u (make-tmp 'u)])
         (seq
           `(set! ,(make-live-info) ,u (immediate ,offset))
           `(set! ,(make-live-info) ,z (asm ,info ,(asm-add #f) ,x ,u)))))])

  (define-instruction value lea2
    ; NB: would be simpler if offset were explicit operand
    [(op (z ur) (x ur) (y ur))
     (let ([offset (info-lea-offset info)] [u (make-tmp 'u)])
       (seq
         `(set! ,(make-live-info) ,u (immediate ,offset))
         `(set! ,(make-live-info) ,u (asm ,null-info ,(asm-add #f) ,u ,y))
         `(set! ,(make-live-info) ,z (asm ,info ,(asm-add #f) ,x ,u))))])

  (define-instruction value (sext8 sext16 sext32 zext8 zext16 zext32)
    [(op (z ur) (x ur)) `(set! ,(make-live-info) ,z (asm ,info ,(asm-move/extend op) ,x))])

  (let ()
    (define imm-zero (with-output-language (L15d Triv) `(immediate 0)))
    (define load/store
      (lambda (x y w imm8? k) ; x ur, y ur, w ur or imm
        (with-output-language (L15d Effect)
          (if (ur? w)
              (if (eq? y %zero)
                  (k x w imm-zero)
                  (let ([u (make-tmp 'u)])
                    (seq
                      `(set! ,(make-live-info) ,u (asm ,null-info ,(asm-add #f) ,y ,w))
                      (k x u imm-zero))))
              (let ([n (nanopass-case (L15d Triv) w [(immediate ,imm) imm])])
                (cond
                  [(if imm8?
                       (or (unsigned8? n) (unsigned8? (- n)))
                       (or (unsigned12? n) (unsigned12? (- n))))
                   (let ([w (in-context Triv `(immediate ,n))])
                     (if (or (eq? y %zero) (fx= n 0))
                         (k x y w)
                         (let ([u (make-tmp 'u)])
                           (seq
                             `(set! ,(make-live-info) ,u (asm ,null-info ,(asm-add #f) ,x ,y))
                             (k u %zero w)))))]
                  [else
                   (let ([u (make-tmp 'u)])
                     (seq
                       `(set! ,(make-live-info) ,u (immediate ,n))
                       (if (eq? y %zero)
                           (k x u imm-zero)
                           (seq
                             `(set! ,(make-live-info) ,u (asm ,null-info ,(asm-add #f) ,x ,u))
                             (k u y imm-zero)))))]))))))

    (define-instruction value (load)
      [(op (z ur) (x ur) (y ur) (w ur imm-constant))
       (let ([type (info-load-type info)])
         (load/store x y w (memq type '(integer-16 unsigned-16 integer-8))
           (lambda (x y w)
             (let ([instr `(set! ,(make-live-info) ,z (asm ,null-info ,(asm-load type) ,x ,y ,w))])
               (if (info-load-swapped? info)
                   (seq
                     instr
                     `(set! ,(make-live-info) ,z (asm ,null-info ,(asm-swap type) ,z)))
                   instr)))))])

    (define-instruction effect (store)
      [(op (x ur) (y ur) (w ur imm-constant) (z ur))
       (let ([type (info-load-type info)])
         (load/store x y w (memq type '(integer-16 unsigned-16))
           (lambda (x y w)
             (if (info-load-swapped? info)
                 (let ([u (make-tmp 'unique-bob)])
                   (seq
                     `(set! ,(make-live-info) ,u (asm ,null-info ,(asm-swap type) ,z))
                     `(asm ,null-info ,(asm-store type) ,x ,y ,w ,u)))
                 `(asm ,null-info ,(asm-store type) ,x ,y ,w ,z)))))]))

  (let ()
    (define pick-asm-op
      (lambda (op info)
        (let ([flreg (info-loadfl-flreg info)])
          (case op
            [(load-single->double load-double->single) (asm-fl-load/cvt op flreg)]
            [(store-single->double) (asm-fl-store/cvt op flreg)]
            [else (asm-fl-load/store op flreg)]))))
    (define-instruction effect (load-single->double load-double->single store-single->double
                                 store-single store-double
                                 load-single load-double)
      [(op (x ur) (y ur) (z uword8))
       (if (eq? y %zero)
           `(asm ,info ,(pick-asm-op op info) ,x ,z)
           (let ([u (make-tmp 'u)])
             (seq
               `(set! ,(make-live-info) ,u (asm ,info ,(asm-add #f) ,x ,y))
               `(asm ,info ,(pick-asm-op op info) ,u ,z))))]
      [(op (x ur) (y ur) (z ur))
       (let ([u (make-tmp 'u)])
         (seq
           `(set! ,(make-live-info) ,u (asm ,info ,(asm-add #f) ,x ,z))
           (if (eq? y %zero)
               `(asm ,info ,(pick-asm-op op info) ,u (immediate 0))
               (seq
                 `(set! ,(make-live-info) ,u (asm ,info ,(asm-add #f) ,u ,y))
                 `(asm ,info ,(pick-asm-op op info) ,u (immediate 0))))))]))

  (let ()
    ; vldr, vstr allow only word offsets, and we require byte offset due to the type tag
    (module (with-flonum-data-pointers)
      (define $flonum-data-pointer
        (lambda (x p)
          (with-output-language (L15d Effect)
            (let ([u (make-tmp 'u)])
              (seq
                `(set! ,(make-live-info) ,u (asm ,null-info ,(asm-add #f) ,x (immediate ,(constant flonum-data-disp))))
                (p u))))))
      (define-syntax with-flonum-data-pointers
        (syntax-rules ()
          [(_ () e1 e2 ...) (begin e1 e2 ...)]
          [(_ (x1 x2 ...) e1 e2 ...)
           ($flonum-data-pointer x1
             (lambda (x1)
               (with-flonum-data-pointers (x2 ...) e1 e2 ...)))])))

    (define-instruction effect (flt)
      [(op (x ur) (y ur))
       (with-flonum-data-pointers (y)
         `(asm ,info ,asm-flt ,x ,y))])

    (define-instruction effect (fl+ fl- fl/ fl*)
      [(op (x ur) (y ur) (z ur))
       (with-flonum-data-pointers (x y z)
         `(asm ,info ,(asm-flop-2 op) ,x ,y ,z))])

    (define-instruction effect (flsqrt)
      [(op (x ur) (y ur))
       (with-flonum-data-pointers (x y)
         `(asm ,info ,asm-flsqrt ,x ,y))])

    (define-instruction value (trunc)
      [(op (z ur) (x ur))
       (with-flonum-data-pointers (x)
         `(set! ,(make-live-info) ,z (asm ,info ,asm-trunc ,x)))])

    (define-instruction pred (fl= fl< fl<=)
      [(op (x ur) (y ur))
       (with-flonum-data-pointers (x y)
         (let ([info (make-info-condition-code op #f #f)])
           (values '() `(asm ,info ,(asm-fl-relop info) ,x ,y))))]))

  (define-instruction effect (inc-cc-counter)
    [(op (x ur) (w ur) (z ur))
     (let ([u1 (make-tmp 'u1)] [u2 (make-tmp 'u2)])
       (seq
         `(set! ,(make-live-info) ,u1 (asm ,null-info ,(asm-add #f) ,x ,w))
         `(set! ,(make-live-info) ,u2 (asm ,null-info ,asm-kill))
         `(asm ,null-info ,asm-inc-cc-counter ,u1 ,z ,u2)))])

  (define-instruction effect (inc-profile-counter)
    [(op (x mem) (y ur))
     (let ([u (make-tmp 'u)])
       (seq
         `(set! ,(make-live-info) ,u ,x)
         `(set! ,(make-live-info) ,u (asm ,null-info ,(asm-add #f) ,u ,y))
         `(set! ,(make-live-info) ,x ,u)))])

  (define-instruction value (read-time-stamp-counter)
    [(op (z ur)) `(set! ,(make-live-info) ,z (asm ,null-info ,(asm-read-counter 1)))])

  (define-instruction value (read-performance-monitoring-counter)
    [(op (z ur) (x unsigned8))
     ; could require unsigned1 and skip the fxmin...but no point burdening instruction scheduler with an additional one-off type
     (let ([imm (nanopass-case (L15d Triv) x [(immediate ,imm) (fxmin imm 1)])])
       `(set! ,(make-live-info) ,z (asm ,null-info ,(asm-read-counter (fx+ imm 2)))))]
    [(op (z ur) (x ur)) `(set! ,(make-live-info) ,z (asm ,null-info ,(asm-read-counter) ,x))])

  ;; no kills since we expect to be called when all necessary state has already been saved
  (define-instruction value (get-tc)
    [(op (z ur))
     (safe-assert (eq? z %Cretval))
     (let ([u (make-tmp 'u)] [ulr (make-precolored-unspillable 'ulr %lr)])
       (seq
         `(set! ,(make-live-info) ,u (asm ,null-info ,asm-kill))
         `(set! ,(make-live-info) ,ulr (asm ,null-info ,asm-kill))
         `(set! ,(make-live-info) ,z (asm ,info ,asm-get-tc ,u ,ulr))))])

  (define-instruction value (asmlibcall)
    [(op (z ur))
     (let ([u (make-tmp 'u)])
       (if (info-asmlib-save-ra? info)
           (seq
             `(set! ,(make-live-info) ,u (asm ,null-info ,asm-kill))
             `(set! ,(make-live-info) ,z (asm ,info ,(asm-library-call (info-asmlib-libspec info) #t) ,u ,(info-kill*-live*-live* info) ...)))
           (let ([ulr (make-precolored-unspillable 'ulr %lr)])
             (seq
               `(set! ,(make-live-info) ,u (asm ,null-info ,asm-kill))
               `(set! ,(make-live-info) ,ulr (asm ,null-info ,asm-kill))
               `(set! ,(make-live-info) ,z (asm ,info ,(asm-library-call (info-asmlib-libspec info) #f) ,u ,ulr ,(info-kill*-live*-live* info) ...))))))])

  (define-instruction effect (asmlibcall!)
    [(op)
     (let ([u (make-tmp 'u)])
       (if (info-asmlib-save-ra? info)
           (let ([ulr (make-precolored-unspillable 'ulr %lr)])
             (seq
               `(set! ,(make-live-info) ,u (asm ,null-info ,asm-kill))
               `(asm ,info ,(asm-library-call! (info-asmlib-libspec info) #t) ,u ,(info-kill*-live*-live* info) ...)))
           (let ([ulr (make-precolored-unspillable 'ulr %lr)])
             (seq
               `(set! ,(make-live-info) ,u (asm ,null-info ,asm-kill))
               `(set! ,(make-live-info) ,ulr (asm ,null-info ,asm-kill))
               `(asm ,info ,(asm-library-call! (info-asmlib-libspec info) #f) ,u ,ulr ,(info-kill*-live*-live* info) ...)))))])

  (safe-assert (reg-callee-save? %tc)) ; no need to save-restore
  (define-instruction effect (c-simple-call)
    [(op)
     (let ([u (make-tmp 'u)])
       (if (info-c-simple-call-save-ra? info)
           (seq
             `(set! ,(make-live-info) ,u (asm ,null-info ,asm-kill))
             `(asm ,info ,(asm-c-simple-call (info-c-simple-call-entry info) #t) ,u))
           (let ([ulr (make-precolored-unspillable 'ulr %lr)])
             (seq
               `(set! ,(make-live-info) ,u (asm ,null-info ,asm-kill))
               `(set! ,(make-live-info) ,ulr (asm ,null-info ,asm-kill))
               `(asm ,info ,(asm-c-simple-call (info-c-simple-call-entry info) #f) ,u ,ulr)))))])

  (define-instruction pred (eq? u< < > <= >=)
    [(op (x ur) (y ur))
     (let ([info (if (eq? op 'eq?) info-cc-eq (make-info-condition-code op #f #t))])
       (values '() `(asm ,info ,(asm-relop info) ,x ,y)))])

  (define-instruction pred (condition-code)
    [(op) (values '() `(asm ,info ,(asm-condition-code info)))])

  (define-instruction pred (type-check?)
    [(op (x ur) (mask ur) (type ur))
     (let ([tmp (make-tmp 'u)])
       (values
         (with-output-language (L15d Effect)
           `(set! ,(make-live-info) ,tmp (asm ,null-info ,asm-logand ,x ,mask)))
         `(asm ,info-cc-eq ,asm-eq ,tmp ,type)))])

  (define-instruction pred (logtest log!test)
    [(op (x logimm) (y ur))
     (values '() `(asm ,info-cc-eq ,(asm-logtest (eq? op 'log!test) info-cc-eq) ,y ,x))]
    [(op (x ur) (y ur logimm))
     (values '() `(asm ,info-cc-eq ,(asm-logtest (eq? op 'log!test) info-cc-eq) ,x ,y))])

  (let ()
    (define lea->reg
      (lambda (x y w k)
        (with-output-language (L15d Effect)
          (define add-offset
            (lambda (r)
              (if (eqv? (nanopass-case (L15d Triv) w [(immediate ,imm) imm]) 0)
                  (k r)
                  (let ([u (make-tmp 'u)])
                    (seq
                      `(set! ,(make-live-info) ,u (asm ,null-info ,(asm-add #f) ,r ,w))
                      (k u))))))
          (if (eq? y %zero)
              (add-offset x)
              (let ([u (make-tmp 'u)])
                (seq
                  `(set! ,(make-live-info) ,u (asm ,null-info ,(asm-add #f) ,x ,y))
                  (add-offset u)))))))
    ; NB: compiler ipmlements init-lock! and unlock! as 32-bit store of zero
    (define-instruction pred (lock!)
      [(op (x ur) (y ur) (w unsigned12))
       (let ([u (make-tmp 'u)])
         (values
           (lea->reg x y w
             (lambda (r)
               (with-output-language (L15d Effect)
                 (seq
                   `(set! ,(make-live-info) ,u (asm ,null-info ,asm-kill))
                   `(asm ,null-info ,asm-lock ,r ,u)))))
           `(asm ,info-cc-eq ,asm-eq ,u (immediate 0))))])
    (define-instruction effect (locked-incr! locked-decr!)
      [(op (x ur) (y ur) (w unsigned12))
       (lea->reg x y w
         (lambda (r)
           (let ([u1 (make-tmp 'u1)] [u2 (make-tmp 'u2)])
             (seq
               `(set! ,(make-live-info) ,u1 (asm ,null-info ,asm-kill))
               `(set! ,(make-live-info) ,u2 (asm ,null-info ,asm-kill))
               `(asm ,null-info ,(asm-lock+/- op) ,r ,u1 ,u2)))))])
    (define-instruction effect (cas)
      [(op (x ur) (y ur) (w unsigned12) (old ur) (new ur))
       (lea->reg x y w
         (lambda (r)
           (let ([u1 (make-tmp 'u1)] [u2 (make-tmp 'u2)])
             (seq
               `(set! ,(make-live-info) ,u1 (asm ,null-info ,asm-kill))
               `(set! ,(make-live-info) ,u2 (asm ,null-info ,asm-kill))
               `(asm ,info ,asm-cas ,r ,old ,new ,u1 ,u2)))))]))

  (define-instruction effect (pause)
    ; NB: user sqrt or something like that?
    [(op) '()])

  (define-instruction effect (c-call)
    [(op (x ur))
     (let ([ulr (make-precolored-unspillable 'ulr %lr)])
       (seq
         `(set! ,(make-live-info) ,ulr (asm ,null-info ,asm-kill))
         `(asm ,info ,asm-indirect-call ,x ,ulr ,(info-kill*-live*-live* info) ...)))])

  (define-instruction effect (pop-multiple)
    [(op) `(asm ,info ,(asm-pop-multiple (info-kill*-kill* info)))])

  (define-instruction effect (push-multiple)
    [(op) `(asm ,info ,(asm-push-multiple (info-kill*-live*-live* info)))])

  (define-instruction effect (vpush-multiple)
    [(op) `(asm ,info ,(asm-vpush-multiple (info-vpush-reg info) (info-vpush-n info)))])

  (define-instruction effect save-flrv
    [(op) `(asm ,info ,asm-save-flrv)])

  (define-instruction effect restore-flrv
    [(op) `(asm ,info ,asm-restore-flrv)])

  (define-instruction effect (invoke-prelude)
    [(op) `(set! ,(make-live-info) ,%tc ,%Carg1)])
)

;;; SECTION 3: assembler
(module asm-module (; required exports

                     asm-cmpi asm-smulh asm-sdiv asm-udiv
                     ax-logical-immediate

                     asm-move asm-move/extend asm-load asm-store asm-swap asm-library-call asm-library-call! asm-library-jump
                     asm-mul asm-smull asm-cmp/shift asm-add asm-sub asm-logand asm-logor asm-logxor
                     asm-pop-multiple asm-shiftop asm-logand asm-lognot
                     asm-logtest asm-fl-relop asm-relop asm-push-multiple asm-vpush-multiple
                     asm-indirect-jump asm-literal-jump
                     asm-direct-jump asm-return-address asm-jump asm-conditional-jump asm-data-label asm-rp-header
                     asm-indirect-call asm-condition-code
                     asm-fl-load/store
                     asm-fl-load/cvt asm-fl-store/cvt asm-flt asm-trunc
                     asm-lock asm-lock+/- asm-cas
                     asm-flop-2 asm-flsqrt asm-c-simple-call
                     asm-save-flrv asm-restore-flrv asm-return asm-c-return asm-size
                     asm-enter asm-foreign-call asm-foreign-callable
                     asm-read-counter
                     asm-inc-cc-counter
                     shift-count? unsigned8? unsigned12?
                     ; threaded version specific
                     asm-get-tc
                     ; machine dependent exports
                     asm-kill
                     info-vpush-reg info-vpush-n)


  ; handles imm13 n:imms:immr to n:immr:imms conversion
  (define ax-logical-immediate
    (lambda (imm)
      ;; TODO Until the project includes arm64le.boot as a first-class citizen,
      ;;      folks will have to cross-compile from another architecture. Rather
      ;;      than add this file to the source target of Mf-base, fish it out of
      ;;      the real s directory. May want to handle logical immediates
      ;;      differently anyway.
      (define C3 (include "../../s/arm64-lookup-table.ss"))
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
        (define (lognot64 x) (bitwise-xor (1- (ash 1 64)) x))
        (cond
         [(seek imm) => lo13]
         [(seek (lognot64 imm)) => hi13]
         [else #f]))
     (search3 C3 imm)))

  (define-record-type info-vpush (nongenerative)
    (parent info)
    (sealed #t)
    (fields reg n))

  (define ax-register?
    (case-lambda
      [(x) (record-case x [(reg) r #t] [else #f])]
      [(x reg) (record-case x [(reg) r (eq? r reg)] [else #f])]))

  (define-who ax-ea-reg-code
    (lambda (ea)
      (record-case ea
        [(reg) r (reg-mdinfo r)]
        [else (sorry! who "ea=~s" ea)])))

  (define ax-register-list
    (lambda (r*)
      (fold-left
        (lambda (a r) (fx+ a (fxsll 1 (reg-mdinfo r))))
        0 r*)))

  (define ax-reg?
    (lambda (ea)
      (record-case ea
        [(reg) ignore #t]
        [else #f])))

  (define ax-imm?
    (lambda (ea)
      (record-case ea
        [(imm) ignore #t]
        [else #f])))

  (define-who ax-imm-data
    (lambda (ea)
      (record-case ea
        [(imm) (n) n]
        [else (sorry! who "ax-imm-data ea=~s" ea)])))


  ; define-op sets up assembly op macros--
  ; the opcode and all other expressions are passed to the specified handler--
  (define-syntax define-op
    (lambda (x)
      (syntax-case x ()
        [(k op handler e ...)
         (with-syntax ([op (construct-name #'k "asmop-" #'op)])
           #'(define-syntax op
               (syntax-rules ()
                 [(_ mneu arg (... ...))
                  (handler 'mneu e ... arg (... ...))])))])))

  (define-syntax emit
    (lambda (x)
      (syntax-case x ()
        [(k op x ...)
         (with-syntax ([emit-op (construct-name #'k "asmop-" #'op)])
           #'(emit-op op x ...))])))

  ;;; note that the assembler isn't clever--you must be very explicit about
  ;;; which flavor you want, and there are a few new varieties introduced
  ;;; (commented-out opcodes are not currently used by the assembler--
  ;;; spaces are left to indicate possible size extensions)

  (define move-immediate
    (lambda (n)
      (define cons-bits
        (lambda (shift ls)
          (let ([bits (bitwise-bit-field n shift (+ shift 16))])
            (if (zero? bits)
                ls
                (cons (cons (/ shift 16) bits) ls)))))
      (cond
        [(zero? n) '((0 . 0))]
        [(> n (- (ash 1 64) 1)) '()]
        [else
          (cons-bits 48
            (cons-bits 32
              (cons-bits 16
                (cons-bits 0 '()))))])))

  (define-syntax dynamic-reference
    (syntax-rules ()
      [(_ unscaled unsigned register register-shifted)
        (lambda (src/dest breg n code*)
          (define (bad!) (sorry! "dynamic load/store error with src/dest ~s and breg ~s" src/dest breg))
          (define-syntax make-emit
            (syntax-rules ()
              [(_ op)
               (lambda (src/dest breg ireg code*)
                 (emit op src/dest breg ireg code*))]))
          (define dynamic-helper
            (lambda (emit-op n src/dest breg code*)
              (let ([code* (emit-op src/dest `(reg . ,breg) `(reg . ,%ratmp) code*)])
                   (if (> n 0)
                       (emit movi `(reg . ,%ratmp) n code*)
                       (emit movn `(reg . ,%ratmp) (lognot n) 0 code*)))))
          (cond
            [(signed9? n)
              (emit unscaled src/dest `(reg . ,breg) n code*)]
            [(and (fx= (fxlogand n 7) 0) (unsigned12? (fx/ n 8)))
              (emit unsigned src/dest `(reg . ,breg) (fx/ n 8) code*)]
            [(and (fx= (fxlogand n 7) 0) (imm16? (fx/ n 8)))
              (dynamic-helper (make-emit register-shifted) (fx/ n 8) src/dest breg code*)]
            [(imm16? n)
              (dynamic-helper (make-emit register) n src/dest breg code*)]
            [else (bad!)]))]))

  (define ldri-dynamic  (dynamic-reference ldur ldri ldr ldrs))
  (define stri-dynamic  (dynamic-reference stur stri str strs))

  (define fldri-dynamic.dbl (dynamic-reference fldur.dbl fldri.dbl fldr.dbl fldrs.dbl))
  (define fstri-dynamic.dbl (dynamic-reference fstur.dbl fstri.dbl fstr.dbl fstrs.dbl))

  (define fldri-dynamic.sgl (dynamic-reference fldur.sgl fldri.sgl fldr.sgl fldrs.sgl))
  (define fstri-dynamic.sgl (dynamic-reference fstur.sgl fstri.sgl fstr.sgl fstrs.sgl))


  ; move immidiate
  (define-op movi/k
    (lambda (mneu dest-ea imm16 shift16 keep code*)
      (emit-code ((if keep 'movk 'movi) dest-ea imm16 shift16 code*)
        [31 1]
        [30 1]
        [29 (if keep 1 0)]
        [23 #b100101]
        [21 shift16]  ; 00: 0, 01: 16, 10: 32, 11: 48
        [5 (fxlogand #xffff imm16)]
        [0 (ax-ea-reg-code dest-ea)])))

  (define-op movi
    (lambda (mneu dest-ea imm16 code*)
      (emit movi/k dest-ea imm16 0 #f code*)))

  (define-op movn
    (lambda (mneu dest-ea imm16 shift16 code*)
      (emit-code ('movn dest-ea imm16 shift16 code*)
        [31 #b1]
        [29 #b00]
        [23 #b100101]
        [21 shift16] ; 00: 0, 01: 16, 10: 32, 11: 48
        [5 (fxlogand #xffff imm16)]
        [0 (ax-ea-reg-code dest-ea)])))

  ; binary immediate ops

  (define binary-op
    (lambda (mneu opcode op set-cc? dest-ea opnd0-ea opnd1-ea code*)
      (emit-code (mneu dest-ea opnd0-ea opnd1-ea code*)
        [31 1]
        [30 op]
        [29 (if set-cc? #b1 #b0)]
        [24 opcode]
        [22 #b00]                       ; shift type
        [21 0]
        [16 (ax-ea-reg-code opnd1-ea)]
        [10 #b00000]                    ; shift amount (0 - 63)
        [5 (ax-ea-reg-code opnd0-ea)]
        [0 (ax-ea-reg-code dest-ea)])))

  (define binary-imm-op
    (lambda (mneu opcode op shift12 set-cc? dest-ea opnd-ea imm12 code*)
      (emit-code (mneu dest-ea opnd-ea imm12 code*)
        [31 1]
        [30 op]
        [29 (if set-cc? #b1 #b0)]
        [24 opcode]
        [23 0]
        [22 shift12] ; 0: no shift, 1: shift left 12
        [10 (fxlogand #xfff imm12)]
        [5 (ax-ea-reg-code opnd-ea)]
        [0 (ax-ea-reg-code dest-ea)])))

  (define binary-log-op
    (lambda (mneu opcode dest-ea opnd0-ea opnd1-ea code*)
      (emit-code (mneu dest-ea opnd0-ea opnd1-ea code*)
        [31 1]
        [24 opcode]
        [22 #b00] ; 0: no shift, 1: shift left 12
        [21 0]
        [16 (ax-ea-reg-code opnd1-ea)]
        [10 #b000000]
        [5 (ax-ea-reg-code opnd0-ea)]
        [0 (ax-ea-reg-code dest-ea)])))

  ; immediate masks (binary immediate ops)
  (define-op tsti imm-tst-mask-op #b11)
  (define-op andi imm-mask-op #b00)
  (define-op orri imm-mask-op #b01)
  (define-op eori imm-mask-op #b10)

  ; binary ops
  (define-op addi binary-imm-op #b10001 #b0 #b0)
  (define-op subi binary-imm-op #b10001 #b1 #b0)
  (define-op add  binary-op #b01011 #b0)
  (define-op sub  binary-op #b01011 #b1)

  (define-op and  binary-log-op #b0001010)
  (define-op orr  binary-log-op #b0101010)
  (define-op eor  binary-log-op #b1001010)

  ; cmp ops
  (define-op cmp cmp-op)

  (define-op tst
    (lambda (mneu dest-ea opnd-ea code*)
       (emit-code (mneu dest-ea opnd-ea code*)
         [31 1]
         [29 #b11]
         [24 #b01010]
         [22 #b00]                       ; shift type
         [21 0]
         [16 (ax-ea-reg-code opnd-ea)]
         [10 #b000000]                   ; shift (0 - 63)
         [5 (ax-ea-reg-code dest-ea)]
         [0 #b11111])))

  (define-op cmp/shift
    (lambda (mneu imm6 shift-type opnd0-ea opnd1-ea code*)
      (emit-code (mneu opnd0-ea opnd1-ea shift-type imm6 code*)
        [31 1]
        [30 1]
        [29 1]
        [24 #b01011]
        [22 (case shift-type
              [(sll) #b00]
              [(lsr) #b01]
              [(sra) #b10]
              [else (errorf 'shift-op "bad shift type ~s" shift-type)])]
        [21 0]
        [16 (ax-ea-reg-code opnd1-ea)]
        [10 (fxlogand #x3f imm6)]
        [5 (ax-ea-reg-code opnd0-ea)]
        [0 #b11111])))

  (define-op cmpi
    (lambda (mneu opnd-ea imm12 code*)
      (emit-code (mneu opnd-ea imm12 code*)
        [31 1]
        [30 1]
        [29 1]
        [24 #b10001]
        [22 #b00]
        [10 (fxlogand #xfff imm12)]
        [5 (ax-ea-reg-code opnd-ea)]
        [0 #b11111])))

  ; unary ops
  (define-op mov move-op #b0)
  (define-op mvn move-op #b1)

  (define move-op
    (lambda (mneu negate? dest-ea opnd-ea code*)
      (emit-code (mneu dest-ea opnd-ea code*)
        [31 1]
        [29 #b01]
        [24 #b01010]
        [22 #b00]    ; shift type
        [21 negate?]
        [16 (ax-ea-reg-code opnd-ea)]
        [10 #b000000]
        [5 #b11111]  ; shift value
        [0 (ax-ea-reg-code dest-ea)])))

  (define-op shifti shifti-op)
  (define-op shift shift-op)

  (define-op sxtb sx-op #b00 #b1 #b000111)
  (define-op sxth sx-op #b00 #b1 #b001111)
  (define-op sxtw sx-op #b00 #b1 #b011111)
  (define-op uxtb sx-op #b10 #b0 #b000111)
  (define-op uxth sx-op #b10 #b0 #b001111)

  (define-op uxtw
    (lambda (mneu dest-ea opnd-ea code*)
      (emit-code (mneu dest-ea opnd-ea code*)
        [31 1]
        [29 #b00]
        [24 #b01011]
        [21 #b001]
        [16 (ax-ea-reg-code opnd-ea)]
        [13 #b010]
        [10 #b000]
        [5 #b11111]
        [0 (ax-ea-reg-code dest-ea)])))

  (define sx-op
    (lambda (mneu opc N imms dest-ea opnd-ea code*)
      (emit-code (mneu dest-ea opnd-ea code*)
        [31 1]
        [29 opc]
        [23 #b100110]
        [22 N]        ; signed
        [16 #b000000]
        [10 imms]     ; data type
        [5 (ax-ea-reg-code opnd-ea)]
        [0 (ax-ea-reg-code dest-ea)])))

  (define-op mul   multiply-op #b000)
  (define-op smull multiply-op #b101)
  (define-op smulh multiply-op #b010)

  (define multiply-op
    (lambda (mneu flags dest-ea opnd0-ea opnd1-ea code*)
      (emit-code (mneu dest-ea opnd0-ea opnd1-ea code*)
        [31 1]
        [29 #b00]
        [24 #b11011]
        [21 flags]
        [16 (ax-ea-reg-code opnd1-ea)]
        [15 0]
        [10 #b11111]
        [5 (ax-ea-reg-code opnd0-ea)]
        [0 (ax-ea-reg-code dest-ea)])))

  (define-op sdiv division-op #b1)
  (define-op udiv division-op #b0)

  (define division-op
    (lambda (mneu signed? dest-ea opnd0-ea opnd1-ea code*)
      (emit-code (mneu dest-ea opnd0-ea opnd1-ea code*)
        [31 1]
        [29 #b00]
        [21 #b11010110]
        [16 (ax-ea-reg-code opnd1-ea)]
        [11 #b00001]
        [10 signed?]
        [5 (ax-ea-reg-code opnd0-ea)]
        [0 (ax-ea-reg-code dest-ea)])))


  ; 64 bit (extended)
  (define-op ldri   ldr/str-imm-op       #b11 #b01)
  (define-op stri   ldr/str-imm-op       #b11 #b00)
  (define-op ldur   ldur/stur-imm-op     #b11 #b01)
  (define-op stur   ldur/stur-imm-op     #b11 #b00)

  (define-op ldr    ldr/str-reg-op       #b11 #b01 #b111 #b0)
  (define-op ldrs   ldr/str-reg-op       #b11 #b01 #b111 #b1)
  (define-op str    ldr/str-reg-op       #b11 #b00 #b111 #b0)
  (define-op strs   ldr/str-reg-op       #b11 #b00 #b111 #b1)

  ; 64 bit (double)
  (define-op fldri.dbl  ldr/str-fl-imm-op     #b11 #b01)
  (define-op fstri.dbl  ldr/str-fl-imm-op     #b11 #b00)
  (define-op fldur.dbl  ldur/stur-fl-imm-op   #b11 #b01)
  (define-op fstur.dbl  ldur/stur-fl-imm-op   #b11 #b00)

  (define-op fldr.dbl   ldr/str-fl-reg-op     #b11 #b01 #b111 #b0)
  (define-op fldrs.dbl  ldr/str-fl-reg-op     #b11 #b01 #b111 #b1)
  (define-op fstr.dbl   ldr/str-fl-reg-op     #b11 #b00 #b111 #b0)
  (define-op fstrs.dbl  ldr/str-fl-reg-op     #b11 #b00 #b111 #b1)

  ; 32 bit (word)
  (define-op ldrw    ldr/str-reg-op      #b10 #b01 #b111 #b0)
  (define-op ldrsw   ldr/str-reg-op      #b10 #b10 #b111 #b0)
  (define-op strw    ldr/str-reg-op      #b10 #b00 #b111 #b0)

  (define-op ldurw   ldur/stur-imm-op    #b10 #b01)
  (define-op ldursw  ldur/stur-imm-op    #b10 #b10)
  (define-op sturw   ldur/stur-imm-op    #b10 #b00)

  ; 32 bit (single)
  (define-op fldri.sgl  ldr/str-fl-imm-op     #b10 #b01)
  (define-op fstri.sgl  ldr/str-fl-imm-op     #b10 #b00)
  (define-op fldur.sgl  ldur/stur-fl-imm-op   #b10 #b01)
  (define-op fstur.sgl  ldur/stur-fl-imm-op   #b10 #b00)

  (define-op fldr.sgl   ldr/str-fl-reg-op     #b10 #b01 #b111 #b0)
  (define-op fldrs.sgl  ldr/str-fl-reg-op     #b10 #b01 #b111 #b1)
  (define-op fstr.sgl   ldr/str-fl-reg-op     #b10 #b00 #b111 #b0)
  (define-op fstrs.sgl  ldr/str-fl-reg-op     #b10 #b00 #b111 #b1)

  ; 16 bit (half-word)
  (define-op ldrh    ldr/str-reg-op      #b01 #b01 #b111 #b0)
  (define-op ldrsh   ldr/str-reg-op      #b01 #b10 #b111 #b0)
  (define-op strh    ldr/str-reg-op      #b01 #b00 #b111 #b0)

  (define-op ldurh   ldur/stur-imm-op    #b01 #b01)
  (define-op ldursh  ldur/stur-imm-op    #b01 #b10)
  (define-op sturh   ldur/stur-imm-op    #b01 #b00)

  ; 8 bit (byte)
  (define-op ldrb    ldr/str-reg-op      #b00 #b01 #b111 #b0)
  (define-op ldrsb   ldr/str-reg-op      #b00 #b10 #b111 #b0)
  (define-op strb    ldr/str-reg-op      #b00 #b00 #b111 #b0)

  (define-op ldurb   ldur/stur-imm-op    #b00 #b01)
  (define-op ldursb  ldur/stur-imm-op    #b00 #b10)
  (define-op sturb   ldur/stur-imm-op    #b00 #b00)

  (define ldur/stur-imm-op
    (lambda (mneu size opc dest base simm9 code*)
      (emit-code (mneu dest base simm9 code*)
        [30 size]
        [27 #b111]
        [26 #b0]
        [24 #b00]
        [22 opc]
	[21 0]
        [12 (fxlogand #x1ff simm9)]
        [10 #b00]
        [5 (ax-ea-reg-code base)]
        [0 (ax-ea-reg-code dest)])))

  (define ldur/stur-fl-imm-op
    (lambda (mneu size opc dest base simm9 code*)
      (emit-code (mneu dest base simm9 code*)
        [30 size]
        [27 #b111]
        [26 #b1]
        [24 #b00]
        [22 opc]
	[21 0]
        [12 (fxlogand #x1ff simm9)]
        [10 #b00]
        [5 (ax-ea-reg-code base)]
        [0 (reg-mdinfo dest)])))

  (define ldr/str-imm-op
    (lambda (mneu size opc dest base pimm12 code*)
      (emit-code (mneu dest base pimm12 code*)
        [30 size]
        [27 #b111]
        [26 #b0]
        [24 #b01]
        [22 opc]
        [10 (fxlogand #xfff pimm12)] ; scaled by 8
        [5 (ax-ea-reg-code base)]
        [0 (ax-ea-reg-code dest)])))

  (define ldr/str-fl-imm-op
    (lambda (mneu size opc dest base pimm12 code*)
      (emit-code (mneu dest base pimm12 code*)
        [30 size]
        [27 #b111]
        [26 #b1]
        [24 #b01]
        [22 opc]
        [10 (fxlogand #xfff pimm12)] ; scaled by 8
        [5 (ax-ea-reg-code base)]
        [0 (reg-mdinfo dest)])))

  (define-op str/preidx  pre/post-imm-op #b00 #b11)
  (define-op ldr/postidx pre/post-imm-op #b01 #b01)

  (define pre/post-imm-op
    (lambda (mneu op1 op2 dest base simm9 code*)
      (emit-code (mneu dest base code*)
        [30 #b11]
        [27 #b111]
        [26 #b0]
        [24 #b00]
        [22 op1]
        [21 #b0]
        [12 (fxlogand #x1ff simm9)]
        [10 op2]
        [5 (ax-ea-reg-code dest)]
        [0 (ax-ea-reg-code base)])))

  (define ldr/str-reg-op
    (lambda (mneu size opc option shift dest base index code*)
      (emit-code (mneu dest base index code*)
        [30 size]
        [27 #b111]
        [26 #b0]
        [24 #b00]
        [22 opc]
        [21 1]
        [16 (ax-ea-reg-code index)]     ; option<0> = 0: 32 bit, option<0> = 1: 64 bit
        [13 option]                     ; 2: uxtw, 3: lsl, 6: sxtw, 7: sxtx
        [12 shift]                      ; 0: sll 0, 1: sll 3
        [10 #b10]
        [5 (ax-ea-reg-code base)]
        [0 (ax-ea-reg-code dest)])))

  (define ldr/str-fl-reg-op
    (lambda (mneu size opc option shift dest base index code*)
      (emit-code (mneu dest base index code*)
        [30 size]
        [27 #b111]
        [26 #b1]
        [24 #b00]
        [22 opc]
        [21 1]
        [16 (ax-ea-reg-code index)]     ; option<0> = 0: 32 bit, option<0> = 1: 64 bit
        [13 option]                     ; 2: uxtw, 3: lsl, 6: sxtw, 7: sxtx
        [12 shift]                      ; 0: sll 0, 1: sll 3
        [10 #b10]
        [5 (ax-ea-reg-code base)]
        [0 (reg-mdinfo dest)])))

  (define-op ldxr
    (lambda (mneu dest base code*)
      (emit-code (mneu dest base code*)
        [30 #b11]
        [24 #b001000]
        [23 0]
        [22 1]
        [21 0]
        [16 #b11111]
        [15 0]
        [10 #b11111]
        [5 (ax-ea-reg-code base)]
        [0 (ax-ea-reg-code dest)])))

  (define-op stxr
    (lambda (mneu status src dest code*)
      (emit-code (mneu status src dest code*)
        [30 #b11]
        [24 #b001000]
        [23 0]
        [22 0]
        [21 0]
        [16 (ax-ea-reg-code status)] ; 0 if update passes, 1 if update fails
        [15 0]
        [10 #b11111]
        [5 (ax-ea-reg-code dest)]
        [0 (ax-ea-reg-code src)])))

  (define-op adr
    (lambda (mneu dest disp code*)
      (let ([disp1 (+ disp 4)])
        (emit-code (mneu dest disp code*)
          [31 0]
          [29 (bitwise-bit-field disp1 0 2)]
          [24 #b10000]
          [5  (bitwise-bit-field disp1 2 21)]
          [0  (ax-ea-reg-code dest)]))))

  ; branch ops
  (define-op bnei  branch-imm-op       (ax-cond 'ne))
  (define-op brai  branch-imm-op       (ax-cond 'al))

  (define-op br    branch-reg-op       #b00)
  (define-op blr   branch-reg-op       #b01)

  ; branch label ops
  (define-op bra
    (lambda (op dest code*)
      (record-case dest
        [(label) (offset l)
         (emit-code (op dest code*)
           [26 #b00101]
           [0 (fxlogand (fxsrl (fx+ offset 4) 2) #x3ffffff)])] ; imm26
        [else (sorry! "unexpected dest ~s" dest)])))

  (define-op beq   branch-label-op     (ax-cond 'eq))
  (define-op bne   branch-label-op     (ax-cond 'ne))
  (define-op blt   branch-label-op     (ax-cond 'lt))
  (define-op ble   branch-label-op     (ax-cond 'le))
  (define-op bgt   branch-label-op     (ax-cond 'gt))
  (define-op bge   branch-label-op     (ax-cond 'ge))
  (define-op bcc   branch-label-op     (ax-cond 'cc))
  (define-op bcs   branch-label-op     (ax-cond 'cs))
  (define-op bvc   branch-label-op     (ax-cond 'vc))
  (define-op bvs   branch-label-op     (ax-cond 'vs))
  (define-op bls   branch-label-op     (ax-cond 'ls))
  (define-op bhi   branch-label-op     (ax-cond 'hi))




  (define-op scvtf.gpr->dbl  fmov-op.gpr->flt  #b1  #b01 #b00 #b010)  ; signed integer convert to double
  (define-op fmov.dbl->gpr   fmov-op.flt->gpr  #b1  #b01 #b00 #b110)

  (define-op fcvt.sgl->dbl   fcvt-op           #b00 #b01)
  (define-op fcvt.dbl->sgl   fcvt-op           #b01 #b00)


  (define fmov-op.gpr->flt
    (lambda (op sf type rmode opcode dest src code*)
      (emit-code (op dest src code*)
        [31 sf]
        [29 #b00]
        [24 #b11110]
        [22 type]
        [21 1]
        [19 rmode]
        [16 opcode]
        [10 #b000000]
        [5 (ax-ea-reg-code src)]
        [0 (reg-mdinfo dest)])))

  (define fmov-op.flt->gpr
    (lambda (op sf type rmode opcode src dest code*)
      (emit-code (op src dest code*)
        [31 sf]
        [29 #b00]
        [24 #b11110]
        [22 type]
        [21 1]
        [19 rmode]
        [16 opcode]
        [10 #b000000]
        [5 (reg-mdinfo src)]
        [0 (ax-ea-reg-code dest)])))

  (define fcvt-op
    (lambda (op type opc fldest flsrc code*)
      (emit-code (op fldest flsrc code*)
        [31 0]
        [30 0]
        [29 0]
        [24 #b11110]
        [22 type]
        [21 1]
        [17 #b0001]
        [15 opc]
        [10 #b10000]
        [5 (reg-mdinfo flsrc)]
        [0 (reg-mdinfo fldest)])))

  (define-op fcmp
    (lambda (mneu flopnd0 flopnd1 code*)
      (emit-code (mneu flopnd0 flopnd1 code*)
        [31 0]
        [30 0]
        [29 0]
        [24 #b11110]
        [22 #b01]
        [21 1]
        [16 (reg-mdinfo flopnd1)]
        [14 #b00]
        [10 #b1000]
        [5 (reg-mdinfo flopnd0)]
        [3 #b00]
        [0 #b000])))


  (define-op rev   rev-op #b11)
  (define-op rev32 rev-op #b10)
  (define-op rev16 rev-op #b01)

  (define-op mrc mrc/mcr-op #b1)

   ; float ops
  (define-op flop
    (lambda (mneu opc fldest flopnd0 flopnd1 code*)
      (emit-code (mneu opc fldest flopnd0 flopnd1 code*)
        [31 0]
        [30 0]
        [29 0]
        [24 #b11110]
        [22 #b01]
        [21 1]
        [16 (reg-mdinfo flopnd1)]
        [10 opc]
        [5 (reg-mdinfo flopnd0)]
        [0 (reg-mdinfo fldest)])))

  (define-op fsqrt
    (lambda (mneu fldest flsrc code*)
      (emit-code (mneu fldest flsrc code*)
        [31 0]
        [30 0]
        [29 0]
        [24 #b11110]
        [22 #b01]
        [21 1]
        [17 #b0000]
        [15 #b11]
        [10 #b10000]
        [5 (reg-mdinfo flsrc)]
        [0 (reg-mdinfo fldest)])))

  ; masks are ordered n:immr:imms bitwise but are encoded as n:imms:immr, abstracted as imm13
  ; the logic for conversion is handled in ax-logical-immediate
  ; this is similiar to arm32's funky12 concept

  (define imm-mask-op
    (lambda (mneu opcode dest-ea src-ea imm13 code*)
      (emit-code (mneu dest-ea src-ea imm13 code*)
        [31 1]
        [29 opcode]
        [23 #b100100]
        [10 (fxlogand #x1fff imm13)]
        [5 (ax-ea-reg-code src-ea)]
        [0 (ax-ea-reg-code dest-ea)])))

  (define imm-tst-mask-op
    (lambda (mneu opcode src-ea imm13 code*)
      (emit-code (mneu src-ea imm13 code*)
        [31 1]
        [29 opcode]
        [23 #b100100]
        [10 (fxlogand #x1fff imm13)]
        [5 (ax-ea-reg-code src-ea)]
        [0 #b11111])))

  (define fmov-op
    (lambda (mneu opc fl->gen? src dest code*)
      (emit-code (mneu fl->gen? src dest code*)
        [31 1]
        [30 0]
        [29 0]
        [24 #b11110]
        [22 #b11]
        [21 1]
        [19 #b00]
        [16 opc]
        [10 #b000000]
        [5 (if fl->gen? (reg-mdinfo src) (ax-ea-reg-code src))]
        [0 (if fl->gen? (ax-ea-reg-code dest) (reg-mdinfo dest))])))


  (define rev-op
    (lambda (op opcode dest-ea src-ea code*)
      (emit-code (op opcode dest-ea src-ea code*)
        [31 1]
        [30 1]
        [21 #b11010110]
        [16 #b00000]
        [12 #b0000]
        [10 opcode]
        [5 (ax-ea-reg-code src-ea)]
        [0 (ax-ea-reg-code dest-ea)])))

  (define cmp-op
    (case-lambda
      [(op opnd0-ea opnd1-ea code*)
        (emit-code (op opnd0-ea opnd1-ea code*)
          [31 1]
          [30 1]
          [29 1]
          [24 #b01011]
          [22 #b00]
          [21 0]
          [16 (ax-ea-reg-code opnd1-ea)]
          [10 #b00000]
          [5 (ax-ea-reg-code opnd0-ea)]
          [0 #b11111])]
      [(op shift-count shift-type opnd0-ea opnd1-ea code*)
       (emit-code (op opnd0-ea shift-type opnd1-ea shift-count code*)
          [31 1]
          [30 1]
          [29 1]
          [24 #b01011]
          [22 (ax-shift-type shift-type)]
          [21 0]
          [16 (ax-ea-reg-code opnd1-ea)]
          [10 shift-count]
          [5 (ax-ea-reg-code opnd0-ea)]
          [0 #b11111])]))

  (define shift-op
    (lambda (op dest-ea src0-ea src1-ea shift-type code*)
      (emit-code (shift-type dest-ea src0-ea src1-ea code*)
        [29 #b100]
        [21 #b11010110]
        [16 (ax-ea-reg-code src1-ea)]
        [12 #b0010]
        [10 (case shift-type
              [(sll) #b00]
              [(srl) #b01]
              [(sra) #b10]
              [else (errorf 'shift-op "bad shift type ~s" shift-type)])]
        [5 (ax-ea-reg-code src0-ea)]
        [0 (ax-ea-reg-code dest-ea)])))

  (define shifti-op
    (lambda (op dest-ea src-ea n shift-type code*)
      (let ([imm6 (fxlogand #x3f n)])
        (emit-code (shift-type dest-ea src-ea n code*)
          [29 (case shift-type
               [(sll srl) #b110]
               [(sra) #b100])]
          [22 #b1001101]
          [16 (case shift-type
               [(sll) (- 64 imm6)]
               [(srl sra) imm6])]
         [10 (case shift-type       ; sll if imms != 111111
               [(sll) (- 63 imm6)]
               [(srl sra) #b111111]
               [else (errorf 'shifti-op "bad shift type ~s" shift-type)])]
         [5 (ax-ea-reg-code src-ea)]
         [0 (ax-ea-reg-code dest-ea)]))))

  (define-who branch-label-op
    (lambda (op cond-bits dest code*)
      (record-case dest
        [(label) (offset l)
         (emit-code (op dest code*)
           [24 #b01010100]
           [5 (fxlogand (fxsrl (fx+ offset 4) 2) #x7ffff)]
           [4 0]
           [0 cond-bits])]
        [else (sorry! who "unexpected dest ~s" dest)])))

  (define-who branch-reg-op
    (lambda (op opcode dest code*)
      (emit-code (op dest code*)
        [25 #b1101011]
        [24 0]
        [23 0]
        [21 opcode]
        [16 #b11111]
        [12 #b0000]
        [11 0]
        [10 0]
        [5 (ax-ea-reg-code dest)]
        [0 #b00000])))

  (define branch-imm-op
    (lambda (op cond-bits imm19 code*)
      (emit-code (op imm19 code*)
        [24 #b01010100]
        [5 (fxlogand #x7ffff imm19)]
        [4 0]
        [0 cond-bits])))

  (define-who mrc/mcr-op
    (lambda (op dir cond coproc opc1 dest-ea CRn CRm opc2 code*)
      (emit-code (op cond coproc opc1 dest-ea CRn CRm opc2 code*) ; encoding A1
        [22 #b1101010100]
        [21 #b0]        ; result?
        [19 #b01]
        [16 opc1]
        [12 CRn]
        [8  CRm]
        [5  opc2]
        [0  (ax-ea-reg-code dest-ea)])))



  ; Unprocessed

  ; aarch64 does not have push, pop, push-multiple, nor pop-multiple
  (define-op popm  pm-op #b10001011)
  (define-op pushm pm-op #b10010010)
  (define-op vpushm vpushm-op)

  (define pm-op
    (lambda (op opcode regs code*)
      (NOP 'unprocessed op code*)))

  (define vpushm-op
    (lambda (op flreg n code*)
      (NOP 'unprocessed op code*)))

  (define NOP
    (lambda (flag op code*)
      (printf "Warning: ~s op ~s was caught\n" flag op)
      (emit-code (flag op code*)
        [22 #b1101010100]
        [21 #b0]
        [20 #b00]
        [16 #b011]
        [12 #b0010]
        [8  #b0000]
        [5  #b000]
        [0  #b11111])))



  ; asm helpers

  ; man page 153
  (define-who ax-cond
    (lambda (x)
      (case x
        [(eq) #b0000] ; z == 1
        [(ne) #b0001] ; z == 0
        [(cs) #b0010] ; c == 1, equal to hs
        [(cc) #b0011] ; c == 0, equal to lo
        [(mi) #b0100] ; n == 1
        [(pl) #b0101] ; n == 0
        [(vs) #b0110] ; v == 1
        [(vc) #b0111] ; v == 0
        [(hi) #b1000] ; c == 1 ^ z == 0
        [(ls) #b1001] ; ! (c == 1 ^ z == 0)
        [(ge) #b1010] ; n == v
        [(lt) #b1011] ; n! = v
        [(gt) #b1100] ; z == 0 ^ n == v
        [(le) #b1101] ; !(z == 0 ^ n == v)
        [(al) #b1110] ; T       1111 is also considered to be al
        [else (sorry! who "unrecognized cond name ~s" x)])))

  (define-who ax-shift-type
    (lambda (op)
      (case op
        [(sll) #b00]
        [(srl) #b01]
        [(sra) #b10]
        ; [(ror) #b11] disallowed
        [else ($oops who "unsupported op ~s" op)])))

  (define-syntax emit-code
    (lambda (x)
      ; NB: probably won't need emit-code to weed out #f
      (define build-maybe-cons*
        (lambda (op e* e-ls)
          (if (null? e*)
            e-ls
              #`(let ([t #,(car e*)] [ls #,(build-maybe-cons* op (cdr e*) e-ls)])
                  (if t (cons t ls) ls)))))
      (syntax-case x ()
        [(_ (op opnd ... ?code*) chunk ...)
         (build-maybe-cons* #'op #'((build long (byte-fields chunk ...)))
           #'(aop-cons* `(asm ,op ,opnd ...) ?code*))])))

  #;(define-syntax emit-code
    (lambda (x)
      (syntax-case x ()
        [(_ (op opnd ... ?code*) chunk ...)
         (fold-right cons #'(aop-cons* `(asm ,op ,opnd ...) ?code*)
           #'((build long (byte-fields chunk ...))))])))

  (define-who ax-size-code
    (lambda (x)
      (case x
        [(byte) 0]
        [(word) 1]
        [(long) 1]
        [else (sorry! who "invalid size ~s" x)])))

  (define-syntax build
    (syntax-rules ()
      [(_ x e)
       (and (memq (datum x) '(byte word long)) (integer? (datum e)))
       (quote (x . e))]
      [(_ x e)
       (memq (datum x) '(byte word long))
       (cons 'x e)]))

  (define-syntax byte-fields
    ; NB: make more efficient for fixnums
    (syntax-rules ()
      [(byte-fields (n e) ...)
       (andmap fixnum? (datum (n ...)))
       (+ (bitwise-arithmetic-shift-left e n) ...)]))

  (define ax-byte-size?
    (lambda (n)
      (<= -128 n 127)))

  (define ax-range?
    (lambda (low x high)
      (record-case x
        [(imm) (n) (<= low n high)]
        [else #f])))

  (define ax-ea-branch-disp
    (lambda (dest-ea)
      (record-case dest-ea
        [(literal) stuff (cons 'rel stuff)]
        [else ($oops 'assembler-internal
                "ax-ea-branch-disp dest-ea=~s" dest-ea)])))

  (define signed-bound?
    (lambda (imm bits)
      (let ([bound (expt 2 (- bits 1))])
        (fx<= (- bound) imm (- bound 1)))))

  (define shift-count?
    (lambda (imm)
      (and (fixnum? imm) (fx<= 1 imm 63))))

  (define unsigned8?
    (lambda (imm)
      (and (fixnum? imm)
           ($fxu< imm (expt 2 8)))))

  (define unsigned12?
    (lambda (imm)
      (and (fixnum? imm)
           ($fxu< imm (expt 2 12)))))

  (define imm16?
    (lambda (imm)
      (and (fixnum? imm)
           (or ($fxu< imm (expt 2 16))
               (signed-bound? imm 16)))))

  (define signed9?
    (lambda (imm)
      (and (fixnum? imm)
           (signed-bound? imm 9))))

  (define signed21?
    (lambda (imm)
      (and (fixnum? imm)
           (signed-bound? imm 21))))

  (define branch-disp?
    (lambda (x)
      (and (fixnum? x)
           (signed-bound? x 28)
           (not (fxlogtest x #b11)))))

  (define cond-branch-disp?
    (lambda (x)
      (and (fixnum? x)
           (signed-bound? x 21)
           (not (fxlogtest x #b11)))))


  (define asm-size
    (lambda (x)
      (case (car x)
        [(asm arm64-abs arm64-jump arm64-call) 0]
        [(byte) 1]
        [(word) 2]
        [(long) 4]
        [else 8])))

  (define ax-mov64
    (lambda (dest n code*)
     (emit movi dest 0
       (emit movi/k dest 0 1 #t
        (emit movi/k dest 0 2 #t
          (emit movi/k dest 0 3 #t code*))))))

(define ax-mov-quad
    (lambda (dest imm64 code*)
     (emit movi dest (fxlogand #xffff imm64)
       (emit movi/k dest (fxlogand #xffff (fxsrl imm64 16)) 1 #t
        (emit movi/k dest (fxlogand #xffff (fxsrl imm64 32)) 2 #t
          (emit movi/k dest (fxlogand #xffff (fxsrl imm64 48)) 3 #t code*))))))

  (define-who asm-move
    (lambda (code* dest src)
      ; move pseudo instruction used by set! case in select-instruction
      ; guarantees dest is a reg and src is reg, mem, or imm OR dest is
      ; mem and src is reg.
      (Trivit (dest src)
        (define (bad!) (sorry! who "unexpected combination of src ~s and dest ~s" src dest))
        (define (finish-move p* keep)
          (if (null? p*)
              code*
              (let ([p (car p*)])
                (emit movi/k dest (cdr p) (car p) keep
                  (finish-move (cdr p*) #t)))))
        (cond
          [(ax-reg? dest)
           (record-case src
             [(reg) ignore (emit mov dest src code*)]
             [(imm) (n)
              (let ([p* (move-immediate n)])
                (cond
                  [(null? p*) (ax-mov64 dest n code*)]
                  [(< (length p*) 3) (finish-move p* #f)]
                  [else
                   (let ([np* (move-immediate (lognot n))])
                     (if (< (length np*) 4)
                         (let ([p* (map (lambda (x) (cons (car x) (lognot (cdr x)))) (cdr np*))]
                               [np (car np*)])
                           (emit movn dest (cdr np) (car np)
                             (finish-move p* #t)))
                         (finish-move p* #f)))]))]
             [(literal) stuff
              (ax-mov64 dest 0
                (asm-helper-relocation code* (cons 'arm64-abs stuff)))]
             [(disp) (n breg)
              (ldri-dynamic dest breg n code*)]
             [(index) (n ireg breg)
              (safe-assert (eqv? n 0))
              (emit ldr dest `(reg . ,breg) `(reg . ,ireg) code*)]
             [else (bad!)])]
          [(ax-reg? src)
           (record-case dest
             [(disp) (n breg)
              (stri-dynamic src breg n code*)]
             [(index) (n ireg breg)
              (safe-assert (eqv? n 0))
              (emit str src `(reg . ,breg) `(reg . ,ireg) code*)]
             [else (bad!)])]
          [else (bad!)]))))

  (define-who asm-move/extend
    (lambda (op)
      (lambda (code* dest src)
        (Trivit (dest src)
          (case op
            [(sext8) (emit sxtb dest src code*)]
            [(sext16) (emit sxth dest src code*)]
            [(sext32) (emit sxtw dest src code*)]
            [(zext8) (emit uxtb dest src code*)]
            [(zext16) (emit uxth dest src code*)]
            [(zext32) (emit uxtw dest src code*)]
            [else (sorry! who "unexpected op ~s" op)])))))

  (module (asm-add asm-sub asm-logand asm-logor asm-logxor)
    (define-syntax asm-binop-64
      (syntax-rules ()
        [(_ opi op)
         (lambda (set-cc?)
           (lambda (code* dest src0 src1)
             (Trivit (dest src0 src1)
               (record-case src1
                 [(imm) (n) (emit opi set-cc? dest src0 n code*)]
                 [else (emit op set-cc? dest src0 src1 code*)]))))]))

    (define-syntax asm-log-binop
      (syntax-rules ()
        [(_ opi op)
         (lambda (code* dest src0 src1)
           (Trivit (dest src0 src1)
             (record-case src1
               [(imm) (n) (emit opi dest src0 n code*)]
               [else (emit op dest src0 src1 code*)])))]))

    (define asm-add (asm-binop-64 addi add))
    (define asm-sub (asm-binop-64 subi sub))
    (define asm-logand (asm-log-binop andi and))
    (define asm-logor  (asm-log-binop orri orr))
    (define asm-logxor (asm-log-binop eori eor)))

  (define asm-mul
    (lambda (code* dest src0 src1)
      (Trivit (dest src0 src1)
        (emit mul dest src0 src1 code*))))

  (define asm-smulh
    (lambda (code* dest src0 src1)
      (Trivit (dest src0 src1)
        (emit smulh dest src0 src1 code*))))

  (define asm-sdiv
    (lambda (code* dest src0 src1)
      (Trivit (dest src0 src1)
        (emit sdiv dest src0 src1 code*))))

  (define asm-udiv
    (lambda (code* dest src0 src1)
      (Trivit (dest src0 src1)
        (emit udiv dest src0 src1 code*))))

  ; modified to remove tmp
  (define asm-smull
    (lambda (code* dest src0 src1)
      (Trivit (dest src0 src1)
        (emit smull dest src0 src1 code*))))

  (define asm-cmp/shift
    (lambda (count type)
      (lambda (code* src0 src1)
        (Trivit (src0 src1)
          (emit cmp/shift count type src0 src1 code*)))))

  (define asm-cmpi
    (lambda (code* imm12 src0)
      (Trivit (src0)
        (nanopass-case (L16 Triv) imm12
          [(immediate ,imm)
           (emit cmpi src0 imm code*)]))))


  (define-who asm-fl-load/cvt
    (lambda (op flreg)
      (lambda (code* base offset)
        (Trivit (base offset)
          (case op
            [(load-single->double)
              (emit fldri.sgl %flreg2 base (ax-imm-data offset)
                (emit fcvt.sgl->dbl flreg %flreg2 code*))]
            [(load-double->single)
             (emit fldri.dbl %flreg2 base (ax-imm-data offset)
               (emit fcvt.dbl->sgl flreg %flreg2 code*))]
            [else (sorry! who "unrecognized op ~s" op)])))))

  (define-who asm-fl-store/cvt
    (lambda (op flreg)
      (lambda (code* base offset)
        (Trivit (base offset)
          (case op
            [(store-single->double)
             (emit fcvt.sgl->dbl %flreg2 flreg
               (emit fstri.dbl %flreg2 base (ax-imm-data offset) code*))]
            [else (sorry! who "unrecognized op ~s" op)])))))

  (define-who asm-fl-load/store
    (lambda (op flreg)
      (lambda (code* base offset)
        (Trivit (offset)
          (let ([offset (ax-imm-data offset)])
            (case op
              [(load-single) (fldri-dynamic.sgl flreg base offset code*)]
              [(load-double) (fldri-dynamic.dbl flreg base offset code*)]
              [(store-single) (fstri-dynamic.sgl flreg base offset code*)]
              [(store-double) (fstri-dynamic.dbl flreg base offset code*)]
              [else (sorry! who "unrecognized op ~s" op)]))))))

  (define-who asm-load
    (lambda (type)
      (rec asm-load-internal
        (lambda (code* dest base index offset)
          (let ([n (nanopass-case (L16 Triv) offset
                     [(immediate ,imm) imm]
                     [else (sorry! who "unexpected non-immediate offset ~s" offset)])])
            (Trivit (dest base)
              (cond
                [(eq? index %zero)
                  (case type
                    [(integer-64 unsigned-64) (emit ldur dest base n code*)]
                    [(integer-32)  (emit ldursw dest base n code*)]
                    [(unsigned-32) (emit ldurw dest base n code*)]
                    [(integer-16)  (emit ldursh dest base n code*)]
                    [(unsigned-16) (emit ldurh dest base n code*)]
                    [(integer-8)   (emit ldursb dest base n code*)]
                    [(unsigned-8)  (emit ldurb dest base n code*)]
                    [else (sorry! who "unexpected mref type ~s" type)])]
                [(eqv? n 0)
                  (Trivit (index)
                    (case type
                      [(integer-64 unsigned-64) (emit ldr dest base index code*)]
                      [(integer-32)  (emit ldrsw dest base index code*)]
                      [(unsigned-32) (emit ldrw dest base index code*)]
                      [(integer-16)  (emit ldrsh dest base index code*)]
                      [(unsigned-16) (emit ldrh dest base index code*)]
                      [(integer-8)   (emit ldrsb dest base index code*)]
                      [(unsigned-8)  (emit ldrb dest base index code*)]
                      [else (sorry! who "unexpected mref type ~s" type)]))]
                [else (sorry! who "expected %zero index or 0 offset, got ~s and ~s" index offset)])))))))

  (define-who asm-store
    (lambda (type)
      (rec asm-store-internal
        (lambda (code* base index offset src)
          (let ([n (nanopass-case (L16 Triv) offset
                     [(immediate ,imm) imm]
                     [else (sorry! who "unexpected non-immediate offset ~s" offset)])])
            (Trivit (src base)
              (cond
                [(eq? index %zero)
                  (case type
                    [(integer-64 unsigned-64) (emit stur  src base n code*)]
                    [(integer-32 unsigned-32) (emit sturw src base n code*)]
                    [(integer-16 unsigned-16) (emit sturh src base n code*)]
                    [(integer-8  unsigned-8)  (emit sturb src base n code*)]
                    [else (sorry! who "unexpected mref type ~s" type)])]
                [(eqv? n 0)
                  (Trivit (index)
                    (case type
                      [(integer-64 unsigned-64) (emit str  src base index code*)]
                      [(integer-32 unsigned-32) (emit strw src base index code*)]
                      [(integer-16 unsigned-16) (emit strh src base index code*)]
                      [(integer-8  unsigned-8)  (emit strb src base index code*)]
                      [else (sorry! who "unexpected mref type ~s" type)]))]
                [else (sorry! who "expected %zero index or 0 offset, got ~s and ~s" index offset)])))))))

  (define-who asm-flop-2
    (lambda (op)
      (lambda (code* src1 src2 dest)
        (Trivit (src1 src2 dest)
          (emit fldri.dbl %flreg1 src1 0
            (emit fldri.dbl %flreg2 src2 0
              (let ([code* (emit fstri.dbl %flreg1 dest 0 code*)])
                (case op
                  [(fl+) (emit flop #b001010 %flreg1 %flreg1 %flreg2 code*)]
                  [(fl-) (emit flop #b001110 %flreg1 %flreg1 %flreg2 code*)]
                  [(fl*) (emit flop #b000010 %flreg1 %flreg1 %flreg2 code*)]
                  [(fl/) (emit flop #b000110 %flreg1 %flreg1 %flreg2 code*)]
                  [else (sorry! who "unrecognized op ~s" op)]))))))))

  (define asm-flsqrt
    (lambda (code* src dest)
      (Trivit (src dest)
        (emit fldri.dbl %flreg1 src 0
          (emit fsqrt %flreg1 %flreg1
            (emit fstri.dbl %flreg1 dest 0 code*))))))

  (define asm-trunc
    (lambda (code* dest flonumreg)
      (Trivit (dest flonumreg)
        (emit fldri.dbl %flreg1 flonumreg 0
          (emit fmov.dbl->gpr %flreg1 dest code*)))))

  (define asm-flt
    (lambda (code* src flonumreg)
      (Trivit (src flonumreg)
        (emit scvtf.gpr->dbl %flreg1 src
          (emit fstri.dbl %flreg1 flonumreg 0 code*)))))

  (define-who asm-swap
    (lambda (type)
      (rec asm-swap-internal
        (lambda (code* dest src)
          (Trivit (dest src)
            (case type
              [(integer-16 unsigned-16) (emit rev16 dest src code*)]
              [(integer-32 unsigned-32) (emit rev32 dest src code*)]
              [(integer-64 unsigned-64) code*]
              [else (sorry! who "unexpected asm-swap type argument ~s" type)]))))))


  ; TODO needs testing
  (define asm-lock
    ;  tmp = ldxr src
    ;  cmp tmp, 0
    ;  bne L1 (+2)
    ;  tmp = 1
    ;  tmp = stxr tmp, src
    ;L1:
    (lambda (code* src tmp)
      (Trivit (src tmp)
        (emit ldxr tmp src
          (emit cmpi tmp 0
            (emit bnei 1
              (emit movi tmp 1
                (emit stxr tmp tmp src code*))))))))

  (define-who asm-lock+/-
    ; L:
    ;   tmp1 = ldxr src
    ;   tmp1 = tmp1 +/- 1
    ;   tmp2 = stxr tmp1, src
    ;   cmp tmp2, 0
    ;   bne L (-6)
    ;   cmp tmp1, 0
    (lambda (op)
      (lambda (code* src tmp1 tmp2)
        (Trivit (src tmp1 tmp2)
          (emit ldxr tmp1 src
            (let ([code* (emit stxr tmp2 tmp1 src
                           (emit cmpi tmp2 0
                             (emit bnei -6
                               (emit cmpi tmp1 0 code*))))])
              (case op
                [(locked-incr!) (emit addi #f tmp1 tmp1 1 code*)]
                [(locked-decr!) (emit subi #f tmp1 tmp1 1 code*)]
                [else (sorry! who "unexpected op ~s" op)])))))))

  (define-who asm-cas
    ;   tmp = ldxr src
    ;   cmp tmp, old
    ;   bne L (+2)
    ;   tmp2 = stxr new, src
    ;   cmp tmp2, 0
    ; L:
    (lambda (code* src old new tmp1 tmp2)
      (Trivit (src old new tmp1 tmp2)
        (emit ldxr tmp1 src
          (emit cmp tmp1 old
            (emit bnei 1
              (emit stxr tmp2 new src
                (emit cmpi tmp2 0
                   code*))))))))

  (define asm-fl-relop
    (lambda (info)
      (lambda (l1 l2 offset x y)
        (Trivit (x y)
          (values
            (emit fldri.dbl %flreg1 x 0
              (emit fldri.dbl %flreg2 y 0
                (emit fcmp %flreg1 %flreg2 '())))
            (asm-conditional-jump info l1 l2 offset))))))

  (define-who asm-relop
    (lambda (info)
      (rec asm-relop-internal
        (lambda (l1 l2 offset x y)
          (Trivit (x y)
            (unless (ax-reg? x) (sorry! who "unexpected first operand ~s" x))
            (values
              (record-case y
                [(imm) (n) (emit cmpi x n '())]
                [(reg) ignore (emit cmp x y '())]
                [else (sorry! who "unexpected second operand ~s" y)])
              (asm-conditional-jump info l1 l2 offset)))))))

  (define asm-condition-code
    (lambda (info)
      (rec asm-check-flag-internal
        (lambda (l1 l2 offset)
          (values '() (asm-conditional-jump info l1 l2 offset))))))

  (define asm-pop-multiple
    (lambda (regs)
      (lambda (code*)
        (emit popm regs code*))))

  (define asm-push-multiple
    (lambda (regs)
      (lambda (code*)
        (emit pushm regs code*))))

  (define asm-vpush-multiple
    (lambda (reg n)
      (lambda (code*)
        (emit vpushm reg n code*))))

  (define asm-save-flrv
    (lambda (code*)
      (let ([sp (cons 'reg %sp)])
        (emit subi #f sp sp 16
          (emit fstri.dbl %Cfpretval sp 0 code*)))))

  (define asm-restore-flrv
    (lambda (code*)
      (let ([sp (cons 'reg %sp)])
        (emit fldri.dbl %Cfpretval sp 0
          (emit addi #f sp sp 16 code*)))))

  (define asm-read-counter
    (case-lambda
      [(k)
       (lambda (code* dest)
         (Trivit (dest)
           (emit mrc 'al 15 0 dest 15 12 k code*)))]
      [()
       (lambda (code* dest src)
         (Trivit (dest src)
           (emit cmpi src 0
             ; may need ISB instruction here
             (emit mrc 'eq 15 0 dest 15 12 2
               (emit mrc 'ne 15 0 dest 15 12 3 code*)))))]))

  (define asm-library-jump
    (lambda (l)
      (asm-helper-jump '()
        `(arm64-jump ,(constant code-data-disp) (library-code ,(libspec-label-libspec l))))))

  (define asm-library-call
    (lambda (libspec save-ra?)
      (let ([target `(arm64-call ,(constant code-data-disp) (library-code ,libspec))])
        (rec asm-asm-call-internal
          (lambda (code* dest jmp-tmp . ignore) ; ignore arguments, which must be in fixed locations
            (asm-helper-call code* target save-ra? jmp-tmp))))))

  (define asm-library-call!
    (lambda (libspec save-ra?)
      (let ([target `(arm64-call ,(constant code-data-disp) (library-code ,libspec))])
        (rec asm-asm-call-internal
          (lambda (code* jmp-tmp . ignore) ; ignore arguments, which must be in fixed locations
            (asm-helper-call code* target save-ra? jmp-tmp))))))

  (define asm-c-simple-call
    (lambda (entry save-ra?)
      (let ([target `(arm64-call 0 (entry ,entry))])
        (rec asm-c-simple-call-internal
          (lambda (code* jmp-tmp . ignore)
            (asm-helper-call code* target save-ra? jmp-tmp))))))

  (define-who asm-indirect-call
    (lambda (code* dest lr . ignore)
      (safe-assert (eq? lr %lr))
      (Trivit (dest)
        (unless (ax-reg? dest) (sorry! who "unexpected dest ~s" dest))
        (emit blr dest code*))))

  (define asm-direct-jump
    (lambda (l offset)
      (asm-helper-jump '() (make-funcrel 'arm64-jump l offset))))

  (define asm-literal-jump
    (lambda (info)
      (asm-helper-jump '()
        `(arm64-jump ,(info-literal-offset info) (,(info-literal-type info) ,(info-literal-addr info))))))

  (define-who asm-indirect-jump
    (lambda (src)
      (Trivit (src)
        (record-case src
          [(reg) ignore (emit br src '())]
          [else (sorry! who "unexpected src ~s" src)]))))

  (define asm-logtest
    (lambda (i? info)
      (lambda (l1 l2 offset x y)
        (Trivit (x y)
          (values
            (record-case y
              [(imm) (n) (emit tsti x n '())]
              [else (emit tst x y '())])
            (let-values ([(l1 l2) (if i? (values l2 l1) (values l1 l2))])
              (asm-conditional-jump info l2 l1 offset)))))))

  (define asm-get-tc
    (let ([target `(arm64-call 0 (entry ,(lookup-c-entry get-thread-context)))])
      (lambda (code* dest jmp-tmp . ignore) ; dest is ignored, since it is always Cretval
        (asm-helper-call code* target #f jmp-tmp))))

  (define-who asm-return-address
    (lambda (dest l incr-offset next-addr)
      (make-rachunk dest l incr-offset next-addr
        (or (cond
              [(local-label-offset l) =>
               (lambda (offset)
                 (let ([disp (fx- next-addr (fx- offset incr-offset))])
                   (cond
                     [(signed21? disp)
                        (Trivit (dest)
                          ; aka adr, encoding A1
                          (emit adr dest disp '()))]
                     #;[(fixnum? disp)
                        (Trivit (dest)
                          ; 64 bit adr, this should never be used realistically
                          (emit adr dest 0
                            (ax-mov-quad `(reg . ,%ratmp) (fx+ disp 20)
                              (emit add #f dest dest `(reg . ,%ratmp) '()))))]
                     [else #f])))]
              [else #f])
            (asm-move '() dest (with-output-language (L16 Triv) `(label-ref ,l ,incr-offset)))))))

  (define-who asm-jump
    (lambda (l next-addr)
      (make-gchunk l next-addr
        (cond
          [(local-label-offset l) =>
           (lambda (offset)
             (let ([disp (fx- next-addr offset)])
               (cond
                 [(eqv? disp 0) '()]
                 [(branch-disp? disp) (emit bra `(label ,disp ,l) '())]
                 ; will have to deal with this on architectures with smaller displacements.
                 ; problem is we'll need a temp reg, and we discover this way past register
                 ; allocation.  so possibly compute the max possible code-object size at
                 ; instruction selection time.  when max possible size exceeds branch range
                 ; (plus or minus), supply asm-jump and others like it an unspillable.  don't
                 ; want to supply an unspillable for smaller code objects since this
                 ; unnecessarily constrains the register allocator.
                 [else (sorry! who "no support for code objects > 128MB in length")])))]
          [else
            ; label must be somewhere above.  generate something so that a hard loop
            ; doesn't get dropped.  this also has some chance of being the right size
            ; for the final branch instruction.
            (emit bra `(label 0 ,l) '())]))))

  (define-who asm-conditional-jump
    (lambda (info l1 l2 next-addr)
      (define get-disp-opnd
        (lambda (next-addr l)
          (if (local-label? l)
              (cond
                [(local-label-offset l) =>
                 (lambda (offset)
                   (let ([disp (fx- next-addr offset)])
                     (values disp `(label ,disp ,l))))]
                [else (values 0 `(label 0 ,l))])
              (sorry! who "unexpected label ~s" l))))
      (let ([type (info-condition-code-type info)]
            [reversed? (info-condition-code-reversed? info)])
        (make-cgchunk info l1 l2 next-addr
          (let ()
            (define-syntax pred-case
              (lambda (x)
                (define build-bop-seq
                  (lambda (bop opnd1 opnd2 l2 body)
                    #`(let ([code* (emit #,bop #,opnd1 code*)])
                        (let-values ([(ignore #,opnd2) (get-disp-opnd (fx+ next-addr (asm-size* code*)) #,l2)])
                          #,body))))
                (define ops->code
                  (lambda (bop opnd)
                    #`(emit #,bop #,opnd code*)))
                (define handle-reverse
                  (lambda (e opnd l)
                    (syntax-case e (r?)
                      [(r? c1 c2) #`(if reversed? #,(ops->code #'c1 opnd) #,(ops->code #'c2 opnd))]
                      [_ (ops->code e opnd)])))

                ; pass in inverse op to jump over a 28 bit unconditional branch (actually a shifted 26 bit branch)
                (define handle-reverse-imm28
                  (lambda (e opnd base l)
                    (syntax-case e (r?)
                      [(r? c1 c2) #`(if reversed? #,(ops->code-imm28 #'c1 opnd base) #,(ops->code-imm28 #'c2 opnd base))]
                      [_ (ops->code-imm28 e opnd base)])))
                (define ops->code-imm28
                  (lambda (bop opnd base)
                     #`(emit #,bop `(label ,4 #,base)
                         (emit bra #,opnd code*))))

                ; could also handle 64 bit immediates using similar logic to ops->code-imm28
                ; you would have to choose a register to serve as ratmp2
                ; (emit #,bop `(label ,28 #,base)      <- passing in inverse bop during handle-inverse
                ;   (emit adr `(reg . %ratmp)
                ;     (ax-mov-quad `(reg . %ratmp2)
                ;       (emit add `(reg . %ratmp) `(reg . %ratmp) `(reg . ratmp2)
                ;         (emit br `(reg . %ratmp) code*)))))

                (define handle-inverse
                  (lambda (e)
                    (syntax-case e (i?)
                      [(i? c1 c2)
                       #`(cond
                           [(fx= disp1 0)
                             (cond
                               [(cond-branch-disp? disp2)
                                 #,(handle-reverse #'c1 #'opnd2 #'l2)]
                               [(branch-disp? disp2)
                                 #,(handle-reverse-imm28 #'c2 #'opnd2 #'opnd1 #'l2)]
                               [else
                                 (sorry! "unsupported displacement ~s" disp2)])]
                           [(fx= disp2 0)
                             (cond
                               [(cond-branch-disp? disp1)
                                 #,(handle-reverse #'c2 #'opnd1 #'l1)]
                               [(branch-disp? disp1)
                                 #,(handle-reverse-imm28 #'c1 #'opnd1 #'opnd2 #'l1)]
                               [else
                                 (sorry! "unsupported displacement ~s" disp1)])]
                           [else
                             #,(build-bop-seq #'bra #'opnd2 #'opnd1 #'l1
                                     (handle-reverse #'c2 #'opnd1 #'l1))])]
                      [_ #`(cond
                             [(fx= disp1 0) #,(handle-reverse e #'opnd2 #'l2)]
                             [else #,(build-bop-seq #'bra #'opnd1 #'opnd2 #'l2
                                       (handle-reverse e #'opnd2 #'l2))])])))
                (syntax-case x ()
                  [(_ [(pred ...) cl-body] ...)
                   (with-syntax ([(cl-body ...) (map handle-inverse #'(cl-body ...))])
                     #'(let ([code* '()])
                         (let-values ([(disp1 opnd1) (get-disp-opnd next-addr l1)]
                                      [(disp2 opnd2) (get-disp-opnd next-addr l2)])
                           (case type
                             [(pred ...) cl-body] ...
                             [else (sorry! who "~s branch type is currently unsupported" type)]))))])))
            (pred-case
              [(eq?) (i? bne beq)]
              [(u<) (i? (r? bls bcs) (r? bhi bcc))]
              [(<) (i? (r? ble bge) (r? bgt blt))]
              [(<=) (i? (r? blt bgt) (r? bge ble))]
              [(>) (i? (r? bge ble) (r? blt bgt))]
              [(>=) (i? (r? bgt blt) (r? ble bge))]
              [(overflow) (i? bvc bvs)]
              [(carry) (i? bcc bcs)]

              ; result of comparing sign bit of low word with all bits in high word: eq if no overflow, ne if oveflow
              [(multiply-overflow) (i? beq bne)]

              [(fl<) (i? (r? ble bcs) (r? bgt bcc))]
              [(fl<=) (i? (r? blt bhi) (r? bge bls))]
              [(fl=) (i? bne beq)]))))))

  (define asm-data-label
    (lambda (code* l offset func code-size)
      (let ([rel (make-funcrel 'abs l offset)])
        (cons* rel (aop-cons* `(asm "mrv point:" ,rel) code*)))))

  (define asm-helper-jump
    (lambda (code* reloc)
      ; NB: kills %ts, unbeknownst to the instruction scheduler
      ; NB: jmp-tmp should be included in jump syntax, introduced by md-handle-jump, and passed in from code generator
      ; NB: probably works despite this since %ts is never live at the jmp point anyway
      (let ([jmp-tmp (cons 'reg %ts)])
        (ax-mov64 jmp-tmp 0
          (emit br jmp-tmp
            (asm-helper-relocation code* reloc))))))

  (define asm-kill
    (lambda (code* dest)
      code*))

  ; NOTE: arm64 requires %sp to be 16-byte aligned, but we only actually need 8-bytes
  ; this solution is space inefficient in cases where we want to push/pop multiple items
  ; in such instances, use stp/ldp to move two at a time and maintain alignment
  (define ax-save/restore
    ; push/pop while maintaining 16-byte alignment
    (lambda (code* reg-ea p)
      (let ([sp (cons 'reg %sp)])
        (emit str/preidx sp reg-ea -16
          (p (emit ldr/postidx sp reg-ea 16 code*))))))

  (define asm-helper-call
    (lambda (code* reloc save-ra? jmp-tmp)
      ; NB: kills %lr
      (let ([jmp-tmp (cons 'reg jmp-tmp)])
        (define maybe-save-ra
          (lambda (code* p)
            (if save-ra?
                (ax-save/restore code* (cons 'reg %lr) p)
                (p code*))))
        (maybe-save-ra code*
          (lambda (code*)
            (ax-mov64 jmp-tmp 0
              (emit blr jmp-tmp
                (asm-helper-relocation code* reloc))))))))

  (define asm-helper-relocation
    (lambda (code* reloc)
      (cons* reloc (aop-cons* `(asm "relocation:" ,reloc) code*))))

  (define asm-rp-header
    (let ([mrv-error `(abs ,(constant code-data-disp)
                        (library-code ,(lookup-libspec values-error)))])
      (lambda (code* mrvl fs lpm func code-size)
        (cons*
          (if (target-fixnum? lpm)
              `(quad . ,(fix lpm))
              `(abs 0 (object ,lpm)))
          (aop-cons* `(asm livemask: ,(format "~b" lpm))
            '(code-top-link)
            (aop-cons* `(asm code-top-link)
              `(quad . ,fs)
              (aop-cons* `(asm "frame size:" ,fs)
                (if mrvl
                    (asm-data-label code* mrvl 0 func code-size)
                    (cons*
                      mrv-error
                      (aop-cons* `(asm "mrv point:" ,mrv-error)
                        code*))))))))))

  ; NB: reads from %lr...should be okay if declare-intrinsics sets up return-live* properly
  (define asm-return (lambda () (emit br (cons 'reg %lr) '())))

  (define asm-c-return (lambda (info) (emit br (cons 'reg %lr) '())))

  (define-who asm-shiftop
    (lambda (op)
      (lambda (code* dest src0 src1)
        (Trivit (dest src0 src1)
          (record-case src1
            [(imm) (n) (emit shifti dest src0 n op code*)]
            [else (emit shift dest src0 src1 op code*)])))))

  (define asm-lognot
    (lambda (code* dest src)
      (Trivit (dest src)
        (emit mvn dest src code*))))

  (define asm-enter values)

  (define-who asm-inc-cc-counter
    (lambda (code* addr val tmp)
      (Trivit (addr val tmp)
        (define do-ldr
          (lambda (offset k code*)
            (emit ldur tmp addr offset (k (emit stur tmp addr offset code*)))))
        (define do-add/cc
          (lambda (code*)
            (record-case val
              [(imm) (n) (emit addi #t tmp tmp n code*)]
              [else (emit add #t tmp tmp val code*)])))
        (do-ldr 0
          do-add/cc
          (emit bnei 2
            (do-ldr 4
              (lambda (code*)
                (emit addi #f tmp tmp 1 code*))
              code*))))))

  (module (asm-foreign-call asm-foreign-callable)
    (define align (lambda (b x) (let ([k (- b 1)]) (fxlogand (fx+ x k) (fxlognot k)))))
    (define (double-member? m) (and (eq? (car m) 'float)
                                    (fx= (cadr m) 8)))
    (define (float-member? m) (and (eq? (car m) 'float)
                                   (fx= (cadr m) 4)))
    (define (indirect-result-that-fits-in-registers? result-type)
      (nanopass-case (Ltype Type) result-type
        [(fp-ftd& ,ftd)
         (let* ([members ($ftd->members ftd)]
                [num-members (length members)])
           (or (fx<= ($ftd-size ftd) 4)
               (and (fx= num-members 1)
                    ;; a struct containing only int64 is not returned in a register
                    (or (not ($ftd-compound? ftd))))
               (and (fx<= num-members 4)
                    (or (andmap double-member? members)
                        (andmap float-member? members)))))]
        [else #f]))
    (define sgl-regs (lambda () (list %Cfparg1 %Cfparg2 %Cfparg3 %Cfparg4 %Cfparg5 %Cfparg6 %Cfparg7 %Cfparg8)))

    (define-who asm-foreign-call
      (with-output-language (L13 Effect)
        (define int-regs (lambda () (list %Carg1 %Carg2 %Carg3 %Carg4 %Carg5 %Carg6 %Carg7 %Carg8)))
        (letrec ([load-double-stack
                   (lambda (offset)
                     (lambda (x) ; requires var
                       (%seq
                         (inline ,(make-info-loadfl %flreg1) ,%load-double ,x ,%zero ,(%constant flonum-data-disp))
                         (inline ,(make-info-loadfl %flreg1) ,%store-double ,%sp ,%zero (immediate ,offset)))))]
                 [load-single-stack
                   (lambda (offset)
                     (lambda (x) ; requires var
                       (%seq
                         (inline ,(make-info-loadfl %flreg1) ,%load-double->single ,x ,%zero ,(%constant flonum-data-disp))
                         (inline ,(make-info-loadfl %flreg1) ,%store-single ,%sp ,%zero (immediate ,offset)))))]
                 [load-int-stack
                   (lambda (offset)
                     (lambda (rhs) ; requires rhs
                       `(set! ,(%mref ,%sp ,offset) ,rhs)))]
                 [load-int64-stack
                   (lambda (offset)
                     (lambda (lorhs hirhs) ; requires rhs
                       (%seq
                         (set! ,(%mref ,%sp ,offset) ,lorhs)
                         (set! ,(%mref ,%sp ,(fx+ offset 4)) ,hirhs))))]
                 [load-int-indirect-stack
                   (lambda (offset from-offset size)
                     (lambda (x) ; requires var
                       (case size
                         [(3)
                          (%seq
                           (set! ,(%mref ,%sp ,offset) (inline ,(make-info-load 'integer-16 #f) ,%load ,x ,%zero (immediate ,from-offset)))
                           (set! ,(%mref ,%sp ,(fx+ offset 2)) (inline ,(make-info-load 'integer-8 #f) ,%load ,x ,%zero (immediate ,(fx+ from-offset 2)))))]
                         [else
                          `(set! ,(%mref ,%sp ,offset) ,(case size
                                                          [(1) `(inline ,(make-info-load 'integer-8 #f) ,%load ,x ,%zero (immediate ,from-offset))]
                                                          [(2) `(inline ,(make-info-load 'integer-16 #f) ,%load ,x ,%zero (immediate ,from-offset))]
                                                          [(4) (%mref ,x ,from-offset)]))])))]
                 [load-int64-indirect-stack
                   (lambda (offset from-offset)
                     (lambda (x) ; requires var
                       (%seq
                        (set! ,(%mref ,%sp ,offset) ,(%mref ,x ,from-offset))
                        (set! ,(%mref ,%sp ,(fx+ offset 4)) ,(%mref ,x ,(fx+ from-offset 4))))))]
                 [load-double-reg
                   (lambda (fpreg fp-disp)
                     (lambda (x) ; requires var
                       `(inline ,(make-info-loadfl fpreg) ,%load-double ,x ,%zero (immediate ,fp-disp))))]
                 [load-single-reg
                   (lambda (fpreg fp-disp single?)
                     (lambda (x) ; requires var
                       `(inline ,(make-info-loadfl fpreg) ,(if single? %load-single %load-double->single) ,x ,%zero (immediate ,fp-disp))))]
                 [load-int-reg
                   (lambda (ireg)
                     (lambda (x)
                       `(set! ,ireg ,x)))]
                 [load-int-indirect-reg
                   (lambda (ireg from-offset size)
                     (lambda (x)
                       (case size
                         [(3)
                          (let ([tmp %lr]) ; ok to use %lr here?
                            (%seq
                             (set! ,ireg (inline ,(make-info-load 'integer-16 #f) ,%load ,x ,%zero (immediate ,from-offset)))
                             (set! ,tmp (inline ,(make-info-load 'integer-8 #f) ,%load ,x ,%zero (immediate ,(fx+ from-offset 2))))
                             (set! ,tmp ,(%inline sll ,tmp (immediate 16)))
                             (set! ,ireg ,(%inline + ,ireg ,tmp))))]
                         [else
                          `(set! ,ireg ,(case size
                                          [(1) `(inline ,(make-info-load 'integer-8 #f) ,%load ,x ,%zero (immediate ,from-offset))]
                                          [(2) `(inline ,(make-info-load 'integer-16 #f) ,%load ,x ,%zero (immediate ,from-offset))]
                                          [(4) (%mref ,x ,from-offset)]))])))]
                 [load-int64-indirect-reg
                   (lambda (loreg hireg from-offset)
                     (lambda (x)
                       (%seq
                         (set! ,loreg ,(%mref ,x ,from-offset))
                         (set! ,hireg ,(%mref ,x ,(fx+ from-offset 4))))))]
                 [do-args
                  (lambda (types)
                    ; sgl* is always of even-length, i.e., has a sgl/dbl reg first
                    ; bsgl is set to "b" single (second half of double) if we have one to fill
                    (let loop ([types types] [locs '()] [live* '()] [int* (int-regs)] [sgl* (sgl-regs)] [bsgl #f] [isp 0])
                      (if (null? types)
                          (values isp locs live*)
                          (nanopass-case (Ltype Type) (car types)
                            [(fp-double-float)
                             (if (null? sgl*)
                                 (let ([isp (align 8 isp)])
                                   (loop (cdr types)
                                     (cons (load-double-stack isp) locs)
                                     live* int* '() #f (fx+ isp 8)))
                                 (loop (cdr types)
                                   (cons (load-double-reg (car sgl*) (constant flonum-data-disp)) locs)
                                   live* int* (cddr sgl*) bsgl isp))]
                            [(fp-single-float)
                             (if bsgl
                                 (loop (cdr types)
                                   (cons (load-single-reg bsgl (constant flonum-data-disp) #f) locs)
                                   live* int* sgl* #f isp)
                                 (if (null? sgl*)
                                     (loop (cdr types)
                                       (cons (load-single-stack isp) locs)
                                       live* int* '() #f (fx+ isp 4))
                                     (loop (cdr types)
                                       (cons (load-single-reg (car sgl*) (constant flonum-data-disp) #f) locs)
                                       live* int* (cddr sgl*) (cadr sgl*) isp)))]
                            [(fp-ftd& ,ftd)
                             (let ([size ($ftd-size ftd)]
                                   [members ($ftd->members ftd)]
                                   [combine-loc (lambda (loc f)
                                                  (if loc
                                                      (lambda (x) (%seq ,(loc x) ,(f x)))
                                                      f))])
                               (case ($ftd-alignment ftd)
                                 [(8)
                                  (let* ([int* (if (even? (length int*)) int* (cdr int*))]
                                         [num-members (length members)]
                                         [doubles? (and (fx<= num-members 4)
                                                        (andmap double-member? members))])
                                    ;; Sequence of up to 4 doubles that fits in registers?
                                    (cond
                                     [(and doubles?
                                           (fx>= (length sgl*) (fx* 2 num-members)))
                                      ;; Allocate each double to a register
                                      (let dbl-loop ([size size] [offset 0] [sgl* sgl*] [loc #f])
                                        (cond
                                         [(fx= size 0)
                                          (loop (cdr types) (cons loc locs) live* int* sgl* #f isp)]
                                         [else
                                          (dbl-loop (fx- size 8) (fx+ offset 8) (cddr sgl*)
                                                    (combine-loc loc (load-double-reg (car sgl*) offset)))]))]
                                     [else
                                      ;; General case; for non-doubles, use integer registers while available,
                                      ;;  possibly splitting between registers and stack
                                      (let obj-loop ([size size] [offset 0] [loc #f]
                                                     [live* live*] [int* int*] [isp isp])
                                        (cond
                                         [(fx= size 0)
                                          (loop (cdr types) (cons loc locs) live* int* sgl* bsgl isp)]
                                         [else
                                          (if (or (null? int*) doubles?)
                                              (let ([isp (align 8 isp)])
                                                (obj-loop (fx- size 8) (fx+ offset 8)
                                                          (combine-loc loc (load-int64-indirect-stack isp offset))
                                                          live* int* (fx+ isp 8)))
                                              (obj-loop (fx- size 8) (fx+ offset 8)
                                                        (combine-loc loc (load-int64-indirect-reg (car int*) (cadr int*) offset))
                                                        (cons* (car int*) (cadr int*) live*) (cddr int*) isp))]))]))]
                                 [else
                                    (let* ([num-members (length members)]
                                           [floats? (and (fx<= num-members 4)
                                                         (andmap float-member? members))])
                                      ;; Sequence of up to 4 floats that fits in registers?
                                      (cond
                                       [(and floats?
                                             (fx>= (fx+ (length sgl*) (if bsgl 1 0)) num-members))
                                        ;; Allocate each float to register
                                        (let flt-loop ([size size] [offset 0] [sgl* sgl*] [bsgl bsgl] [loc #f])
                                          (cond
                                           [(fx= size 0)
                                            (loop (cdr types) (cons loc locs) live* int* sgl* bsgl isp)]
                                           [else
                                            (flt-loop (fx- size 4) (fx+ offset 4)
                                                      (if bsgl sgl* (cddr sgl*))
                                                      (if bsgl #f (cadr sgl*))
                                                      (combine-loc loc (load-single-reg (or bsgl (car sgl*)) offset #t)))]))]
                                       [else
                                        ;; General case; use integer registers while available,
                                        ;;  possibly splitting between registers and stack
                                        (let obj-loop ([size size] [offset 0] [loc #f]
                                                       [live* live*] [int* int*] [isp isp])
                                          (cond
                                           [(fx<= size 0)
                                            (loop (cdr types) (cons loc locs) live* int* sgl* bsgl isp)]
                                           [else
                                            (if (or (null? int*) floats?)
                                                (obj-loop (fx- size 4) (fx+ offset 4)
                                                          (combine-loc loc (load-int-indirect-stack isp offset (fxmin size 4)))
                                                          live* int* (fx+ isp 4))
                                                (obj-loop (fx- size 4) (fx+ offset 4)
                                                          (combine-loc loc (load-int-indirect-reg (car int*) offset (fxmin size 4)))
                                                          (cons (car int*) live*) (cdr int*) isp))]))]))]))]
                            [else
                                 (if (null? int*)
                                   [begin
                                     (loop (cdr types)
                                       (cons (load-int-stack isp) locs)
                                       live* '() sgl* bsgl (fx+ isp 4)) ]
                                   [begin
                                     (loop (cdr types)
                                       (cons (load-int-reg (car int*)) locs)
                                       (cons (car int*) live*) (cdr int*) sgl* bsgl isp) ]
                                       )]))))]
                 [add-fill-result
                  (lambda (fill-result-here? result-type args-frame-size e)
                    (cond
                     [fill-result-here?
                      (nanopass-case (Ltype Type) result-type
                        [(fp-ftd& ,ftd)
                         (let* ([members ($ftd->members ftd)]
                                [num-members (length members)]
                                ;; result pointer is stashed on the stack after all arguments:
                                [dest-x %r2]
                                [init-dest-e `(seq ,e (set! ,dest-x ,(%mref ,%sp ,args-frame-size)))])
                           (cond
                            [(and (fx<= num-members 4)
                                  (or (andmap double-member? members)
                                      (andmap float-member? members)))
                             ;; double/float results are in floating-point registers
                             (let ([double? (and (pair? members) (double-member? (car members)))])
                               (let loop ([members members] [sgl* (sgl-regs)] [offset 0] [e init-dest-e])
                                 (cond
                                  [(null? members) e]
                                  [else
                                   (loop (cdr members)
                                         (if double? (cddr sgl*) (cdr sgl*))
                                         (fx+ offset (if double? 8 4))
                                         `(seq
                                           ,e
                                           (inline ,(make-info-loadfl (car sgl*)) ,(if double? %store-double %store-single)
                                                   ,dest-x ,%zero (immediate ,offset))))])))]
                            [else
                             ;; result is in %Cretval and maybe %r1
                             `(seq
                               ,init-dest-e
                               ,(case ($ftd-size ftd)
                                  [(1) `(inline ,(make-info-load 'integer-8 #f) ,%store ,dest-x ,%zero (immediate 0) ,%Cretval)]
                                  [(2) `(inline ,(make-info-load 'integer-16 #f) ,%store ,dest-x ,%zero (immediate 0) ,%Cretval)]
                                  [(3) (%seq
                                        (inline ,(make-info-load 'integer-16 #f) ,%store ,dest-x ,%zero (immediate 0) ,%Cretval)
                                        (set! ,%Cretval ,(%inline srl ,%Cretval (immediate 16)))
                                        (inline ,(make-info-load 'integer-8 #f) ,%store ,dest-x ,%zero (immediate 2) ,%Cretval))]
                                  [(4) `(set! ,(%mref ,dest-x ,0) ,%Cretval)]
                                  [(8) `(seq
                                         (set! ,(%mref ,dest-x ,0) ,%Cretval)
                                         (set! ,(%mref ,dest-x ,4) ,%r1))]))]))])]
                     [else e]))])
          (lambda (info)
            (safe-assert (reg-callee-save? %tc)) ; no need to save-restore
            (let* ([arg-type* (info-foreign-arg-type* info)]
                   [result-type (info-foreign-result-type info)]
                   [fill-result-here? (indirect-result-that-fits-in-registers? result-type)])
              (with-values (do-args (if fill-result-here? (cdr arg-type*) arg-type*))
                (lambda (args-frame-size locs live*)
                  (let* ([frame-size (align 16 (+ args-frame-size
                                                 (if fill-result-here?
                                                     4
                                                     0)))]
                         [adjust-frame (lambda (op)
                                         (lambda ()
                                           (if (fx= frame-size 0)
                                               `(nop)
                                               `(set! ,%sp (inline ,null-info ,op ,%sp (immediate ,frame-size))))))])
                    (values
                      (adjust-frame %-)
                      (let ([locs (reverse locs)])
                        (cond
                         [fill-result-here?
                          ;; stash extra argument on the stack to be retrieved after call and filled with the result:
                          (cons (load-int-stack args-frame-size) locs)]
                         [else locs]))
                      (lambda (t0)
                        (add-fill-result fill-result-here? result-type args-frame-size
                          `(inline ,(make-info-kill*-live* (reg-list %r0) live*) ,%c-call ,t0)))
                      (nanopass-case (Ltype Type) result-type
                        [(fp-double-float)
                         (lambda (lvalue)
                           `(inline ,(make-info-loadfl %Cfpretval) ,%store-double ,lvalue ,%zero
                              ,(%constant flonum-data-disp)))]
                        [(fp-single-float)
                         (lambda (lvalue)
                           `(inline ,(make-info-loadfl %Cfpretval) ,%store-single->double ,lvalue ,%zero
                              ,(%constant flonum-data-disp)))]
                        [(fp-integer ,bits)
                         (case bits
                           [(8) (lambda (lvalue) `(set! ,lvalue ,(%inline sext8 ,%r0)))]
                           [(16) (lambda (lvalue) `(set! ,lvalue ,(%inline sext16 ,%r0)))]
                           [(32) (lambda (lvalue) `(set! ,lvalue ,(%inline sext32 ,%r0)))]
                           [(64) (lambda (lvalue) `(set! ,lvalue ,%r0))]
                           [else (sorry! who "unexpected asm-foreign-procedures fp-integer size ~s" bits)])]
                        [(fp-unsigned ,bits)
                         (case bits
                           [(8) (lambda (lvalue) `(set! ,lvalue ,(%inline zext8 ,%r0)))]
                           [(16) (lambda (lvalue) `(set! ,lvalue ,(%inline zext16 ,%r0)))]
                           [(32) (lambda (lvalue) `(set! ,lvalue ,(%inline zext32 ,%r0)))]
                           [(64) (lambda (lvalue) `(set! ,lvalue ,%r0))]
                           [else (sorry! who "unexpected asm-foreign-procedures fp-unsigned size ~s" bits)])]
                        [else
                         (lambda (lvalue) `(set! ,lvalue ,%r0))])
                      (adjust-frame %+)))
                  )))))))

; TODO update this and its dependents to be aarch64
; Reference the Procedure Call Standard for the ARM 64-bit Architecture (pg 18)

    (define-who asm-foreign-callable
      #|
        Frame Layout
                   +---------------------------+
                   |                           |
                   |    incoming stack args    |
  sp+36+R+X+Y+Z+W: |                           |
                   +---------------------------+<- 8-byte boundary
                   |                           |
                   |    saved int reg args     | 0-4 words
    sp+36+R+X+Y+Z: |                           |
                   +---------------------------+
                   |                           |
                   |   pad word if necessary   | 0-1 words
      sp+36+R+X+Y: |                           |
                   +---------------------------+<- 8-byte boundary
                   |                           |
                   |   saved float reg args    | 0-16 words
        sp+36+R+X: |                           |
                   +---------------------------+<- 8-byte boundary
                   |                           |
                   |      &-return space       | up to 8 words
          sp+36+R: |                           |
                   +---------------------------+<- 8-byte boundary
                   |                           |
                   |   pad word if necessary   | 0-1 words
            sp+36: |                           |
                   +---------------------------+
                   |                           |
                   |   callee-save regs + lr   | 9 words
             sp+0: |                           |
                   +---------------------------+<- 8-byte boundary

      X = 0 or 4 (depending on whether pad is present)
      Y = int-reg-bytes
      Z = float-reg-bytes
      |#
      (with-output-language (L13 Effect)
        (let ()
          (define load-double-stack
            (lambda (offset)
              (lambda (x) ; requires var
                (%seq
                  (inline ,(make-info-loadfl %flreg1) ,%load-double ,%sp ,%zero (immediate ,offset))
                  (inline ,(make-info-loadfl %flreg1) ,%store-double ,x ,%zero ,(%constant flonum-data-disp))))))
          (define load-single-stack
            (lambda (offset)
              (lambda (x) ; requires var
                (%seq
                  (inline ,(make-info-loadfl %flreg1) ,%load-single->double ,%sp ,%zero (immediate ,offset))
                  (inline ,(make-info-loadfl %flreg1) ,%store-double ,x ,%zero ,(%constant flonum-data-disp))))))
          (define load-int-stack
            (lambda (type offset)
              (lambda (lvalue)
                (nanopass-case (Ltype Type) type
                  [(fp-integer ,bits)
                   (case bits
                     [(8) `(set! ,lvalue (inline ,(make-info-load 'integer-8 #f) ,%load ,%sp ,%zero (immediate ,offset)))]
                     [(16) `(set! ,lvalue (inline ,(make-info-load 'integer-16 #f) ,%load ,%sp ,%zero (immediate ,offset)))]
                     [(32) `(set! ,lvalue ,(%mref ,%sp ,offset))]
                     [else (sorry! who "unexpected load-int-stack fp-integer size ~s" bits)])]
                  [(fp-unsigned ,bits)
                   (case bits
                     [(8) `(set! ,lvalue (inline ,(make-info-load 'unsigned-8 #f) ,%load ,%sp ,%zero (immediate ,offset)))]
                     [(16) `(set! ,lvalue (inline ,(make-info-load 'unsigned-16 #f) ,%load ,%sp ,%zero (immediate ,offset)))]
                     [(32) `(set! ,lvalue ,(%mref ,%sp ,offset))]
                     [else (sorry! who "unexpected load-int-stack fp-unsigned size ~s" bits)])]
                  [else `(set! ,lvalue ,(%mref ,%sp ,offset))]))))
          (define load-int64-stack
            (lambda (offset)
              (lambda (lolvalue hilvalue)
                (%seq
                  (set! ,lolvalue ,(%mref ,%sp ,offset))
                  (set! ,hilvalue ,(%mref ,%sp ,(fx+ offset 4)))))))
          (define load-stack-address
            (lambda (offset)
              (lambda (lvalue)
                `(set! ,lvalue ,(%inline + ,%sp (immediate ,offset))))))
          (define count-reg-args
            (lambda (types synthesize-first?)
              ; bsgl? is #t iff we have a "b" single (second half of double) float reg to fill
              (let f ([types types] [iint (if synthesize-first? -1 0)] [idbl 0] [bsgl? #f])
                (if (null? types)
                    (values iint idbl)
                    (nanopass-case (Ltype Type) (car types)
                      [(fp-double-float)
                       (if (fx< idbl 8)
                           (f (cdr types) iint (fx+ idbl 1) bsgl?)
                           (f (cdr types) iint idbl #f))]
                      [(fp-single-float)
                       (if bsgl?
                           (f (cdr types) iint idbl #f)
                           (if (fx< idbl 8)
                               (f (cdr types) iint (fx+ idbl 1) #t)
                               (f (cdr types) iint idbl #f)))]
                      [(fp-ftd& ,ftd)
                       (let* ([size ($ftd-size ftd)]
                              [members ($ftd->members ftd)]
                              [num-members (length members)])
                         (cond
                          [(and (fx<= num-members 4)
                                (andmap double-member? members))
                           ;; doubles are either in registers or all on stack
                           (if (fx<= (fx+ idbl num-members) 8)
                               (f (cdr types) iint (fx+ idbl num-members) #f)
                               ;; no more floating-point registers should be used, but ok if we count more
                               (f (cdr types) iint idbl #f))]
                          [(and (fx<= num-members 4)
                                (andmap float-member? members))
                           ;; floats are either in registers or all on stack
                           (let ([amt (fxsrl (align 2 (fx- num-members (if bsgl? 1 0))) 1)])
                             (if (fx<= (fx+ idbl amt) 8)
                                 (let ([odd-floats? (fxodd? num-members)])
                                   (if bsgl?
                                       (f (cdr types) iint (+ idbl amt) (not odd-floats?))
                                       (f (cdr types) iint (+ idbl amt) odd-floats?)))
                                 ;; no more floating-point registers should be used, but ok if we count more
                                 (f (cdr types) iint idbl #f)))]
                          [(fx= 8 ($ftd-alignment ftd))
                           (f (cdr types) (fxmin 4 (fx+ (align 2 iint) (fxsrl size 2))) idbl bsgl?)]
                          [else
                           (let ([size (align 4 size)])
                             (f (cdr types) (fxmin 4 (fx+ iint (fxsrl size 2))) idbl bsgl?))]))]
                      [else
                       (if (nanopass-case (Ltype Type) (car types)
                             [(fp-integer ,bits) (fx= bits 64)]
                             [(fp-unsigned ,bits) (fx= bits 64)]
                             [else #f])
                           (let ([iint (align 2 iint)])
                             (f (cdr types) (if (fx< iint 4) (fx+ iint 2) iint) idbl bsgl?))
                           (f (cdr types) (if (fx< iint 4) (fx+ iint 1) iint) idbl bsgl?))])))))
          (define do-stack
            ; all of the args are on the stack at this point, though not contiguous since
            ; we push all of the int reg args with one push instruction and all of the
            ; float reg args with another (v)push instruction; the saved int regs
            ; continue on into the stack variables, which is convenient when a struct
            ; argument is split across registers and the stack
            (lambda (types saved-reg-bytes pre-pad-bytes return-bytes float-reg-bytes post-pad-bytes int-reg-bytes
                           synthesize-first?)
              (let* ([return-space-offset (fx+ saved-reg-bytes pre-pad-bytes)]
                     [float-reg-offset (fx+ return-space-offset return-bytes)]
                     [int-reg-offset (fx+ float-reg-offset float-reg-bytes post-pad-bytes)]
                     [stack-arg-offset (fx+ int-reg-offset int-reg-bytes)])
                (let loop ([types (if synthesize-first? (cdr types) types)]
                           [locs '()]
                           [iint 0]
                           [idbl 0]
                           [bsgl-offset #f]
                           [int-reg-offset int-reg-offset]
                           [float-reg-offset float-reg-offset]
                           [stack-arg-offset stack-arg-offset])
                  (if (null? types)
                      (let ([locs (reverse locs)])
                        (if synthesize-first?
                            (cons (load-stack-address return-space-offset)
                                  locs)
                            locs))
                      (nanopass-case (Ltype Type) (car types)
                        [(fp-double-float)
                         (if (< idbl 8)
                             (loop (cdr types)
                               (cons (load-double-stack float-reg-offset) locs)
                               iint (fx+ idbl 1) bsgl-offset int-reg-offset (fx+ float-reg-offset 8) stack-arg-offset)
                             (let ([stack-arg-offset (align 8 stack-arg-offset)])
                               (loop (cdr types)
                                 (cons (load-double-stack stack-arg-offset) locs)
                                 iint 8 #f int-reg-offset float-reg-offset (fx+ stack-arg-offset 8))))]
                        [(fp-single-float)
                         (if bsgl-offset
                             (loop (cdr types)
                               (cons (load-single-stack bsgl-offset) locs)
                               iint idbl #f int-reg-offset float-reg-offset stack-arg-offset)
                             (if (< idbl 8)
                                 (loop (cdr types)
                                   ; with big-endian ARM might need to adjust offset +/- 4 since pair of
                                   ; single floats in a pushed double float might be reversed
                                   (cons (load-single-stack float-reg-offset) locs)
                                   iint (fx+ idbl 1) (fx+ float-reg-offset 4) int-reg-offset (fx+ float-reg-offset 8) stack-arg-offset)
                                 (loop (cdr types)
                                   (cons (load-single-stack stack-arg-offset) locs)
                                   iint 8 #f int-reg-offset float-reg-offset (fx+ stack-arg-offset 4))))]
                        [(fp-ftd& ,ftd)
                         (let* ([size ($ftd-size ftd)]
                                [members ($ftd->members ftd)]
                                [num-members (length members)])
                           (cond
                            [(and (fx<= num-members 4)
                                  (andmap double-member? members))
                             ;; doubles are either in registers or all on stack
                             (if (fx<= (fx+ idbl num-members) 8)
                                 (loop (cdr types)
                                   (cons (load-stack-address float-reg-offset) locs)
                                   iint (fx+ idbl num-members) #f int-reg-offset (fx+ float-reg-offset size) stack-arg-offset)
                                 (let ([stack-arg-offset (align 8 stack-arg-offset)])
                                   (loop (cdr types)
                                     (cons (load-stack-address stack-arg-offset) locs)
                                     iint 8 #f int-reg-offset #f (fx+ stack-arg-offset size))))]
                            [(and (fx<= num-members 4)
                                  (andmap float-member? members))
                             ;; floats are either in registers or all on stack
                             (let ([amt (fxsrl (align 2 (fx- num-members (if bsgl-offset 1 0))) 1)])
                               (if (fx<= (fx+ idbl amt) 8)
                                   (let ([odd-floats? (fxodd? num-members)])
                                     (if bsgl-offset
                                         (let ([dbl-size (align 8 (fx- size 4))])
                                           (loop (cdr types)
                                             (cons (load-stack-address bsgl-offset) locs)
                                             iint (fx+ idbl amt) (if odd-floats? #f (+ bsgl-offset size)) int-reg-offset
                                             (fx+ float-reg-offset dbl-size) stack-arg-offset))
                                         (let ([dbl-size (align 8 size)])
                                           (loop (cdr types)
                                             (cons (load-stack-address float-reg-offset) locs)
                                             iint (fx+ idbl amt) (and odd-floats? (fx+ float-reg-offset size)) int-reg-offset
                                             (fx+ float-reg-offset dbl-size) stack-arg-offset))))
                                   (loop (cdr types)
                                     (cons (load-stack-address stack-arg-offset) locs)
                                     iint 8 #f int-reg-offset float-reg-offset (fx+ stack-arg-offset size))))]
                            [(fx= 8 ($ftd-alignment ftd))
                             (let ([int-reg-offset (if (fxeven? iint) int-reg-offset (fx+ int-reg-offset 4))]
                                   [iint (align 2 iint)]
                                   [amt (fxsrl size 2)])
                               (if (fx< iint 4) ; argument starts in registers, may continue on stack
                                   (loop (cdr types)
                                     (cons (load-stack-address int-reg-offset) locs)
                                     (fxmin 4 (fx+ iint amt)) idbl bsgl-offset (fx+ int-reg-offset size) float-reg-offset
                                     (fx+ stack-arg-offset (fxmax 0 (fx* 4 (fx- (fx+ iint amt) 4)))))
                                   (let ([stack-arg-offset (align 8 stack-arg-offset)])
                                     (loop (cdr types)
                                       (cons (load-stack-address stack-arg-offset) locs)
                                       iint idbl bsgl-offset int-reg-offset float-reg-offset (fx+ stack-arg-offset size)))))]
                            [else
                             (let* ([size (align 4 size)]
                                    [amt (fxsrl size 2)])
                               (if (fx< iint 4) ; argument starts in registers, may continue on stack
                                   (loop (cdr types)
                                     (cons (load-stack-address int-reg-offset) locs)
                                     (fxmin 4 (fx+ iint amt)) idbl bsgl-offset (fx+ int-reg-offset size) float-reg-offset
                                     (fx+ stack-arg-offset (fxmax 0 (fx* 4 (fx- (fx+ iint amt) 4)))))
                                   (loop (cdr types)
                                     (cons (load-stack-address stack-arg-offset) locs)
                                     iint idbl bsgl-offset int-reg-offset float-reg-offset (fx+ stack-arg-offset size))))]))]
                        [else
                         (if (nanopass-case (Ltype Type) (car types)
                               [(fp-integer ,bits) (fx= bits 64)]
                               [(fp-unsigned ,bits) (fx= bits 64)]
                               [else #f])
                             (let ([int-reg-offset (if (fxeven? iint) int-reg-offset (fx+ int-reg-offset 4))]
                                   [iint (align 2 iint)])
                               (if (fx= iint 4)
                                   (let ([stack-arg-offset (align 8 stack-arg-offset)])
                                     (loop (cdr types)
                                       (cons (load-int64-stack stack-arg-offset) locs)
                                       iint idbl bsgl-offset int-reg-offset float-reg-offset (fx+ stack-arg-offset 8)))
                                   (loop (cdr types)
                                     (cons (load-int64-stack int-reg-offset) locs)
                                     (fx+ iint 2) idbl bsgl-offset (fx+ int-reg-offset 8) float-reg-offset stack-arg-offset)))
                             (if (fx= iint 4)
                                 (loop (cdr types)
                                   (cons (load-int-stack (car types) stack-arg-offset) locs)
                                   iint idbl bsgl-offset int-reg-offset float-reg-offset (fx+ stack-arg-offset 4))
                                 (loop (cdr types)
                                   (cons (load-int-stack (car types) int-reg-offset) locs)
                                   (fx+ iint 1) idbl bsgl-offset (fx+ int-reg-offset 4) float-reg-offset stack-arg-offset)))]))))))
          (define do-result
            (lambda (result-type synthesize-first? return-stack-offset)
              (nanopass-case (Ltype Type) result-type
                [(fp-ftd& ,ftd)
                 (let* ([members ($ftd->members ftd)]
                        [num-members (length members)])
                   (cond
                    [(and (fx<= 1 num-members 4)
                          (or (andmap double-member? members)
                              (andmap float-member? members)))
                     ;; double/float results returned in floating-point registers
                     (values
                      (lambda ()
                        (let ([double? (and (pair? members) (double-member? (car members)))])
                          (let loop ([members members] [sgl* (sgl-regs)] [offset return-stack-offset] [e #f])
                            (cond
                             [(null? members) e]
                             [else
                              (loop (cdr members)
                                    (if double? (cddr sgl*) (cdr sgl*))
                                    (fx+ offset (if double? 8 4))
                                    (let ([new-e
                                           `(inline ,(make-info-loadfl (car sgl*)) ,(if double? %load-double %load-single)
                                                    ,%sp ,%zero (immediate ,offset))])
                                      (if e `(seq ,e ,new-e) new-e)))]))))
                      '()
                      ($ftd-size ftd))]
                    [else
                     (case ($ftd-size ftd)
                       [(8)
                        (values (lambda ()
                                  `(seq
                                    (set! ,%Cretval ,(%mref ,%sp ,return-stack-offset))
                                    (set! ,%r1 ,(%mref ,%sp ,(fx+ 4 return-stack-offset)))))
                                (list %Cretval %r1)
                                8)]
                       [else
                        (values (lambda ()
                                  `(set! ,%Cretval ,(%mref ,%sp ,return-stack-offset)))
                                (list %Cretval %r1)
                                4)])]))]
                [(fp-double-float)
                 (values (lambda (rhs)
                           `(inline ,(make-info-loadfl %Cfpretval) ,%load-double
                                    ,rhs ,%zero ,(%constant flonum-data-disp)))
                         '()
                         0)]
                [(fp-single-float)
                 (values (lambda (rhs)
                           `(inline ,(make-info-loadfl %Cfpretval) ,%load-double->single
                                    ,rhs ,%zero ,(%constant flonum-data-disp)))
                         '()
                         0)]
                [(fp-void)
                 (values (lambda () `(nop))
                         '()
                         0)]
                [else
                 (values (lambda (x)
                             `(set! ,%Cretval ,x))
                           (list %Cretval %r1)
                           0)])))
          (lambda (info)
            (define callee-save-regs+lr (list %r19 %r20 %r21 %r22 %r23 %r24 %r25 %r26 %r27 %r28 %lr))
            (define isaved (length callee-save-regs+lr))
            (let* ([arg-type* (info-foreign-arg-type* info)]
                   [result-type (info-foreign-result-type info)]
                   [synthesize-first? (indirect-result-that-fits-in-registers? result-type)])
              (let-values ([(iint idbl) (count-reg-args arg-type* synthesize-first?)])
                (let ([saved-reg-bytes (fx* isaved 4)]
                      [pre-pad-bytes (if (fxeven? isaved) 0 4)]
                      [int-reg-bytes (fx* iint 4)]
                      [post-pad-bytes (if (fxeven? iint) 0 4)]
                      [float-reg-bytes (fx* idbl 8)])
                  (let-values ([(get-result result-regs return-bytes) (do-result result-type synthesize-first?
                                                                                 (fx+ saved-reg-bytes pre-pad-bytes))])
                    (let ([return-bytes (align 8 return-bytes)])
                      (values
                       (lambda ()
                          (%seq
                            ; save argument register values to the stack so we don't lose the values
                            ; across possible calls to C while setting up the tc and allocating memory
                            ,(if (fx= iint 0) `(nop) `(inline ,(make-info-kill*-live* '() (list-head (list %Carg1 %Carg2 %Carg3 %Carg4) iint)) ,%push-multiple))
                            ; pad if necessary to force 8-byte boundary, and make room for indirect return:
                            ,(let ([len (+ post-pad-bytes return-bytes)])
                               (if (fx= len 0) `(nop) `(set! ,%sp ,(%inline - ,%sp (immediate ,len)))))
                            ,(if (fx= idbl 0) `(nop) `(inline ,(make-info-vpush %Cfparg1 idbl) ,%vpush-multiple))
                            ; pad if necessary to force 8-byte boundardy after saving callee-save-regs+lr
                            ,(if (fx= pre-pad-bytes 0) `(nop) `(set! ,%sp ,(%inline - ,%sp (immediate 4))))

                            ; save the callee save registers & return address
                            (inline ,(make-info-kill*-live* '() callee-save-regs+lr) ,%push-multiple)

                            ; set up tc for benefit of argument-conversion code, which might allocate
                            ,(if-feature pthreads
                               (%seq
                                 (set! ,%r0 ,(%inline get-tc))
                                 (set! ,%tc ,%r0))
                               `(set! ,%tc (literal ,(make-info-literal #f 'entry (lookup-c-entry thread-context) 0))))))
                        ; list of procedures that marshal arguments from their C stack locations
                        ; to the Scheme argument locations
                        (do-stack arg-type* saved-reg-bytes pre-pad-bytes return-bytes float-reg-bytes post-pad-bytes int-reg-bytes
                                  synthesize-first?)
                        get-result
                        (lambda ()
                          (in-context Tail
                            (%seq
                              ; restore the callee save registers
                              (inline ,(make-info-kill* callee-save-regs+lr) ,%pop-multiple)
                              ; deallocate space for pad & arg reg values
                              (set! ,%sp ,(%inline + ,%sp (immediate ,(fx+ pre-pad-bytes int-reg-bytes post-pad-bytes float-reg-bytes))))
                              ; done
                              (asm-c-return ,null-info ,callee-save-regs+lr ... ,result-regs ...)))))))))))))))
)
