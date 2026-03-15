#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 5.
 Due: 3/12 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 5".

 The group members are:

 Mingqi Lu
 
 To make sure that we are all on the same page, build the latest
 version of ACL2s, as per HWK1. You are going to be using SBCL, which
 you already have, due to the build process in

 Next, install quicklisp. See https://www.quicklisp.org/beta/. 

 To make sure everything is OK with quicklisp and to initialize it,
 start sbcl and issue the following commands

 (load "~/quicklisp/setup.lisp")
 (ql:quickload :trivia)
 (ql:quickload :cl-ppcre)
 (ql:quickload :let-plus)
 (setf ppcre:*allow-named-registers* t)
 (exit) 

 Next, clone the ACL2s interface repository:
 (https) https://gitlab.com/acl2s/external-tool-support/interface.git
 (ssh)   git@gitlab.com:acl2s/external-tool-support/interface.git

 This repository includes scripts for interfacing with ACL2s from lisp.
 Put this directory in the ...books/acl2s/ of your ACL2 repository, or 
 use a symbolic link.

 Now, certify the books, by going to ...books/acl2s/interface and
 typing 

 "cert.pl -j 4 top"

 Look at the documentation for cert.pl. If cert.pl isn't in your path,
 then use

 "/Users/lumingqi/acl2-work/acl2/books/build/cert.pl -j 4 top"
 "...books/build/cert.pl -j 4 top"

 The "-j 4" option indicates that you want to run up to 4 instances of
 ACL2 in parallel. Set this number to the number of cores you have.

 As mentioned at the beginning of the semester, some of the code we
 will write is in Lisp. You can find the common lisp manual online in
 various formats by searching for "common lisp manual."

 Other references that you might find useful and are available online
 include
 
 - Common Lisp: A Gentle Introduction to Symbolic Computation by David
   Touretzky
 - ANSI Common Lisp by Paul Graham
 
|#

(in-package "ACL2S")

;; Now for some ACL2s systems programming.

;; This book is already included in ACL2s, so this is a no-op, but I'm
;; putting it here so that you can see where the code for ACL2s
;; systems programming is coming from.
(include-book "acl2s/interface/top" :dir :system)
(set-ignore-ok t)

;; This gets us to raw lisp.
:q

#| 

 The interface books provide us with the ability to call the theorem
 prover within lisp, which will be useful in checking your code. 

 Here are some examples you can try. acl2s-compute is the form you use
 when you are using ACL2s to compute something, e.g., running a
 function on some input. acl2s-query is the form you use when you are
 querying ACL2s, e.g., a property without a name. If the property has
 a name, then that is not a query, but an event and you have to use
 acl2s-event.

 (acl2s-compute '(+ 1 2))
 (acl2s-query '(property (p q :all)
                 (iff (=> p q)
                      (v (! p) q))))
|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. Links to online documentation
 for the software libraries are provided below.

|#

(load "~/quicklisp/setup.lisp")

; See https://lispcookbook.github.io/cl-cookbook/pattern_matching.html
(ql:quickload :trivia)

; See https://www.quicklisp.org/beta/UNOFFICIAL/docs/cl-ppcre/doc/index.html
(ql:quickload :cl-ppcre)

; See https://github.com/sharplispers/let-plus
(ql:quickload :let-plus)

(setf ppcre:*allow-named-registers* t)

#|
 
 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

;; We import acl2s-compute and acl2s-query into our package.

(import 'acl2s-interface-internal::(acl2s-compute acl2s-query))

#|
 
 We have a list of the propositional operators and information about
 them. 

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity. 
 
 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s. 

|# 

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t)
    (not     :arity 1 :identity -   :idem nil :sink -)
    (implies :arity 2 :identity -   :idem nil :sink -)
    (iff     :arity - :identity t   :idem nil :sink -)
    (xor     :arity - :identity nil :idem nil :sink -)
    (if      :arity 3 :identity -   :idem nil :sink -)))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|# 

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

(defun key-alist->val (k l)
  (let* ((in (assoc k l :test #'equal)))
    (values (cdr in) in)))

(key-alist->val 'iff *p-ops*)

(defun key-list->val (k l)
  (let* ((in (member k l :test #'equal)))
    (values (cadr in) in)))

(key-list->val ':arity  (key-alist->val 'iff *p-ops*))

(defun pfun-key->val (fun key)
  (key-list->val key (key-alist->val fun *p-ops*)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defparameter *booleans* '(t nil))

(defun booleanp (x)
  (in x *booleans*))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (key-list->val :arity (key-alist->val pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))

#|
 
 Here is the definition of a propositional formula. 
 
|#

(defun p-formulap (f)
  (match f
    ((type boolean) t) ; don't need this case, but here for emphasis
    ((type symbol) t)
    ((list* pop args)
     (if (p-funp pop)
         (pfun-argsp pop args)
       t))
    (_ nil)))

#|
 
 Notice that in addition to propositional variables, we allow atoms
 such as (foo x). 

 Here are some assertions (see the common lisp manual).
 
|#

(assert (p-formulap '(and)))
(assert (p-formulap '(and x y z)))
(assert (p-formulap '(and t nil)))
(assert (not (p-formulap '(implies x t nil))))
(assert (p-formulap 'q))
(assert (p-formulap '(implies (foo x) (bar y))))
(assert (p-formulap '(iff p q r s t)))
(assert (p-formulap '(xor p q r s t)))
(assert (not (p-formulap '(if p q r t))))

#|

 The propositional skeleton is what remains when we remove
 non-variable atoms.

|#

(defun p-skeleton-args (args amap acc)
  (if (endp args)
      (values (reverse acc) amap)
    (let+ (((&values na namap)
            (p-skeleton (car args) amap)))
          (p-skeleton-args (cdr args) namap (cons na acc)))))

(defun p-skeleton (f &optional amap) ;amap is nil if not specified
  (match f
    ((type symbol) (values f amap))
    ((list* pop args)
     (if (p-funp pop)
         (let+ (((&values nargs namap)
                 (p-skeleton-args args amap nil)))
               (values (cons pop nargs) namap))
       (let ((geta (key-alist->val f amap)))
         (if geta
             (values geta amap)
           (let ((gen (gentemp "P")))
             (values gen (acons f gen amap)))))))
    (_ (error "Not a p-formula"))))

#|

 Here are some examples you can try.

(p-skeleton
 '(or p q r s))

(p-skeleton
 '(iff q r))

(p-skeleton
 '(or p (iff q r)))

(p-skeleton
 '(or p (iff q r) (and p q p) (if p (and p q) (or p q))))

(p-skeleton
 '(iff p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(xor p p q (foo t nil) (foo t nil) (or p q)))

(p-skeleton
 '(iff p p q (foo t r) (foo s nil) (or p q)))

(p-skeleton
 '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))

|#

#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun nary-to-2ary (fun args)
  (let ((identity (pfun-key->val fun :identity)))
    (match args
      (nil identity)
      ((list x) (to-acl2s x))
      (_ (acl2s::xxxjoin (to-acl2s fun) (mapcar #'to-acl2s args))))))

(defun to-acl2s (f)
  (let ((s (p-skeleton f)))
    (match s
      ((type symbol) (intern (symbol-name f) "ACL2S"))
      ((cons x xs)
       (if (in x '(iff xor))
           (nary-to-2ary x xs)
         (mapcar #'to-acl2s f)))
      (_ f))))

(to-acl2s '(and a b c d))
(to-acl2s '(iff a b c d))
(to-acl2s '(xor a b c d))

(defun pvars- (f)
  (match f
    ((type boolean) nil)
    ((type symbol) (list f))
    ((list* op args)
     (and (p-funp op)
          (reduce #'append (mapcar #'pvars- args))))))

(defun pvars (f) (remove-dups (pvars- f)))

(pvars '(and t (iff nil) (iff t nil t nil) p q))
(pvars '(iff p p q (foo t r) (foo s nil) (or p q)))
(pvars '(if p q (or r (foo t s) (and (not q)))))

(defun boolean-hyps (l)
  (reduce #'append
          (mapcar #'(lambda (x) `(,x :bool))
                  (mapcar #'to-acl2s l))))

(boolean-hyps '(p q r))

(defun acl2s-check-equal (f g)
  (let* ((iff `(iff ,f ,g))
         (siff (p-skeleton iff))
   (pvars (pvars siff))
   (aiff (to-acl2s siff))
         (af (second aiff))
         (ag (third aiff))
         (bhyps (boolean-hyps pvars)))
    (acl2s-query
     `(acl2s::property ,bhyps (acl2s::iff ,af ,ag)))))

;; And some simple examples.
(acl2s-check-equal 'p 'p)
(acl2s-check-equal 'p 'q)

; Here is how to check if the query succeeded
(assert (== (car (acl2s-check-equal 'p 'p)) nil))

; So, here's a useful function
(defun assert-acl2s-equal (f g)
  (assert (== (car (acl2s-check-equal f g)) nil)))

(assert-acl2s-equal 'p 'p)

#|

; This will lead to an error. Try it.
; In sbcl :top gets you out of the debugger.
(assert-acl2s-equal 'p 'q)

|#

; Here is how we can use ACL2s to check our code.
(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c))))))
  (assert-acl2s-equal x t))

(let* ((x '(or (foo a (g a c)) (g a c) (not (foo a (g a c)))))
       (sx (p-skeleton x)))
  (assert-acl2s-equal sx t))


#|
 
 Question 1. (25 pts)

 Define function, p-simplify that given a propositional formula
 returns an equivalent propositional formula with the following
 properties. 

 A. The skeleton of the returned formula is either a constant or does
 not include any constants. For example:

 (and p t (foo t nil) q) should be simplified to (and p (foo t nil) q)
 (and p t (foo t b) nil) should be simplified to nil

 B. Flatten expressions, e.g.:

 (and p q (and r s) (or u v)) is not flat, but this is
 (and p q r s (or u v))

 A formula of the form (op ...) where op is a Boolean operator of
 arbitrary arity (ie, and, or, iff) applied to 0 or 1 arguments is not
 flat. For example, replace (and) with t. 

 A formula of the form (op ... (op ...)) where op is a Boolean
 operator of arbitrary arity is not flat. For example, replace (and p
 q (and r s)) with (and p q r s).

 C. If there is Boolean constant s s.t. If (op ... s ...) = s, then we
 say that s is a sink of op. For example t is a sink of or. A formula
 is sink-free if no such subformulas remain. The returned formula
 should be sink-free.

 D. Simplify your formulas so that no subexpressions of the following
 form remain
 
 (not (not f))
 (not (iff ...))
 (not (xor ...))

 E. Apply Shannon expansions in 61-67.

 For example

 (and (or p q) (or r q p) p) should be simplified to

 p because (and (or t q) (or r q t) p) is (and t t p) is p

 F. Simplify formulas so that no subexpressions of the form

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or x y (foo a b) z (not (foo a b)) w) should be simplified to 

 t 

 Make sure that your algorithm is as efficient as you can make
 it. The idea is to use this simplification as a preprocessing step,
 so it needs to be fast. 

 You are not required to perform any other simplifications beyond
 those specified above. If you do, your simplifier must be guaranteed
 to always return something that is simpler that what would be
 returned if you just implemented the simplifications explicitly
 requested. Also, if you implement any other simplifications, your
 algorithm must run in comparable time (eg, no validity checking).
 Notice some simple consequences. You cannot transform the formula to
 an equivalent formula that uses a small subset of the
 connectives (such as not/and). If you do that, the formula you get
 can be exponentially larger than the input formula, as we have
 discussed in class. Notice that even negation normal form (NNF) can
 increase the size of a formula. Such considerations are important
 when you use Tseitin, because experience has shown that even
 transformations such as NNF are usually a bad idea when generating
 CNF, as they tend to result in CNF formulas that take modern solvers
 longer to analyze.

 Test your definition with assert-acl2s-equal using at least 10
 propositional formulas that include non-variable atoms, all of the
 operators, deeply nested formulas, etc.

 
|#

(defun arbitrary-arity-p (op)
  (== (pfun-key->val op :arity) '-))

(defun simplify-fixed-arity-op (op sargs)
  (cond
    ((equal op 'not)
     (let ((x (first sargs)))
       (cond
         ((booleanp x) (if x nil t))
         ((and (consp x) (equal (car x) 'not))
          (p-simplify (cadr x)))
         ((and (consp x) (equal (car x) 'iff))
          (p-simplify
           (cons 'xor
                 (mapcar (lambda (e) `(not ,e)) (cdr x)))))
         ((and (consp x) (equal (car x) 'xor))
          (p-simplify
           (cons 'iff
                 (mapcar (lambda (e) `(not ,e)) (cdr x)))))
         (t `(not ,x)))))
    ((equal op 'implies)
     (let ((a (first sargs))
           (b (second sargs)))
       (cond
         ((equal a t) b)
         ((equal a nil) t)
         ((equal b t) t)
         ((equal b nil) (p-simplify `(not ,a)))
         ((equal a b) t)
         ((equal b `(not ,a)) b)
         ((equal a `(not ,b)) b)
         (t `(implies ,a ,b)))))
    ((equal op 'if)
     (let ((c (first sargs))
           (a (second sargs))
           (b (third sargs)))
       (cond
         ((equal c t) a)
         ((equal c nil) b)
         ((equal a b) a)
         ((and (equal a t) (equal b nil)) c)
         ((and (equal a nil) (equal b t))
          (p-simplify `(not ,c)))
         ((equal a t) (p-simplify `(or ,c ,b)))
         ((equal a nil) (p-simplify `(and (not ,c) ,b)))
         ((equal b t) (p-simplify `(or (not ,c) ,a)))
         ((equal b nil) (p-simplify `(and ,c ,a)))
         (t `(if ,c ,a ,b)))))
    (t
     (cons op sargs))))

(defun flatten-same-op-args (op args)
  (reduce #'append
          (mapcar (lambda (a)
                    (match a
                      ((list* op2 subargs)
                       (if (equal op op2)
                           subargs
                         (list a)))
                      (_ (list a))))
                  args)
          :initial-value nil))

(defun has-sink-p (op args)
  (let ((sink (pfun-key->val op :sink)))
    (and (not (equal sink '-))
         (in sink args))))

(defun remove-identities (op args)
  (let ((id (pfun-key->val op :identity)))
    (if (equal id '-)
        args
      (remove id args :test #'equal))))

(defun has-complementary-literals-p (args)
  (some (lambda (x)
          (some (lambda (y)
                  (or (equal y `(not ,x)) (equal x `(not ,y))))
                args))
        args))

(defun build-flat-arbitrary-op (op args)
  (let ((id (pfun-key->val op :identity)))
    (cond
      ((endp args) id)
      ((endp (cdr args)) (car args))
      (t (cons op args)))))

(defun simplify-arbitrary-op (op sargs)
  (let* ((args1 (flatten-same-op-args op sargs)))
    (if (has-sink-p op args1)
        (pfun-key->val op :sink)
      (let* ((args2 (remove-identities op args1))
             (args3 (if (equal (pfun-key->val op :idem) t)
                        (remove-dups args2)
                      args2)))
        (cond
          ((and (in op '(and or))
                (has-complementary-literals-p args3))
           (pfun-key->val op :sink))
          (t
           (build-flat-arbitrary-op op args3)))))))

(defun p-simplify (f)
  (match f
    ((type boolean) f)
    ((type symbol) f)
    ((list* pop args)
     (if (p-funp pop)
         (let ((sargs (mapcar #'p-simplify args)))
           (if (arbitrary-arity-p pop)
               (simplify-arbitrary-op pop sargs)
             (simplify-fixed-arity-op pop sargs)))
       f))
    (_ f)))


(assert-acl2s-equal (p-simplify '(and p t (foo t nil) q))
                    '(and p (foo t nil) q))

(assert-acl2s-equal (p-simplify '(and p t (foo t b) nil))
                    nil)

(assert-acl2s-equal (p-simplify '(and p q (and r s) (or u v)))
                    '(and p q r s (or u v)))

(assert-acl2s-equal (p-simplify '(and))
                    t)

(assert-acl2s-equal (p-simplify '(and p))
                    'p)

(assert-acl2s-equal (p-simplify '(or x y (foo a b) z (not (foo a b)) w))
                    t)

(assert-acl2s-equal (p-simplify '(and p p q))
                    '(and p q))

(assert-acl2s-equal (p-simplify '(not (not p))) 'p)
(assert-acl2s-equal (p-simplify '(not t)) nil)
(assert-acl2s-equal (p-simplify '(not nil)) t)

(assert-acl2s-equal (p-simplify '(not (iff a b))) '(xor (not a) (not b)))

(assert-acl2s-equal (p-simplify '(implies t p)) 'p)
(assert-acl2s-equal (p-simplify '(implies nil p)) t)
(assert-acl2s-equal (p-simplify '(implies p p)) t)

(assert-acl2s-equal (p-simplify '(if t a b)) 'a)
(assert-acl2s-equal (p-simplify '(if p t nil)) 'p)

(assert-acl2s-equal
 (p-simplify '(not (not (implies t (if p t nil)))))
 'p)

(assert-acl2s-equal
 (p-simplify
  '(implies (not (not p)) (if t (not (not p)) q)))
 t)

#|

 Question 2. (20 pts)

 Define tseitin, a function that given a propositional formula,
 something that satisfies p-formulap, applies the tseitin
 transformation to generate a CNF formula that is equi-satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 You should simplify the formula first, using p-simplify, but do not
 perform any other simplifications. Any simpification you want to
 perform must be done in p-simplify.

 Test tseitin using with assert-acl2s-equal using at least 10
 propositional formulas.

|#

(defun tseitin-neg (x)
  (cond
    ((equal x t) nil)
    ((equal x nil) t)
    ((and (consp x) (equal (car x) 'not)) (cadr x))
    (t `(not ,x))))

(defun tseitin-atom-p (x)
  (or (booleanp x)
      (symbolp x)
      (and (consp x)
           (not (p-funp (car x))))))

(defun right-assoc-op (op args)
  (cond
    ((endp args) (pfun-key->val op :identity))
    ((endp (cdr args)) (car args))
    (t (list op (car args) (right-assoc-op op (cdr args))))))

(defun tseitin-aux-list (args)
  (if (endp args)
      (values nil nil)
    (let+ (((&values r1 c1)
            (tseitin-aux (car args)))
           ((&values rs cs)
            (tseitin-aux-list (cdr args))))
      (values (cons r1 rs)
              (append c1 cs)))))

;; z <-> (and reps)
(defun tseitin-encode-and (z reps)
  (append
   (mapcar (lambda (a)
             (list (tseitin-neg z) a))
           reps)
   (list (cons z (mapcar #'tseitin-neg reps)))))

;; z <-> (or reps)
(defun tseitin-encode-or (z reps)
  (append
   (list (cons (tseitin-neg z) reps))
   (mapcar (lambda (a)
             (list z (tseitin-neg a)))
           reps)))

;; z <-> (implies a b)
(defun tseitin-encode-implies (z a b)
  (list
   (list (tseitin-neg z) (tseitin-neg a) b)
   (list z a)
   (list z (tseitin-neg b))))

;; z <-> (if c a b)
(defun tseitin-encode-if (z c a b)
  (list
   (list (tseitin-neg c) (tseitin-neg a) z)
   (list c (tseitin-neg b) z)
   (list (tseitin-neg z) (tseitin-neg c) a)
   (list (tseitin-neg z) c b)))

;; z <-> (iff a b)
(defun tseitin-encode-iff2 (z a b)
  (list
   (list (tseitin-neg z) (tseitin-neg a) b)
   (list (tseitin-neg z) a (tseitin-neg b))
   (list z a b)
   (list z (tseitin-neg a) (tseitin-neg b))))

;; z <-> (xor a b)
(defun tseitin-encode-xor2 (z a b)
  (list
   (list (tseitin-neg z) a b)
   (list (tseitin-neg z) (tseitin-neg a) (tseitin-neg b))
   (list z (tseitin-neg a) b)
   (list z a (tseitin-neg b))))

(defun tseitin-aux (f)
  (cond
    ;; atom / constant / non-pfun atom
    ((tseitin-atom-p f)
     (values f nil))

    ;; not: do not create fresh var, just negate representative
    ((and (consp f) (equal (car f) 'not))
     (let+ (((&values r cls)
             (tseitin-aux (cadr f))))
       (values (tseitin-neg r) cls)))

    ;; right-associate iff/xor if they have >2 args
    ((and (consp f)
          (equal (car f) 'iff)
          (> (length (cdr f)) 2))
     (tseitin-aux (right-assoc-op 'iff (cdr f))))

    ((and (consp f)
          (equal (car f) 'xor)
          (> (length (cdr f)) 2))
     (tseitin-aux (right-assoc-op 'xor (cdr f))))

    ;; general propositional operator
    ((and (consp f) (p-funp (car f)))
     (let ((op (car f))
           (args (cdr f)))
       (let+ (((&values reps child-clauses)
               (tseitin-aux-list args)))
         (cond
           ;; 0 args
           ((endp reps)
            (values (pfun-key->val op :identity)
                    child-clauses))

           ;; 1 arg
           ((endp (cdr reps))
            (values (car reps)
                    child-clauses))

           ;; >= 2 args
           (t
            (let ((z (gentemp "Z")))
              (values
               z
               (append
                child-clauses
                (cond
                  ((equal op 'and)
                   (tseitin-encode-and z reps))

                  ((equal op 'or)
                   (tseitin-encode-or z reps))

                  ((equal op 'implies)
                   (tseitin-encode-implies z
                                           (first reps)
                                           (second reps)))

                  ((equal op 'if)
                   (tseitin-encode-if z
                                      (first reps)
                                      (second reps)
                                      (third reps)))

                  ((equal op 'iff)
                   (tseitin-encode-iff2 z
                                        (first reps)
                                        (second reps)))

                  ((equal op 'xor)
                   (tseitin-encode-xor2 z
                                        (first reps)
                                        (second reps)))

                  (t
                   (error "Unsupported operator in tseitin: ~a" op)))))))))))

    (t
     (error "Not a propositional formula: ~a" f))))

(defun tseitin (f)
  (let ((sf (p-simplify f)))
    (let+ (((&values root clauses)
            (tseitin-aux sf)))
      (append clauses
              (list (list root))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helpers for testing tseitin
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun clause-list->pformula (cl)
  (cond
    ((endp cl) nil)
    ((endp (cdr cl)) (car cl))
    (t (cons 'or cl))))

(defun cnf-list->pformula (cnf)
  (cond
    ((endp cnf) t)
    ((endp (cdr cnf)) (clause-list->pformula (car cnf)))
    (t (cons 'and (mapcar #'clause-list->pformula cnf)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 10 test cases for tseitin
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-acl2s-equal
 (cnf-list->pformula (tseitin 'p))
 'p)

(assert-acl2s-equal
 (cnf-list->pformula (tseitin '(not p)))
 '(not p))

(assert-acl2s-equal
 (cnf-list->pformula (tseitin 't))
 't)

(assert-acl2s-equal
 (cnf-list->pformula (tseitin 'nil))
 'nil)

(assert-acl2s-equal
 (cnf-list->pformula (tseitin '(not (not p))))
 'p)

(assert-acl2s-equal
 (cnf-list->pformula (tseitin '(implies t p)))
 'p)

(assert-acl2s-equal
 (cnf-list->pformula (tseitin '(implies nil p)))
 't)

(assert-acl2s-equal
 (cnf-list->pformula (tseitin '(if p t nil)))
 'p)

(assert-acl2s-equal
 (cnf-list->pformula (tseitin '(if p nil t)))
 '(not p))

(assert-acl2s-equal
 (cnf-list->pformula (tseitin '(foo a b)))
 '(foo a b))

#|

 Question 3. (30 pts)

 Define DP, a function that given a propositional formula in CNF,
 applies the Davis-Putnam algorithm to determine if the formula is
 satisfiable.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DP returns 'sat and a satisfying assignment: an
 alist mapping each atom in the formula to t/nil. Use values to return
 multiple values.

 If it is usat, return 'unsat.

 Do some profiling

 Test DP using with assert-acl2s-equal using at least 10
 propositional formulas. 

 It is easy to extend dp to support arbitrary formulas by using
 tseitin to generate CNF.

|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic helpers for CNF as list of clauses
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lit-atom (lit)
  (if (and (consp lit) (equal (car lit) 'not))
      (cadr lit)
    lit))

(defun lit-negatedp (lit)
  (and (consp lit) (equal (car lit) 'not)))

(defun lit-negate (lit)
  (if (lit-negatedp lit)
      (cadr lit)
    `(not ,lit)))

(defun lit-truth-value (lit)
  ;; If literal itself is made true, what value does its atom get?
  (not (lit-negatedp lit)))

(defun literalp-dp (x)
  (or (symbolp x)
      (and (consp x)
           (not (p-funp (car x))))
      (and (consp x)
           (equal (car x) 'not)
           (or (symbolp (cadr x))
               (and (consp (cadr x))
                    (not (p-funp (caadr x))))))))

(defun clause-tautologyp (clause)
  (some (lambda (lit)
          (in (lit-negate lit) clause))
        clause))

(defun normalize-clause (clause)
  (let ((c (remove-dups clause)))
    (if (clause-tautologyp c)
        :tautology
      c)))

(defun normalize-cnf (cnf)
  (remove-dups
   (remove :tautology
           (mapcar #'normalize-clause cnf)
           :test #'equal)))

(defun empty-clause-present-p (cnf)
  (in nil cnf))

(defun formula-atoms-aux (f)
  (cond
    ((booleanp f) nil)
    ((symbolp f) (list f))
    ((and (consp f) (p-funp (car f)))
     (reduce #'append
             (mapcar #'formula-atoms-aux (cdr f))
             :initial-value nil))
    ((consp f) (list f))
    (t nil)))

(defun formula-atoms (f)
  (remove-dups (formula-atoms-aux f)))

(defun cnf-literals (cnf)
  (remove-dups
   (reduce #'append cnf :initial-value nil)))

(defun complete-assignment (atoms assignment)
  (if (endp atoms)
      assignment
    (let ((pr (assoc (car atoms) assignment :test #'equal)))
      (if pr
          (complete-assignment (cdr atoms) assignment)
        (complete-assignment (cdr atoms)
                             (acons (car atoms) t assignment))))))

(defun project-assignment (assignment atoms)
  (remove nil
          (mapcar (lambda (a)
                    (let ((pr (assoc a assignment :test #'equal)))
                      (and pr pr)))
                  atoms)))

(defun clause-satisfied-p (clause assignment)
  (some (lambda (lit)
          (let ((pr (assoc (lit-atom lit) assignment :test #'equal)))
            (and pr
                 (equal (cdr pr)
                        (lit-truth-value lit)))))
        clause))

(defun add-assignment (atom val assignment)
  (let ((pr (assoc atom assignment :test #'equal)))
    (cond
      ((null pr) (values (acons atom val assignment) nil))
      ((equal (cdr pr) val) (values assignment nil))
      (t (values assignment t)))))

(defun merge-assignments (a1 a2)
  (if (endp a1)
      (values a2 nil)
    (let+ (((&values rest conflict1)
            (merge-assignments (cdr a1) a2)))
      (if conflict1
          (values rest t)
        (add-assignment (caar a1) (cdar a1) rest)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simplification under a literal
;; Make literal lit true in cnf:
;;   - remove clauses containing lit
;;   - remove occurrences of (neg lit) from remaining clauses
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simplify-under-literal (cnf lit)
  (let ((neg (lit-negate lit)))
    (normalize-cnf
     (mapcan (lambda (clause)
               (cond
                 ((in lit clause) nil)
                 (t (list (remove neg clause :test #'equal)))))
             cnf))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rule 1: Pure Literal Rule
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-pure-literal (cnf)
  (let ((lits (cnf-literals cnf)))
    (find-if (lambda (lit)
               (not (in (lit-negate lit) lits)))
             lits)))

(defun dp-pure-literal-rule (cnf)
  ;; Apply pure literal rule to a fixpoint.
  ;; Returns (values status new-cnf assignment)
  ;; status is 'ok or 'unsat
  (let ((lit (find-pure-literal cnf)))
    (if (null lit)
        (values 'ok cnf nil)
      (let+ (((&values a1 conflict1)
              (add-assignment (lit-atom lit)
                              (lit-truth-value lit)
                              nil)))
        (if conflict1
            (values 'unsat cnf nil)
          (let ((cnf1 (simplify-under-literal cnf lit)))
            (if (empty-clause-present-p cnf1)
                (values 'unsat cnf1 nil)
              (let+ (((&values status cnf2 a2)
                      (dp-pure-literal-rule cnf1)))
                (if (equal status 'unsat)
                    (values 'unsat cnf2 nil)
                  (let+ (((&values merged conflict2)
                          (merge-assignments a1 a2)))
                    (if conflict2
                        (values 'unsat cnf2 nil)
                      (values 'ok cnf2 merged))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rule 2: Unit Resolution / BCP
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-unit-literal (cnf)
  (let ((u (find-if (lambda (clause)
                      (and (consp clause)
                           (endp (cdr clause))))
                    cnf)))
    (and u (car u))))

(defun dp-unit-resolution-rule (cnf)
  ;; Apply BCP to a fixpoint.
  ;; Returns (values status new-cnf assignment)
  ;; status is 'ok or 'unsat
  (let ((lit (find-unit-literal cnf)))
    (if (null lit)
        (values 'ok cnf nil)
      (let+ (((&values a1 conflict1)
              (add-assignment (lit-atom lit)
                              (lit-truth-value lit)
                              nil)))
        (if conflict1
            (values 'unsat cnf nil)
          (let ((cnf1 (simplify-under-literal cnf lit)))
            (if (empty-clause-present-p cnf1)
                (values 'unsat cnf1 nil)
              (let+ (((&values status cnf2 a2)
                      (dp-unit-resolution-rule cnf1)))
                (if (equal status 'unsat)
                    (values 'unsat cnf2 nil)
                  (let+ (((&values merged conflict2)
                          (merge-assignments a1 a2)))
                    (if conflict2
                        (values 'unsat cnf2 nil)
                      (values 'ok cnf2 merged))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rule 3: Resolution elimination
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun choose-resolution-atom (cnf)
  (lit-atom (car (car cnf))))

(defun dp-resolution-rule (cnf)
  ;; Choose atom p.
  ;; Let P = clauses containing p
  ;; Let N = clauses containing (not p)
  ;; Let E = all other clauses
  ;; Return E U all p-resolvents(P,N)
  ;;
  ;; Also return enough info to reconstruct p later:
  ;; positive residual clauses (with p removed).
  ;;
  ;; Returns:
  ;;   (values new-cnf p positive-residuals)
  (let* ((p (choose-resolution-atom cnf))
         (pos p)
         (neg `(not ,p))
         (P nil)
         (N nil)
         (E nil))
    (dolist (clause cnf)
      (cond
        ((in pos clause) (push clause P))
        ((in neg clause) (push clause N))
        (t (push clause E))))
    (let* ((P (reverse P))
           (N (reverse N))
           (E (reverse E))
           (P0 (mapcar (lambda (clause)
                         (remove pos clause :test #'equal))
                       P))
           (N0 (mapcar (lambda (clause)
                         (remove neg clause :test #'equal))
                       N))
           (resolvents
             (mapcan (lambda (c)
                       (mapcan (lambda (d)
                                 (let ((r (normalize-clause (append c d))))
                                   (if (equal r :tautology)
                                       nil
                                     (list r))))
                               N0))
                     P0))
           (new-cnf (normalize-cnf (append E resolvents))))
      (values new-cnf p P0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DP recursion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun dp-aux (cnf)
  (let ((cnf (normalize-cnf cnf)))
    (cond
      ((empty-clause-present-p cnf)
       (values 'unsat nil))

      ((endp cnf)
       (values 'sat nil))

      (t
       ;; First BCP
       (let+ (((&values status1 cnf1 a1)
               (dp-unit-resolution-rule cnf)))
         (cond
           ((equal status1 'unsat)
            (values 'unsat nil))

           ((not (equal cnf1 cnf))
            (let+ (((&values status-rest a-rest)
                    (dp-aux cnf1)))
              (if (equal status-rest 'unsat)
                  (values 'unsat nil)
                (let+ (((&values merged conflict)
                        (merge-assignments a1 a-rest)))
                  (if conflict
                      (values 'unsat nil)
                    (values 'sat merged))))))

           (t
            ;; Then pure literal rule
            (let+ (((&values status2 cnf2 a2)
                    (dp-pure-literal-rule cnf1)))
              (cond
                ((equal status2 'unsat)
                 (values 'unsat nil))

                ((not (equal cnf2 cnf1))
                 (let+ (((&values status-rest a-rest)
                         (dp-aux cnf2)))
                   (if (equal status-rest 'unsat)
                       (values 'unsat nil)
                     (let+ (((&values merged conflict)
                             (merge-assignments a2 a-rest)))
                       (if conflict
                           (values 'unsat nil)
                         (values 'sat merged))))))

                (t
                 ;; Finally resolution elimination
                 (let+ (((&values cnf3 p pos-residuals)
                         (dp-resolution-rule cnf2))
                        ((&values status3 a3)
                         (dp-aux cnf3)))
                   (if (equal status3 'unsat)
                       (values 'unsat nil)
                     ;; Reconstruct p:
                     ;; If all positive residual clauses are already satisfied,
                     ;; set p = nil; otherwise set p = t.
                     (let ((pval
                             (if (every (lambda (cl)
                                          (clause-satisfied-p cl a3))
                                        pos-residuals)
                                 nil
                               t)))
                       (let+ (((&values a4 conflict)
                               (add-assignment p pval a3)))
                         (if conflict
                             (values 'unsat nil)
                           (values 'sat a4))))))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DP
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun dp (f)
  ;; f is a propositional formula.
  ;; We simplify it, convert it to clause-list CNF by tseitin,
  ;; run DP on that CNF, and return assignments only for atoms
  ;; occurring in the original formula.
  (let* ((sf (p-simplify f))
         (orig-atoms (formula-atoms sf))
         (cnf (tseitin sf)))
    (let+ (((&values status assignment)
            (dp-aux cnf)))
      (if (equal status 'unsat)
          'unsat
        (values 'sat
                (project-assignment
                 (complete-assignment orig-atoms assignment)
                 orig-atoms))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Testing DP
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(dp 'p)
(dp '(not p))
(dp '(and p q))
(dp '(and p (not p)))
(dp '(or p (not p)))
(dp '(if p q r))
(dp '(and (or p q) (or (not p) q)))
(dp '(and (foo a b) (not (foo a b))))
(dp '(implies p q))
(dp '(and (or p q) (not r)))

#|

 Question 4.

 Part1: (25pts) Profile DP and make it as efficient as possible. If it
 meets the efficiency criteria of the evaluator, you get credit. The
 fastest submission will get 20 extra points, no matter how slow. To
 generate interesting problems, see your book.

 Part 2: (30pts) Define DPLL, a function that given a propositional
 formula in CNF, applies the DPLL algorithm to determine if the
 formula is satisfiable. You have to implement the iterative with
 backjumping version of DPLL from the book.

 Remember that you have to deal with atoms such as

 (foo (if a b))

 If the formula is sat, DPLL returns 'sat and a satisfying assignment:
 an alist mapping each atom in the formula to t/nil. Use values to
 return multiple values.

 If it is usat, return 'unsat.

 Test DPLL using with assert-acl2s-equal using at least 10
 propositional formulas.

 The fastest submission will get 20 extra points, no matter how
 slow. To generate interesting problems, see your book.

|#

(defun dpll-bcp (cnf assignment)
  ;; Apply unit propagation to a fixpoint.
  ;; Returns: (values status new-cnf new-assignment)
  ;; status = 'ok or 'unsat
  (let ((lit (find-unit-literal cnf)))
    (if (null lit)
        (values 'ok cnf assignment)
      (let+ (((&values assignment1 conflict1)
              (add-assignment (lit-atom lit)
                              (lit-truth-value lit)
                              assignment)))
        (if conflict1
            (values 'unsat cnf assignment)
          (let ((cnf1 (simplify-under-literal cnf lit)))
            (if (empty-clause-present-p cnf1)
                (values 'unsat cnf1 assignment1)
              (dpll-bcp cnf1 assignment1))))))))

(defun dpll-pure-literal-rule (cnf assignment)
  ;; Apply pure literal elimination to a fixpoint.
  ;; Returns: (values status new-cnf new-assignment)
  ;; status = 'ok or 'unsat
  (let ((lit (find-pure-literal cnf)))
    (if (null lit)
        (values 'ok cnf assignment)
      (let+ (((&values assignment1 conflict1)
              (add-assignment (lit-atom lit)
                              (lit-truth-value lit)
                              assignment)))
        (if conflict1
            (values 'unsat cnf assignment)
          (let ((cnf1 (simplify-under-literal cnf lit)))
            (if (empty-clause-present-p cnf1)
                (values 'unsat cnf1 assignment1)
              (dpll-pure-literal-rule cnf1 assignment1))))))))

(defun choose-branch-literal (cnf)
  ;; A simple branching heuristic:
  ;; choose a literal from a shortest clause.
  (car (reduce (lambda (c1 c2)
                 (if (< (len c1) (len c2)) c1 c2))
               cnf)))

(defun dpll-backtrack-step (stack)
  ;; stack stores decision points of the form:
  ;;   (saved-cnf saved-assignment tried-lit)
  ;;
  ;; We pop one frame and try the opposite branch.
  ;; Returns:
  ;;   (values status new-cnf new-assignment new-stack)
  ;; status = 'retry or 'unsat
  (if (endp stack)
      (values 'unsat nil nil nil)
    (let* ((frame (car stack))
           (rest (cdr stack))
           (saved-cnf (first frame))
           (saved-assignment (second frame))
           (tried-lit (third frame))
           (opp-lit (lit-negate tried-lit)))
      (let+ (((&values assignment1 conflict1)
              (add-assignment (lit-atom opp-lit)
                              (lit-truth-value opp-lit)
                              saved-assignment)))
        (if conflict1
            ;; impossible in principle, but skip to earlier decision if it happens
            (dpll-backtrack-step rest)
          (values 'retry
                  (simplify-under-literal saved-cnf opp-lit)
                  assignment1
                  rest))))))

(defun dpll-aux (cnf)
  ;; Iterative DPLL with an explicit decision stack.
  ;; Returns:
  ;;   (values 'sat assignment)
  ;;   (values 'unsat nil)
  (let ((cnf (normalize-cnf cnf))
        (assignment nil)
        (stack nil))
    (loop
      ;; base cases before simplification
      (cond
        ((empty-clause-present-p cnf)
         (let+ (((&values bt-status bt-cnf bt-assignment bt-stack)
                 (dpll-backtrack-step stack)))
           (if (equal bt-status 'unsat)
               (return (values 'unsat nil))
             (setf cnf bt-cnf
                   assignment bt-assignment
                   stack bt-stack))))

        ((endp cnf)
         (return (values 'sat assignment)))

        (t
         ;; 1. BCP
         (let+ (((&values status1 cnf1 assignment1)
                 (dpll-bcp cnf assignment)))
           (cond
             ((equal status1 'unsat)
              (let+ (((&values bt-status bt-cnf bt-assignment bt-stack)
                      (dpll-backtrack-step stack)))
                (if (equal bt-status 'unsat)
                    (return (values 'unsat nil))
                  (setf cnf bt-cnf
                        assignment bt-assignment
                        stack bt-stack))))

             (t
              (setf cnf cnf1
                    assignment assignment1)

              ;; base cases after BCP
              (cond
                ((empty-clause-present-p cnf)
                 (let+ (((&values bt-status bt-cnf bt-assignment bt-stack)
                         (dpll-backtrack-step stack)))
                   (if (equal bt-status 'unsat)
                       (return (values 'unsat nil))
                     (setf cnf bt-cnf
                           assignment bt-assignment
                           stack bt-stack))))

                ((endp cnf)
                 (return (values 'sat assignment)))

                (t
                 ;; 2. Pure literal rule
                 (let+ (((&values status2 cnf2 assignment2)
                         (dpll-pure-literal-rule cnf assignment)))
                   (cond
                     ((equal status2 'unsat)
                      (let+ (((&values bt-status bt-cnf bt-assignment bt-stack)
                              (dpll-backtrack-step stack)))
                        (if (equal bt-status 'unsat)
                            (return (values 'unsat nil))
                          (setf cnf bt-cnf
                                assignment bt-assignment
                                stack bt-stack))))

                     (t
                      (setf cnf cnf2
                            assignment assignment2)

                      ;; base cases after pure literal elimination
                      (cond
                        ((empty-clause-present-p cnf)
                         (let+ (((&values bt-status bt-cnf bt-assignment bt-stack)
                                 (dpll-backtrack-step stack)))
                           (if (equal bt-status 'unsat)
                               (return (values 'unsat nil))
                             (setf cnf bt-cnf
                                   assignment bt-assignment
                                   stack bt-stack))))

                        ((endp cnf)
                         (return (values 'sat assignment)))

                        (t
                         ;; 3. Branch
                         ;; Choose lit, push decision point, try lit=true first.
                         (let ((lit (choose-branch-literal cnf)))
                           (push (list cnf assignment lit) stack)
                           (let+ (((&values assignment3 conflict3)
                                   (add-assignment (lit-atom lit)
                                                   (lit-truth-value lit)
                                                   assignment)))
                             (if conflict3
                                 ;; should be rare; immediately backtrack
                                 (let+ (((&values bt-status bt-cnf bt-assignment bt-stack)
                                         (dpll-backtrack-step stack)))
                                   (if (equal bt-status 'unsat)
                                       (return (values 'unsat nil))
                                     (setf cnf bt-cnf
                                           assignment bt-assignment
                                           stack bt-stack)))
                               (setf cnf (simplify-under-literal cnf lit)
                                     assignment assignment3)))))))))))))))))))))

(defun dpll (f)
  ;; f is a propositional formula.
  ;; We simplify it, convert it to clause-list CNF via tseitin,
  ;; run DPLL, and return assignments only for atoms in the original formula.
  (let* ((sf (p-simplify f))
         (orig-atoms (formula-atoms sf))
         (cnf (tseitin sf)))
    (let+ (((&values status assignment)
            (dpll-aux cnf)))
      (if (equal status 'unsat)
          'unsat
        (values 'sat
                (project-assignment
                 (complete-assignment orig-atoms assignment)
                 orig-atoms))))))

(dpll 'p)
(dpll '(not p))
(dpll '(and p q))
(dpll '(and p (not p)))
(dpll '(or p (not p)))
(dpll '(if p q r))
(dpll '(and (or p q) (or (not p) q)))
(dpll '(and (foo a b) (not (foo a b))))
(dpll '(implies p q))
(dpll '(and (or p q) (not r)))