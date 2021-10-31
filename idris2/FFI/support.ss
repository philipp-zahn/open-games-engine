(define (idris-make-hashtable k v)
  (make-hashtable equal-hash equal?))

(define (idris-hashtable-set k v ht key obj)
  (let ((new (hashtable-copy ht #t)))
       (begin (hashtable-set! new key obj)
              new)))

(define (idris-hashtable-ref k v ht key)
  (let ((r (hashtable-ref ht key #f)))
       (if (equal? r #f) '() (box r))))

(define (idris-hashtable-contains k v ht key)
  (case (hashtable-contains? ht key)
        ((#f) 0)
        ((#t) 1)))

(define (idris-hashtable-update k v ht key f)
  (let ((new (hashtable-copy ht #t)))
       (begin (hashtable-update! new key f)
              new)))

(define (idris-hashtable-delete k v ht key)
  (let ((new (hashtable-copy ht #t)))
       (begin (hashtable-delete! new key)
              new)))

(define (idris-hashtable-size k v ht)
  (hashtable-size ht))

(define (idris-hashtable-keys k v ht)
  (vector->list (hashtable-keys ht)))

(define (zip . xss) (apply map list xss))

(define (idris-hashtable-entries k v ht)
  (let-values ([(keys vals) (hashtable-entries ht)])
              (cons (vector->list keys) (vector->list vals))))
