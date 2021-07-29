(in-package #:sdf/base)

(defmacro do-edge-pairs ((wx wy i1 j1 i2 j2) &body body)
  (a:with-gensyms (di dj)
    `(loop for ,j1 below ,wy
           do (loop for ,i1 below ,wx
                    do (loop for ,di from -1 to 1
                             do (loop for ,dj from -1 to 1
                                      unless (= ,di ,dj 0)
                                        do (let ((,i1 ,i1)
                                                 (,i1 ,j1)
                                                 (,i2 (+ ,i1 ,di))
                                                 (,j2 (+ ,j1 ,dj)))
                                             (when (and (< -1 ,i2 ,wx)
                                                        (< -1 ,j2 ,wy))
                                               ,@body))))))))

(defmacro do-edge-pairs4 ((wx wy i1 j1 i2 j2) &body body)
  (a:with-gensyms (run)
    `(flet ((,run (,i1 ,j1 ,i2 ,j2)
              (when (and (< -1 ,i2 ,wx)
                         (< -1 ,j2 ,wy))
                ,@body)))
       (loop for ,j1 below ,wy
             do (loop for ,i1 below ,wx
                      do ;; horizontal
                         (,run ,i1 ,j1 (+ ,i1 1) ,j1)
                         ;; vertical
                         (,run ,i1 ,j1 ,i1 (+ ,j1 1))
                         ;; down/right
                         (,run ,i1 ,j1 (+ ,i1 1) (+ ,j1 1))
                         ;; down/left
                         (,run ,i1 ,j1 (- ,i1 1) (+ ,j1 1)))))))

(defun protect-samples (protected image pimage corner-cells)
  ;; 'protect' samples around a corner of shape
  (let ((wx (array-dimension image 1))
        (wy (array-dimension image 0)))
    (format t "protect corners~%")
    (flet ((cc (j i)
             (when (array-in-bounds-p protected j i)
               (format t " protect ~s,~s~%" i j)
               (setf (aref protected j i) 1))))
      (loop for j below wy
            do (loop for i below wx
                     when (aref corner-cells j i)
                       do (cc j i)
                          (cc (1+ j) i)
                          (cc j (1+ i))
                          (cc (1+ j) (1+ i)))))
    ;; protect samples that have non-median samples that contribute to an edge
    (do-edge-pairs4 (wx wy i1 j1 i2 j2)
      (labels ((median3 (a b c)
                 (max (min a b) (min (max a b) c)))
               (vmedian (v)
                 (median3 (aref v 0)
                          (aref v 1)
                          (aref v 2)))
               (imedian (j i)
                 (median3 (aref image j i 0)
                          (aref image j i 1)
                          (aref image j i 2)))
               (lerp-at (at)
                 (vector (a:lerp at
                                 (aref image j1 i1 0)
                                 (aref image j2 i2 0))
                         (a:lerp at
                                 (aref image j1 i1 1)
                                 (aref image j2 i2 1))
                         (a:lerp at
                                 (aref image j1 i1 2)
                                 (aref image j2 i2 2))))
               (channel-has-edge (c)
                 (let* ((a (aref image j1 i1 c))
                        (b (aref image j2 i2 c))
                        ;; a + tt (b - a) = 0
                        ;; tt (b - a) = -a
                        ;; tt = (- a) / (- b a)
                        ;;    = (/ a (- a b))
                        (tt (/ a (- a b))))
                   (and (< 0 tt 1)
                        (let* ((i (lerp-at tt))
                               (m (vmedian i)))
                          (= m (aref i c)))))))
        (progn #+unless (and (plusp (aref protected j1 i1))
                     (plusp (aref protected j2 i2)))
          (let ((m1 (aref pimage j1 i1))
                (m2 (aref pimage j2 i2)))
            (when (< (+ (abs m1) (abs m2))
                     (* 1.001
                        (sqrt (+ (expt (- i2 i1) 2)
                                 (expt (- j2 j1) 2)))))
              (loop for c below 3
                       when (channel-has-edge c)
                         do (when (/= m1 (aref image j1 i1 c))
                              #++(format t "protect ~s,~s~%" i1 j1)
                              (setf (aref protected j1 i1) 1))
                            (when (/= m2 (aref image j2 i2 c))
                              #++(format t "protect ~s,~s~%" i2 j2)
                              (setf (aref protected j2 i2) 1)))
              (let ((m (loop for c below 3 collect (channel-has-edge c))))
                (when (some 'identity m)
                  (let* ((x (min i1 i2))
                         (y (min j1 j2))
                         (dx (- (max i1 i2) x))
                         (dy (- (max j1 j2) y))
                         (d (loop for i below 3 for e in m
                                  when e sum (ash 1 i)))
                         (cc (if (and (/= i1 i2) (/= j1 j2))
                                 :d
                                 (if (zerop dx) :v :h))))
                    #++(format t "~a ~2,'0d, ~2,'0d = ~s, ~,5f ~,5f~%"
                               cc x y (loop for i below 3 for e in m
                                            when e sum (ash 1 i))
                               (aref pimage y x)
                               (aref pimage (+ y dy) (+ x dx))
                               )
                    (loop for c below 3 for e in m
                          do (when (and e (/= m1 (aref image j1 i1 c)))
                               (format t "~a protect ~s+~s,~s+~s ~s ~s~%"
                                       cc x (- i1 x) y (- j1 y) m d)
                               (setf (aref protected j1 i1) 1)
                               (loop-finish)))
                    (loop for c below 3 for e in m
                          do (when (and e (/= m2 (aref image j2 i2 c)))
                               (format t "~a protect ~s+~s,~s+~s ~s ~s~%"
                                       cc x (- i2 x) y (- j2 y) m d)
                               (setf (aref protected j2 i2) 1)
                               (loop-finish))
                          ))
                  )
                ))))))))

(defparameter *feb-edge-epsilon* 0.01)
(defparameter *feb-distance-epsilon* 0.111)
(defun find-errors-base (errors protected image pimage)
  (let ((wx (array-dimension image 1))
        (wy (array-dimension image 0)))
    (do-edge-pairs4 (wx wy i1 j1 i2 j2)
      ;; look at whichever sample of pair is further from shape,
      ;; unless it is protected and other is not
      (when (and (< (abs (aref pimage j1 i1))
                    (abs (aref pimage j2 i2)))
                 (or (zerop (aref protected j2 i2))
                     (plusp (aref protected j1 i1))))
        (rotatef i1 i2)
        (rotatef j1 j2))
      (labels ((median3 (a b c)
                 (max (min a b) (min (max a b) c)))
               (imedian (j i)
                 (median3 (aref image j i 0)
                          (aref image j i 1)
                          (aref image j i 2)))
               (d (x)
                 (coerce x 'double-float)))
        (unless (plusp (aref errors j1 i1))
          (let ((m1 (imedian j1 i1))
                (m2 (imedian j2 i2))
                (ddd (and (<= sdf-scratch::*kx* i1 (1+ sdf-scratch::*kx*))
                          (<= sdf-scratch::*ky* j1 (1+ sdf-scratch::*ky*)))))
            (labels (#++(vmedian (v)
                          (median3 (aref v 0)
                                   (aref v 1)
                                   (aref v 2)))
                     (%lerp-at (at)
                       (values (a:lerp at
                                       (aref image j1 i1 0)
                                       (aref image j2 i2 0))
                               (a:lerp at
                                       (aref image j1 i1 1)
                                       (aref image j2 i2 1))
                               (a:lerp at
                                       (aref image j1 i1 2)
                                       (aref image j2 i2 2))))
                     #++(lerp-at (at)
                          (multiple-value-call #'vector (%lerp-at at)))
                     (median-at (at)
                       (multiple-value-call #'median3 (%lerp-at at)))

                     (d-pair (a b)
                       ;; 1 2
                       ;; 3 4
                       (let* ((a1 (d (aref image j1 i1 a)))
                              (a2 (d (aref image j1 i2 a)))
                              (a3 (d (aref image j2 i1 a)))
                              (a4 (d (aref image j2 i2 a)))
                              (b1 (d (aref image j1 i1 b)))
                              (b2 (d (aref image j1 i2 b)))
                              (b3 (d (aref image j2 i1 b)))
                              (b4 (d (aref image j2 i2 b)))
                              ;; ah1 = a1 + tt (a2 - a1)
                              ;; ah2 = a3 + tt (a4 - a3)
                              ;; sa = ah1 + tt (ah2 - ah1)
                              ;;    = a1 + tt (a2 - a1)
                              ;;         + tt a3 + tt² (a4 - a3)
                              ;;         - tt a1 - tt² (a2 - a1)
                              ;;    = tt² (a4 - a3 - a2 + a1)
                              ;;     + tt (a2 - a1 + a3 - a1)
                              ;;     + a1
                              (ac2 (- (- a4 a3) (- a2 a1)))
                              (ac1 (+ (- a2 a1) (- a3 a1)))
                              (ac0 a1)
                              (bc2 (- (- b4 b3) (- b2 b1)))
                              (bc1 (+ (- b2 b1) (- b3 b1)))
                              (bc0 b1)
                              ;; ac2 tt² + ac1 tt + ac0 = bc2 tt² + bc1 tt + bc0
                              ;; (ac2-bc2) tt² + (ac1-bc1) tt + (ac0-bc0) = 0
                              (qa (- ac2 bc2))
                              (qb (- ac1 bc1))
                              (qc (- ac0 bc0))
                              (qd (- (expt qb 2) (* 4 qa qc)))
                              ;; extrema of channels
                              ;; 2 ac2 tt + ac1 = 0
                              ;; tt = (/ (- ac1) (* 2 ac2)
                              (amt (unless (zerop ac2) (/ (- ac1) (* 2 ac2))))
                              (bmt (unless (zerop bc2) (/ (- bc1) (* 2 bc2)))))
                         (labels ((c-at2 (at1 at2 c)
                                    (a:lerp at2
                                            (a:lerp at1
                                                    (aref image j1 i1 c)
                                                    (aref image j1 i2 c))
                                            (a:lerp at1
                                                    (aref image j2 i1 c)
                                                    (aref image j2 i2 c))))
                                  (median-at2 (at1 at2)
                                    (median3 (c-at2 at1 at2 0)
                                             (c-at2 at1 at2 1)
                                             (c-at2 at1 at2 2)))
                                  (check (m m1 m2 tt t1 t2)
                                    (when ddd
                                     (format t "  prot = ~s, ~s~%"
                                             (aref protected j1 i1)
                                             (aref protected j2 i2))
                                     (format t "  m = ~s ~s ~s~%"
                                             (min m1 m2) m (max m1 m2))
                                     (format t "  t = ~s ~s ~s~%"
                                             t1 tt t2)
                                     (format t "  d1 = ~s - ~s = ~,5f, > ~,5f (~s)~%"
                                             m m1 (abs (- m m1))
                                             (* (sqrt 2)
                                                (- tt t1)
                                                (1+ *feb-distance-epsilon*))
                                             (- tt t1))
                                     (format t "  d2 = ~s - ~s = ~,5f, > ~,5f (~s)~%"
                                             m m2 (abs (- m m2))
                                             (* (sqrt 2)
                                                (- t2 tt)
                                                (1+ *feb-distance-epsilon*))
                                             (- t2 tt)))
                                    (when (or (not (= (signum m)
                                                      (signum m1)
                                                      (signum m2)))
                                              (and (zerop (aref protected j1 i1))
                                                   (not
                                                    (<= (min m1 m2) m (max m1 m2)))))
                                      (when (or (> (abs (- m m1))
                                                   (* (sqrt 2)
                                                      (- tt t1)
                                                      (1+ *feb-distance-epsilon*)))
                                                (> (abs (- m m2))
                                                   (* (sqrt 2)
                                                      (- t2 tt)
                                                      (1+ *feb-distance-epsilon*))))
                                        (format t ">>d2 ~s,~s - ~s,~s: ~s, ~s, ~s~%"
                                                i1 j1 i2 j2 m1 m m2)
                                        (return-from d-pair t))))
                                  (d-pair2 (tt)
                                    (when (< *feb-edge-epsilon*
                                             tt
                                             (- 1 *feb-edge-epsilon*))
                                      (assert (< (abs (- (c-at2 tt tt a)
                                                         (c-at2 tt tt b)))
                                                 0.001))
                                      #++(format t "tt = ~s~%" tt)
                                      (let ((m (median-at2 tt tt)))
                                        (when ddd
                                          (format t "DDD ~s,~s - ~s,~s @ ~s,~s = ~,5f: s= ~s,~s,~s~%"
                                                  i1 j1 i2 j2 a b tt
                                                  (signum m)
                                                  (signum m1)
                                                  (signum m2)))
                                        (check m m1 m2 tt 0 1)
                                        (when (and amt (< 0 amt 1) (/= amt tt))
                                          (let ((mat1 (median-at2 amt amt)))
                                            (when ddd
                                              (format t "  amt = ~s = ~s~%"
                                                      amt mat1)
                                              (format t "  @ ~,5f = ~,5f~%"
                                                      amt (c-at2 amt amt a))
                                              (loop for i upto 1 by 0.125
                                                    do (format t "    ~,5f=~,5f~%"
                                                               i (c-at2 i i a))))
                                            (if (< amt tt)
                                                (check m mat1 m2 tt amt 1)
                                                (check m m1 mat1 tt 0 amt))))
                                        (when (and bmt (< 0 bmt 1) (/= bmt tt))
                                          (let ((mbt1 (median-at2 bmt bmt)))
                                            (when ddd
                                              (format t "  bmt = ~s = ~s~%"
                                                      bmt mbt1)
                                              (format t "  @ ~,5f = ~,5f~%"
                                                      bmt (c-at2 bmt bmt b))
                                              (loop for i upto 1 by 0.125
                                                    do (format t "    ~,5f=~,5f~%" i (c-at2 i i b)))
                                              (let ((l (/ bmt 2))
                                                    (r (/ (1+ bmt) 2)))
                                                (format t "  ~,5f=~,5f, ~,5f=~,5f, ~,5f=~,5f~%"
                                                        l (c-at2 l l b)
                                                        bmt (c-at2 bmt bmt b)
                                                        r (c-at2 r r b))))
                                            (if (< bmt tt)
                                                (check m mbt1 m2 tt bmt 1)
                                                (check m m1 mbt1 tt 0 bmt)))
)))))
                           (cond
                             ((or (zerop qa) (minusp qd))
                              ;; no solutions, skip this pair
                              )
                             ((zerop qd)
                              (d-pair2 (/ (- qb) (* qa 2))))
                             (t
                              (d-pair2 (/ (+ (- qb) (sqrt qd)) (* qa 2)))
                              (d-pair2 (/ (- (- qb) (sqrt qd)) (* qa 2)))))
                           nil)))
                     (mark-diagonal ()
                       (when (or (d-pair 0 1)
                                 (d-pair 0 2)
                                 (d-pair 1 2))
                         (setf (aref errors j1 i1) 1)))
                     (hv-pair (a b)
                       ;; a1 + tt (- a2 a1) = b1 + tt ( - b2 b1)
                       ;; tt (- a2 a1) - tt ( - b2 b1) = b1 - a1
                       ;; tt (- a2 a1 b1 b2) = (- b1 a1)
                       ;; tt = (- b1 a1) / (- a2 a1 b1 b2)
                       (let* ((a1 (aref image j1 i1 a))
                              (a2 (aref image j2 i2 a))
                              (b1 (aref image j1 i1 b))
                              (b2 (aref image j2 i2 b))
                              (d (- a2 a1 (- b2 b1))))
                         (unless (zerop d)
                           (let ((tt (/ (- b1 a1) d)))
                             (when (< *feb-edge-epsilon*
                                      tt
                                      (- 1 *feb-edge-epsilon*))
                               (let ((m (median-at tt)))
                                 (when (or (not (= (signum m)
                                                   (signum m1)
                                                   (signum m2)))
                                           (and (zerop (aref protected j1 i1))
                                                (not
                                                 (<= (min m1 m2) m (max m1 m2)))))
                                   (when (or (> (abs (- m m1))
                                                (* tt
                                                   (1+ *feb-distance-epsilon*)))
                                             (> (abs (- m m2))
                                                (* (- 1 tt)
                                                   (1+ *feb-distance-epsilon*))))
                                     (format t "h1 ~s,~s - ~s,~s: ~s, ~s, ~s~%"
                                             i1 j1 i2 j2 m1 m m2)
                                     (return-from hv-pair t)))))))))
                     (mark-hv ()
                       (when (or (hv-pair 0 1)
                                 (hv-pair 0 2)
                                 (hv-pair 1 2))
                         (setf (aref errors j1 i1) 1))))
              (if (and (/= i1 i2) (/= j1 j2))
                  (mark-diagonal)
                  (mark-hv)))))))))

(defun fix-msdf7 (image pimage corner-cells)
  (let ((protected (make-array (array-dimensions pimage)
                               :element-type 'bit :initial-element 0))
        (errors (make-array (array-dimensions pimage)
                            :element-type 'bit :initial-element 0))
        (wx (array-dimension pimage 1))
        (wy (array-dimension pimage 0)))
    ;; protect samples contributing to corners/edges
    (protect-samples protected image pimage corner-cells)

    (format t "protected=~%")
    (loop for j below wy
          do (loop for i below wx
                   do (format t " ~s" (aref protected j i)))
          (format t "~%"))
    ;; find errors
    (find-errors-base errors protected image pimage)

    ;; remove errors
    (loop for j below wy
          do (loop for i below wx
                   when (plusp (aref errors j i))
                     do (setf (aref image j i 0) (aref pimage j i))
                        (setf (aref image j i 1) (aref pimage j i))
                        (setf (aref image j i 2) (aref pimage j i))
                        (setf (aref image j i 3)
                              (* -100 (aref image j i 3)))))))
