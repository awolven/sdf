(in-package #:sdf)


;;;
;;;  MAXRECT packing as defined in http://clb.demon.fi/files/RectangleBinPack.pdf
;;;  See also: https://github.com/juj/RectangleBinPack
;;;

(defmacro with-rect ((x y &optional (w (gensym)) (h (gensym))) rect &body body)
  `(destructuring-bind (,x ,y ,w ,h) ,rect
     (declare (ignorable ,x ,y ,w ,h))
     ,@body))

(defun delta-weight (w h rect)
  (with-rect (x y rw rh) rect
    (min (- rw w) (- rh h))))

(defun grow-rects (rects dx dy)
  (destructuring-bind (x1 y1)
      (loop for (x y w h) in rects
            maximize (+ x w) into mx
            maximize (+ y h) into my
            finally (return (list mx my)))
    (let ((x-edges ())
          (y-edges ()))
      (loop
        for r in rects
        do (with-rect (x y w h) r
             (when (= x1 (+ x w))
               (push r y-edges)
               (incf (third r) dx))
             (when (= y1 (+ y h))
               (push r x-edges)
               (incf (fourth r) dy))))
      (setf x-edges (sort x-edges '< :key 'first)
            y-edges (sort y-edges '< :key 'second))
      (format t "x:~s~%" x-edges)
      (format t "y:~s~%" y-edges)
      (when (and x-edges (plusp dy))
        ;; start outside edge to simplify handling of edge
        (loop with live = (list (list -1 0 1 0))
              with start = nil
              for x below (+ x1 dx)
              for in = live
              do (loop for edge = (car x-edges)
                       while (and edge (<= (first edge) x))
                       do (push (pop x-edges) live))
                 (setf live (loop for l in live
                                  for (lx nil w nil) = l
                                  unless (< (+ lx w) x)
                                    collect l))
                 (when (and in (not live))
                   (setf start x))
                 (when (and live (not in))
                   ;; fixme: put rects in an object or something
                   ;; instead of expanding it from the middle like
                   ;; this...
                   (push (print (list start y1 (- x start -1) dy)) (cdr rects))
                   (setf start nil))))
      (when (and y-edges (plusp dx))
        ;; start outside edge to simplify handling of edge
        (loop with live = (list (list 0 -1 0 1))
              with start = nil
              for y from -1 below (+ y1 dy)
              for in = live
              do (loop for edge = (car y-edges)
                       while (and edge (<= (first edge) y))
                       do (push (pop y-edges) live))
                 (setf live (loop for l in live
                                  for (ly nil w nil) = l
                                  unless (< (+ ly w) y)
                                    collect l))
                 (when (and in (not live))
                   (setf start y))
                 (when (and live (not in))
                   ;; fixme: put rects in an object or something
                   ;; instead of expanding it from the middle like
                   ;; this...
                   (push (print (list x1 start dx (- y start -1))) (cdr rects))
                   (setf start nil)))))))

(define-condition packing-failed (simple-error)
  ((w :reader w :initarg :w)
   (h :reader h :initarg :h))
  (:report (lambda (c s)
             (format s "Cannot pack any more rectangles (trying to pack ~sx~s)"
                     (w c) (h c)))))

(defun find-free-rect (w h rects)
  (loop with min-rect = (car rects)
     with min-d = (delta-weight w h min-rect)
     for rect in (rest rects)
     for cur-d = (delta-weight w h rect)
     ;; add case for when w and h of free rect exactly matches required w h
     when (or (< min-d 0) (and (>= cur-d 0) (< cur-d min-d)))
     do (setf min-rect rect
              min-d cur-d)
     finally (return
               (if (< min-d 0)
                   (restart-case
                       (error 'packing-failed :w w :h h)
                     (expand (dx dy)
                       :interactive (lambda ()
                                      (format t "expand by (dx dy):")
                                      (read))
                       (when (or (not (integerp dx))
                                 (not (integerp dy))
                                 (minusp dx) (minusp dy)
                                 (and (zerop dx) (zerop dy)))
                         (error "can't expand packing by ~sx~s" dx dy))
                       (grow-rects rects dx dy)
                       (find-free-rect w h rects)))
                   min-rect))))

(defun intersectsp (r0 r1)
  (with-rect (x0 y0 w0 h0) r0
    (with-rect (x1 y1 w1 h1) r1
      (and (< x0 (+ x1 w1))
           (> (+ x0 w0) x1)
           (< y0 (+ y1 h1))
           (> (+ y0 h0) y1)))))


(defun splitsp (coord coord-from coord-to)
  (> coord-to coord coord-from))

(defun subdivide-rect (rect placed)
  (if (intersectsp placed rect)
      (with-rect (x y w h) rect
        (with-rect (xp yp wp hp) placed
          (let (result)
            ;; left part
            (when (splitsp xp x (+ x w))
              (push (list x y (- xp x) h) result))
            ;; right part
            (when (splitsp (+ xp wp) x (+ x w))
              (push (list (+ xp wp) y (- (+ x w) (+ xp wp)) h) result))
            ;; bottom
            (when (splitsp yp y (+ y h))
              (push (list x y w (- yp y)) result))
            ;; top
            (when (splitsp (+ yp hp) y (+ y h))
              (push (list x (+ yp hp) w (- (+ y h) (+ yp hp))) result))
            result)))
      (list rect)))

(defun subdivide-intersecting (rect free-rects)
  (loop for free-rect in free-rects appending (subdivide-rect free-rect rect)))

(defun containsp (outer inner)
  (with-rect (x0 y0 w0 h0) outer
    (with-rect (x1 y1 w1 h1) inner
      (and (>= (+ x0 w0) (+ x1 w1) x1 x0)
           (>= (+ y0 h0) (+ y1 h1) y1 y0)))))

(defun normalize-free-space (rects)
  (loop with rest-filtered = rects
     for (rect . rest) = rest-filtered until (null rect)
     collecting
       (loop with contained-p = nil
          for other-rect in rest
          unless (containsp rect other-rect) collect other-rect into filtered
          when (and (not contained-p) (containsp other-rect rect))
          do (setf contained-p t)
          finally
            (setf rest-filtered filtered)
            (return (unless contained-p rect)))
     into result
     finally (return (delete-if #'null result))))

(defun subrect (w h rect)
  (with-rect (x y) rect
    (list x y w h)))

(defun place-rect (w h free-rects)
  (let* ((free-rect (find-free-rect w h free-rects))
         (result (subrect w h free-rect)))
    (values result (normalize-free-space (subdivide-intersecting result
                                                                 free-rects)))))

(defun pack (dimensions &key width height)
  (labels ((largest-side (el)
             (max (second el) (third el)))
           (shortest-side (el)
             (min (second el) (third el)))
           (short-side-last ()
             (sort dimensions #'> :key #'shortest-side))
           (double-sorted-dimensions ()
             (sort (short-side-last) #'> :key #'largest-side)))

  (loop with free-rects = (list (list 0 0 width height))
     for (id rect-width rect-height) in (double-sorted-dimensions) collect
       (multiple-value-bind (rect new-free-rects)
           (place-rect rect-width rect-height free-rects)
         (setf free-rects new-free-rects)
         (with-rect (x y w h) rect
           (list id x y w h))))))
