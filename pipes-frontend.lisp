(defmacro define-define-macro (macro function variable)
  `(progn
     (defparameter ,variable (make-hash-table))
     (defmacro ,macro (name lambda-list &body body)
       `(,',function ',name
                     (sb-int:named-lambda (,',macro for ,name) (.list.)
                       (destructuring-bind ,lambda-list (rest .list.)
                         ,@body))))
     (defun ,function (name expander)
       (setf (gethash name ,variable) expander)
       name)))

(define-define-macro defoperator register-operator *operators*)
(define-define-macro defunctor   register-functor  *functors*)

(defparameter *destination* nil)
(defparameter *scope* nil)
(defparameter *graph* nil)

(defun find-var (name &key (scope *scope*) (default nil defaultp))
  (assert name)
  (cdr (or (assoc name scope)
           (if defaultp
               default
               (error "Unknown stream variable ~S" name)))))

(defun %expand-operator (form)
  (loop
   (when (nodep form)
     (push (cons *destination* form) *graph*)
     (return form))
   (when (atom form)
     (let ((node (or (cdr (assoc form *scope*))
                     (make-instance 'constant 'form form))))
       (push (cons *destination* node) *graph*)
       (return node)))
    (let ((fun (gethash (first form) *operators*)))
      (when fun
        (return (funcall fun form))))
    (let ((fun    (gethash (first form) *functors*))
          (*scope* *scope*))
      (setf form (if fun
                     (funcall fun form)
                     `(map ,@form))))))

(defun expand-operator (form
                        ;; FIXME: tailness
                        &key ((:scope *scope*) *scope*)
                             ((:dest *destination*) *destination*))
  (%expand-operator form))

(defun hook-form (form name destination)
  (cons name
        (expand-operator form
                         :dest destination)))

(defun ignorable-name (name)
  (or (null name)
      (string= name "_")))

;; FIXME: copypasta
(macrolet ((update-scope-with-binding (scope binding)
             `(destructuring-bind (name values-or-form
                                   &optional (form nil formp))
                  ,binding
                (unless formp
                  (setf form           values-or-form
                        values-or-form nil))
                (unless (listp values-or-form)
                  (setf values-or-form (list values-or-form)))
                (let ((binding (hook-form form name
                                          (cons name values-or-form))))
                  (unless (ignorable-name name)
                    (push binding ,scope))))))
  (defoperator let* ((&rest bindings) &body body)
    (let ((*scope* *scope*))
      (map nil (lambda (binding)
                 (update-scope-with-binding *scope* binding))
           bindings)
      (expand-operator `(progn ,@body))))

  (defoperator let ((&rest bindings) &body body)
    (let ((scope *scope*))
      (map nil (lambda (binding)
                 (update-scope-with-binding scope binding))
           bindings)
      (expand-operator `(progn ,@body) :scope scope))))

(defoperator progn (&body body)
  (unless body
    (push '(finally nil) body))
  (let ((body (butlast body))
        (last (car (last body))))
    (loop for form in body
          do (expand-operator form :dest (cons nil nil)))
    (expand-operator last)))

(defun generate-evals (forms)
  (let* ((bindings '())
         (gensyms  (loop for form in forms
                         for atomic = (or (atom form)
                                          (typep form '(cons (eql quote))))
                         for gensym = (if atomic
                                          form
                                          (gensym "G"))
                         do (unless atomic
                              (push `(,gensym ,form) bindings))
                         collect gensym)))
    (values (nreverse bindings) gensyms)))

(defmacro wrap-eval (forms (&rest variables) &body body)
  (let ((_bindings  (gensym "BINDINGS"))
        (_variables (gensym "VARIABLES")))
    `(multiple-value-bind (,_bindings ,_variables)
         (generate-evals ,forms)
       `(let ,,_bindings
          ,(destructuring-bind ,variables ,_variables
             ,@body)))))

(defmacro delay (&body body)
  ``(%delay ,(lambda ()
               ,@body)))

(defunctor %delay (function &rest values)
  (apply function values))

(defunctor map (function &rest values)
  (wrap-eval values (&rest values)
    (delay
      (let ((nodes     '())
            (vars      '())
            (args      '())
            (expr-args '()))
        (loop for var in values
              for node = (find-var var :default nil)
              do (cond (node
                        (push node nodes)
                        (push var vars)
                        (let ((g (gensym "G")))
                          (push g args)
                          (push g expr-args)))
                       (t
                        (push var expr-args))))
        (setf args (nreverse args))
        (make-instance 'map-node
                       'input-nodes (nreverse nodes)
                       'input-names args
                       'function `(lambda ,args
                                    (,function ,@(nreverse expr-args))))))))

(defunctor scan (function input initial-value &optional type)
  (wrap-eval (list input) (input)
    (delay
      (make-instance 'scanl-node
                     'function function
                     'input-name input
                     'input-node (find-var input)
                     'initial-value initial-value
                     'accumulator-type type))))

#+nil
(defunctor reduce (function input initial-value &optional type)
  (wrap-eval (list input) (input)
    (delay
      (make-instance 'reduce-node
                     'function function
                     'input-name input
                     'input-node (find-var input)
                     'initial-value initial-value
                     'accumulator-type type))))

(defunctor from-list (list)
  (make-instance 'list-source
                 'list-source list))

(defunctor from-vector (vector &optional (eltype '*))
  (make-instance 'vector-source
                 'vector-source vector
                 'eltype eltype))

(defunctor to-list (input)
  (wrap-eval (list input) (input)
    (delay (make-instance 'list-sink
                          'input-name input
                          'input-node (find-var input)))))

(defunctor to-vector (input &optional (type t))
  (wrap-eval (list input) (input)
    `(%delay ,(lambda ()
                (make-instance 'vector-sink
                               'input-name input
                               'input-node (find-var input)
                               :element-type type)))))

(defunctor finally (value)
  (make-instance 'finally 'form value))

(defunctor constant (value)
  (make-instance 'constant 'form value))

(defun expand-pipe-expression (expression env)
  (let* ((*scope*       '())
         (tail          (list 'tail))
         (*destination* (cons nil tail))
         (*graph*       '()))
    (expand-operator expression)
    (let ((graph (loop for ((name . dest) . node) in (nreverse *graph*)
                       do (setf (slot-value node 'output)
                                (if (eql dest tail)
                                    t
                                    0))
                       collect node)))
      (compile-nodes graph env))))

(defun expand-pipe-binder (expression body env)
  (let* ((*scope*       '())
         (*destination* (cons nil nil))
         (*graph*       '()))
    (expand-operator expression)
    (map nil (lambda (entry)
               (setf (info (cdr entry)) nil))
         *graph*)
    (let* ((vars    '())
           (graph   (loop for ((name . dest) . node) in (nreverse *graph*)
                          for length = (length dest)
                          do (when (plusp length)
                               (assert (zerop (slot-value node 'output)))
                               (setf (slot-value node 'output) length)
                               (push dest vars))
                          unless (shiftf (info node) t)
                            collect node))
           (ignores '()))
      (setf vars (mapcar (lambda (var)
                           (if (ignorable-name var)
                               (let ((temp (gensym "IGNORE")))
                                 (push temp ignores)
                                 temp)
                               var))
                         (reduce #'append (nreverse vars)
                                 :from-end t
                                 :initial-value '())))
      `(multiple-value-bind ,vars
           ,(compile-nodes graph env)
         (declare (ignore ,@(nreverse ignores)))
         ,@body))))

(defmacro pipes (pipe-expression &body body
                 &environment env)
  (if body
      (expand-pipe-binder pipe-expression body env)
      (expand-pipe-expression pipe-expression env)))
