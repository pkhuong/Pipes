;; Suspension: overhead is pretty heavy. THINK.

#||
(define-vop (data-vector-set-with-offset/simple-array-double-float)
  (:note "inline array store")
  (:translate data-vector-set-with-offset)
  (:policy :fast-safe)
  (:args (object :scs (descriptor-reg))
         (index :scs (any-reg))
         (value :scs (double-reg) :target result))
  (:info offset)
  (:arg-types simple-array-double-float positive-fixnum
              (:constant (constant-displacement other-pointer-lowtag
                                                8 vector-data-offset))
              double-float)
  (:results (result :scs (double-reg)))
  (:result-types double-float)
  (:generator 20
     (inst movsd (make-ea-for-float-ref object index offset 8) value)
     (unless (and (eql :normal (sb-c::tn-kind result))
                  (null (sb-c::tn-reads result)))
       (move result value))))
||#

#+debug
(declaim (optimize (debug 2)))
(defclass node-base ()
  ((info :accessor info :documentation "Mutable slot for analyses"
         :initform nil)
   (hash :reader hash :initform (random (1+ most-positive-fixnum))
         :documentation "EQL hashes can have issues")
   (output :reader output :initform 0 :initarg output
           :documentation "Number of values to return; all if T.")
   (input-clock-domain :accessor input-clock-domain)))

(defun node-eql (x y)
  (eql x y))
(defun hash-node-eql (x)
  (if (typep x 'node-base)
      (hash x)
      (sxhash x)))
(define-hash-table-test node-eql hash-node-eql)

;; stream nodes are well-behaved: they produce exactly one output for
;; each input.
(defclass stream-node (node-base) ())
;; scan nodes are even better behaved: they never introduce skips.
(defclass scan-node (stream-node) ())
;; arbitrary nodes aren't so nice: they produce an arbitrary number of
;; outputs for each input.
(defclass node (node-base) ())

(defclass clock (node) ())
;; sinks are special nodes: they can't have any use (output)
(defclass sink (node) ())
;; sources are also special: they don't have any input,
;;  except an implicit dependency on the external clock.
(defclass source (stream-node) ())

;; Protocol
(defgeneric nodep (node)
  (:method ((node node-base))
    t)
  (:method (not)
    nil))
(defgeneric sinkp (node)
  (:documentation "node acts as a sink")
  (:method ((node sink))
    t)
  (:method (node)
    nil))
(defgeneric sourcep (node)
  (:documentation "node acts as a source")
  (:method ((node source))
    t)
  (:method (node)
    nil))
(defgeneric input-nodes (node)
  (:documentation "node -> sequence of input nodes")
  (:method ((node source))
    '()))
(defgeneric (setf input-nodes) (inputs node)
  (:method (inputs (node source))
    (assert (null inputs))
    inputs))
(defgeneric input-names (node)
  (:documentation "node -> sequence of input names (symbols)")
  (:method ((node source))
    '()))
(defgeneric streamlyp (node)
  (:documentation "returns T if node is streamly, producing exactly
one value for each input.")
  (:method ((node stream-node))
    t)
  (:method ((node source))
    t)
  (:method ((node node-base))
    nil))
(defgeneric scanlyp (node)
  (:documentation "returns T if node is scanly, producing exactly
one value for each input, and never introducing skips.")
  (:method ((node scan-node))
    t)
  (:method ((node source))
    t)
  (:method ((node node-base))
    nil))
(defgeneric flushablep (node)
  (:method ((node sink))
    nil)
  (:method (node)
    (eql 0 (output node))))
(defgeneric expansion (node multi-use-p output-count)
  (:documentation
   "
node multiple-anti-deps -> environment-substitution,
                            body-substitution,
                            pass-form,
                            value-form"))

#||
Substitutions are just functions that take a form to splice in, and
return a new form.  The advantage is that the substitution decides
where to splice the form in, e.g., in the middle of a let.

If you ever wished that quasiquotes were more modular, substitutions
might be the pattern you're looking for.
||#

(defgeneric clock-domain (node)
  (:documentation
   "Compute the clock domain for a node, or *how* to compute it.")
  (:method ((node source))
    :clock)
  (:method ((node node))
    :propagate)
  (:method ((node stream-node))
    :propagate))

;; Implementations
(defclass list-source (source)
  ((list :reader list-source :initarg list-source)))

(defmethod expansion ((node list-source) _ __)
  (let ((list (gensym "LIST"))
        (head (gensym "HEAD")))
    (values `((,list ,(list-source node)))
            `((type list ,list))
            (lambda (k)
              `(let ((,head (pop ,list)))
                 ,k))
            nil head
            :test
            `(null ,list))))

(defclass iota-source (source)
  ((type :accessor iota-type :initarg type :initform '(and unsigned-byte fixnum))
   (max  :accessor iota-max  :initarg max  :initform most-positive-fixnum)
   (max-var :reader max-var :initform (gensym "MAX"))
   (idx-var :reader idx-var :initform (gensym "IDX"))))
(defmethod expansion ((node iota-source) _ __)
  (let ((idx (idx-var node))
        (max (max-var node)))
    (values `((,max ,(iota-max node))
              (,idx 0))
            `((type ,(iota-type node) ,idx ,max)
              (close ,max))
            (lambda (k)
              `(progn
                 ,k
                 (incf ,idx)))
            nil
            idx
            :test
            `(>= ,idx ,max)
            :output idx)))

(defclass shared-iota-source (iota-source)
  ((parent :reader parent :initarg parent)))
(defmethod expansion ((node shared-iota-source) _ __)
  (let ((max (max-var node)))
    (values `((,max ,(iota-max node)))
            `((type ,(iota-type node) ,max)
              (close ,max)
              (ignorable ,max))
            'identity
            nil
            (idx-var (parent node))
            :test nil
            :inner-wrap
            (lambda (k)
              `(progn
                 (setf ,(max-var (parent node))
                       (min ,(max-var (parent node)) ,max))
                 ,k))
            :output (idx-var (parent node)))))
(defmethod clock-domain ((node shared-iota-source))
  (info (parent node)))

#+nil
(defclass count-node (scan-node single-input-node)
  ((type :accessor count-type :initarg type      :initform '(and unsigned-byte fixnum))
   (var  :reader    count-var :initarg count-var :initform (gensym "COUNT"))))
#+nil
(defmethod expansion ((node count-node) _ output)
  (let ((var (count-var node)))
    (values `((,var 0))
            `((type ,(count-type node) ,var))
            (lambda (k)
              `(progn
                 ,k
                 (incf ,var)))
            nil
            var
            :output var)))
#+nil
(defclass shared-count-node (scan-node nullary-node)
  ((parent :reader parent :initarg parent)))
#+nil
(defmethod expansion ((node shared-count-node) _ output)
  (let* ((parent (parent node))
         (var    (etypecase parent
                   (count-node (count-var parent))
                   (iota-source (idx-var parent)))))
    (values nil nil
            'identity
            nil
            var
            :output var)))
#+nil
(defmethod clock-domain ((node shared-count-node))
  (info (parent node)))

(defclass vector-source (source)
  ((vector :reader vector-source :initarg vector-source)
   (eltype :initarg eltype :initform '*)))
(defmethod expansion ((node vector-source) _ __)
  (let ((vec (gensym "VEC"))
        (len (gensym "LEN"))
        (idx (gensym "IDX"))
        (value (gensym "VALUE")))
    (values `((,vec ,(vector-source node))
              (,len (length ,vec))
              (,idx 0))
            `((close ,vec ,len)
              (type (and unsigned-byte fixnum) ,idx))
            (lambda (k)
              `(let ((,value (aref ,vec ,idx)))
                 (incf ,idx)
                 ,k))
            nil value
            :test
            `(>= ,idx ,len))))

(defclass single-input-node (node-base)
  ((input-name :initarg input-name)
   (input-node :initarg input-node)))

(defmethod input-nodes ((node single-input-node))
  (list (slot-value node 'input-node)))
(defmethod (setf input-nodes) (inputs (node single-input-node))
  (assert (typep inputs '(cons t null)))
  (setf (slot-value node 'input-node) (first inputs))
  inputs)
(defmethod input-names ((node single-input-node))
  (list (slot-value node 'input-name)))

(defclass list-sink (sink single-input-node) ())

(defmethod expansion ((node list-sink) _ __)
  _
  (let ((list (gensym "LIST"))
        (input (slot-value node 'input-name)))
    (values `((,list '())) `((type list ,list))
            (lambda (k)
              (assert (null k))
              `(unless (? ,input)
                 (push ($ ,input) ,list)))
            nil nil
            :output
            `(values (nreverse ,list)))))

(defclass vector-sink (sink single-input-node)
  ((element-type :reader element-type
                 :initarg :element-type
                 :initform 't)))

(defun generate-flatten-push-vector (type)
  `(lambda (stack last last-length)
     (declare (type list stack)
              (type (simple-array ,type 1) last)
              (type (and unsigned-byte fixnum) last-length)
              (optimize speed (safety 0)))
     (setf stack (reverse stack))
     (let* ((total-length (reduce #'+ stack
                                  :key (lambda (x)
                                         (length (truly-the (simple-array ,type 1) x)))
                                  :initial-value last-length))
            (output       (if (<= total-length (length last))
                              (sb-kernel:%shrink-vector last total-length)
                              (make-array total-length
                                          :element-type (array-element-type last))))
            (start        0))
       (declare (type (mod #.most-positive-fixnum) total-length start)
                (type (simple-array ,type 1) output))
       (replace output last :start1 (- total-length last-length))
       (map nil (lambda (vec)
                  (let ((vec (truly-the (simple-array ,type 1) vec)))
                    (replace output vec :start1 start)
                    (incf start (length vec))))
            stack)
       output)))

(defun flatten-push-vector (stack last last-length)
  (declare (type (simple-array * 1) last))
  (let ((table (load-time-value (make-hash-table :test #'eql)))
        (type  (array-element-type last)))
    (funcall (or (gethash type table)
                 (setf (gethash type table)
                       (compile nil (generate-flatten-push-vector type))))
             stack last last-length)))

(defmethod expansion ((node vector-sink) _ __)
  (let ((vector (gensym "VECTOR"))
        (stack  (gensym "STACK"))
        (max    (gensym "MAX"))
        (idx    (gensym "IDX"))
        (input  (slot-value node 'input-name))
        (eltype (element-type node)))
    (values `((,vector (make-array 16
                                   :element-type ',eltype))
              (,stack  nil)
              (,max    16)
              (,idx    0))
            `((type (simple-array ,eltype 1) ,vector)
              (type (and unsigned-byte fixnum) ,max)
              (type (mod #.most-positive-fixnum) ,idx))
            (lambda (k)
              (assert (null k))
              `(unless (? ,input)
                 (when (= ,max ,idx)
                   (push ,vector ,stack)
                   (setf ,max (* 2 ,max)
                         ,vector (make-array ,max :element-type ',eltype)
                         ,idx 0))
                 (locally (declare (optimize
                                    (sb-c::insert-array-bounds-checks 0)))
                   (setf (aref ,vector ,idx) ($ ,input)))
                 (incf ,idx)))
            nil nil
            :output
            `(flatten-push-vector ,stack ,vector ,idx))))

#+nil
(defmethod expansion ((node vector-sink) _ __)
  (let ((vector (gensym "VECTOR"))
        (max    (gensym "MAX"))
        (idx    (gensym "IDX"))
        (input  (slot-value node 'input-name))
        (eltype (element-type node)))
    (values `((,vector (make-array 16
                                   :element-type ',eltype))
              (,max    16)
              (,idx    0))
            `((type (simple-array ,eltype 1) ,vector)
              (type (and unsigned-byte fixnum) ,max)
              (type (mod #.most-positive-fixnum) ,idx))
            (lambda (k)
              (assert (null k))
              `(unless (? ,input)
                 (when (= ,max ,idx)
                   (setf ,max (* 2 ,max)
                         ,vector (replace (make-array ,max :element-type ',eltype)
                                          ,vector)))
                 (locally (declare (optimize
                                    (sb-c::insert-array-bounds-checks 0)))
                   (setf (aref ,vector ,idx) ($ ,input)))
                 (incf ,idx)))
            nil nil
            :output
            `(sb-kernel:%shrink-vector ,vector ,idx))))

(defclass nullary-node (node-base) ())
(defmethod input-nodes ((node nullary-node))
  '())
(defmethod (setf input-nodes) (input-nodes (node nullary-node))
  (assert (null input-nodes))
  input-nodes)
(defmethod input-names ((node nullary-node))
  '())

(defclass finally (sink nullary-node)
  ((form :initarg form)))
(defmethod clock-domain ((node finally))
  :clock)
(defmethod expansion ((node finally) count _)
  (values nil nil 'identity nil nil
          :output (slot-value node 'form)))

(defclass constant (source nullary-node)
  ((form :initarg form)))
(defmethod clock-domain ((node constant))
  :clock)
(defmethod expansion ((node constant) count _)
  (let ((temp (gensym "TEMP")))
    (values `((,temp ,(slot-value node 'form))) nil
            'identity
            nil
            temp
            :test nil)))

(defclass map-node (scan-node)
  ((input-names :reader input-names :initarg input-names)
   (input-nodes :accessor input-nodes :initarg input-nodes)
   (function    :reader map-function :initarg function)))
(defconstant +skip+ '+skip+)
(defmethod expansion ((node map-node) count _)
  (let ((value (gensym "VALUE"))
        (names (input-names node)))
    (multiple-value-call #'values
      nil nil
      (if (<= count 1)
          (values
            'identity
            `(or ,@(mapcar (lambda (input)
                             `(? ,input))
                           names))
            `(,(map-function node)
               ,@(mapcar (lambda (input)
                           `($ ,input))
                         names)))
          (values
            (lambda (k)
              `(let ((,value (if (or ,@(mapcar (lambda (input)
                                                 `(? ,input))
                                               names))
                                 +skip+
                                 (,(map-function node)
                                   ,@(mapcar (lambda (input)
                                               `($ ,input))
                                             names)))))
                 ,k))
            `(eql ,value '+skip+)
            value)))))

(defclass scanl-node (scan-node single-input-node)
  ((initial-value    :initarg initial-value)
   (accumulator-type :initarg accumulator-type :initform 't)
   (function         :initarg function)))
(defmethod expansion ((node scanl-node) count _)
  (let ((acc  (gensym "ACC"))
        (skip (gensym "SKIP"))
        (input (slot-value node 'input-name)))
    (values `((,acc ,(slot-value node 'initial-value)))
            `((type ,(slot-value node 'accumulator-type) ,acc))
            (lambda (k)
              `(let ((,skip (? ,input)))
                 (unless ,skip
                   (setf ,acc (,(slot-value node 'function)
                                ,acc
                                ($ ,input))))
                 ,k))
            skip
            acc
            :output acc)))

(defclass filter-node (stream-node)
  ((input-names :reader   input-names :initarg input-names)
   (input-nodes :accessor input-nodes :initarg input-nodes)))
(defmethod expansion ((node filter-node) count __)
  (assert (= 2 (length (input-names node))))
  (destructuring-bind (predicate value) (input-names node)
    (let ((skip (gensym "SKIP")))
      (values nil nil
              (lambda (k)
                `(let ((,skip (or (? ,predicate)
                                  (? ,value)
                                  (not ($ ,predicate)))))
                   ,k))
              skip
              `($ ,value)))))

;; Stuff
(defun map-nodes (function nodes &optional type)
  (map type function nodes))

(defun set-info (nodes &optional value)
  (map-nodes (lambda (node)
               (setf (info node) value))
             nodes))

(defun map-info (function nodes)
  (map-nodes (lambda (node)
               (setf (info node) (funcall function node (info node))))
             nodes))

(defun dag-ordered-p (nodes)
  (set-info nodes)
  (let ((nonce (list nil)))
    (map-info (lambda (node info) info
                (unless (every (lambda (node)
                                 (eql nonce (info node)))
                               (input-nodes node))
                  (return-from dag-ordered-p nil))
                nonce)
              nodes))
  t)

(defun annotate-uses (nodes)
  (set-info nodes)
  (map-nodes (lambda (node)
               (map nil (lambda (input)
                          (push node (info input)))
                    (input-nodes node)))
             nodes)
  (let ((map (make-hash-table :test #'node-eql)))
    (map-info (lambda (node info)
                (when (sinkp node)
                  (assert (null info)))
                (setf (gethash node map)
                      (nreverse info)))
              nodes)
    map))

(define-modify-macro nreversef () nreverse)

(defun propagate-clock-domain (nodes clock)
  (set-info nodes)
  ;; use info to memoise the clock domain
  ;; store the node -> transitive children
  ;; mapping in a hash table
  (let ((map (make-hash-table :test #'node-eql)))
    (map-info (lambda (node info) info
                ;; check consistency
                (destructuring-bind (&optional input &rest inputs)
                    (input-nodes node)
                  (when input
                    (assert (every (lambda (x)
                                     (eql (info input) (info x)))
                                   inputs))))
                ;; propagate
                (let ((domain (clock-domain node)))
                  (etypecase domain
                    ((eql :clock)
                       (setf domain clock))
                    ((eql :propagate)
                       (assert (input-nodes node))
                       (setf domain (info (first (input-nodes node)))))
                    (node))
                  (push node (gethash domain map))
                  (setf (input-clock-domain node) domain)
                  (if (streamlyp node)
                      domain
                      node)))
              nodes)
    (map-nodes (lambda (node)
                 (when (gethash node map)
                   (nreversef (gethash node map))))
               nodes)
    (nreversef (gethash clock map))
    map))

(defun merge-iotas (nodes)
  (let ((domain-iotas (make-hash-table :test 'node-eql))
        (replacements (make-hash-table :test 'node-eql)))
    (flet ((replace-inputs (node)
             (setf (input-nodes node)
                   (mapcar (lambda (node)
                             (gethash node replacements node))
                           (input-nodes node)))
             node))
      (map-into nodes (lambda (node)
                        (cond ((typep node 'iota-source)
                               (let* ((domain (input-clock-domain node))
                                      (parent (gethash domain domain-iotas)))
                                 (cond (parent
                                        (setf (iota-type parent)
                                              `(and ,(iota-type parent)
                                                    ,(iota-type node)))
                                        (setf (gethash node replacements)
                                              (make-instance 'shared-iota-source
                                                             'parent parent
                                                             'max  (iota-max node)
                                                             'type (iota-type node)
                                                             'output (output node))))
                                       (t
                                        (setf (gethash domain domain-iotas) node)))))
                              (t
                               (replace-inputs node))))
                nodes))))

(defun adjoin-transitive-child (node table)
  (labels ((walk (parent)
             (let ((key (cons node parent)))
               (unless (gethash key table)
                 (setf (gethash key table) t)
                 (map nil #'walk (input-nodes parent))))))
    (map nil #'walk (input-nodes node)))
  table)

(defun find-skip-root (node transitive-table)
  (cond ((info node))
        ((not (scanlyp node))
         (setf (info node) node))
        ((sourcep node)
         (setf (info node) (input-clock-domain node)))
        (t
         (let* ((inputs (mapcar (lambda (node)
                                  (find-skip-root node transitive-table))
                                (input-nodes node)))
                (parent (find-if (lambda (root)
                                   (every (lambda (input)
                                            (or (eql root input)
                                                (gethash (cons input root)
                                                         transitive-table)))
                                          inputs))
                                 inputs)))
           (setf (info node) (or parent node))))))

#+nil
(defun merge-counts (nodes)
  (set-info nodes)
  (let ((children (reduce #'adjoin-transitive-child
                          nodes
                          :from-end t
                          :initial-value (make-hash-table :test 'node-eql)))
        (root-counts  (make-hash-table :test 'node-eql))
        (replacements (make-hash-table :test 'node-eql)))
    (flet ((replace-inputs (node)
             (setf (input-nodes node)
                   (mapcar (lambda (node)
                             (gethash node replacements node))
                           (input-nodes node)))
             node))
      (map-into nodes (lambda (node)
                        (cond ((typep node 'count-node)
                               (let* ((root   (find-skip-root node children))
                                      (parent (gethash root root-counts)))
                                 (format t "~A -> ~A~%" node root)
                                 (cond (parent
                                        (setf (count-type parent)
                                              `(and ,(count-type node)
                                                    ,(count-type parent)))
                                        (setf (gethash node replacements)
                                              (make-instance 'shared-count-node
                                                             'parent parent
                                                             'output (output node))))
                                       ((typep root 'clock)
                                        (let ((new-node (make-instance
                                                         'iota-source
                                                         'output (output node))))
                                          (setf (gethash node replacements) new-node
                                                (gethash node root-counts)  new-node)))
                                       (t
                                        (setf (gethash root root-counts)
                                              (replace-inputs node))))))
                              (t
                               (replace-inputs node))))
                nodes))))

(defconstant +unbound+ '+unbound+)

(defun +bound+p (x)
  (not (eql x +unbound+)))

;; FIXME: higher level data to enable suspension
;;  1. bindings + initial value + declarations
;;  2. environment
;;  3. outer wrapper
;;  4. clean-up
(defstruct (expansion
             (:constructor make-expansion
              (bindings declarations body pass value
                    &key (test +unbound+) (output +unbound+)
                    (outer-wrap 'identity)
                    (inner-wrap 'identity))))
  bindings declarations body pass value
  test
  output
  outer-wrap inner-wrap)

(defun annotate-with-expansion (nodes uses)
  (map-info (lambda (node info) info
              (let ((expansion
                     (multiple-value-call #'make-expansion
                       (expansion node
                                  (length (gethash node uses))
                                  (output node)))))
                (when (sourcep node)
                  (assert (+bound+p (expansion-test expansion))))
                (when (sinkp node)
                  (assert (+bound+p (expansion-output expansion))))
                expansion))
            nodes))

(defun environment-builder (nodes accessor)
  (let ((environments (map 'simple-vector
                           (lambda (node)
                             (funcall accessor (info node)))
                           nodes)))
    (lambda (k)
      (reduce #'funcall environments
              :from-end t
              :initial-value k))))

;; alist of name -> (pass-form value-form)
(define-symbol-macro %node-expansions% ())

(defmacro ? (name &environment env)
  (let ((expansions (macroexpand-1 '%node-expansions% env)))
    (second (or (assoc name expansions)
                (error "Unknown node ~S" name)))))

(defmacro $ (name &environment env)
  (let ((expansions (macroexpand-1 '%node-expansions% env)))
    (third (or (assoc name expansions)
               (error "Unknown node ~S" name)))))

;; disable (setf ?) and (setf $)
(defsetf ? (name) (value)
  (declare (ignore name value))
  (error "Can't ~S" '(setf ?)))
(defsetf $ (name) (value)
    (declare (ignore name value))
  (error "Can't ~S" '(setf $)))

(defun wrap-body-substitutions (nodes base-assoc)
  (map-nodes (lambda (node)
               (let* ((info (info node))
                      (alist (nconc (mapcar
                                     (lambda (name node)
                                       (list name
                                             (expansion-pass  (info node))
                                             (expansion-value (info node))))
                                     (input-names node)
                                     (input-nodes node))
                                    base-assoc))
                      (body  (expansion-body info)))
                 (assert (typep body '(or function symbol)))
                 (setf (expansion-body info)
                       (lambda (k)
                         `(symbol-macrolet ((%node-expansions% ,alist))
                            ,(funcall body k))))
                 (unless (constantp (expansion-pass info))
                   (setf (expansion-pass info)
                         `(symbol-macrolet ((%node-expansions% ,alist))
                            ,(expansion-pass info))))
                 (unless (constantp (expansion-value info))
                   (setf (expansion-value info)
                         `(symbol-macrolet ((%node-expansions% ,alist))
                            ,(expansion-value info))))
                 info))
             nodes))

(defun combine-forms (substitution domains clock)
  (labels
      ((domainp (domain)
         (not (streamlyp domain)))
       (body (domain)
         (assert (domainp domain))
         (reduce (lambda (child k)
                   (let ((exp (expansion-body (info child))))
                     (cond ((domainp child)
                            `(progn
                               ,(funcall exp (body child))
                               ,k))
                           (t
                            (funcall exp k)))))
                 (gethash domain domains)
                 :from-end t
                 :initial-value '())))
    (funcall substitution (body clock))))

(defun gensym-list (count &optional (base "G"))
  (unless (stringp base)
    (setf base (string base)))
  (loop repeat count collect (gensym base)))

(defun build-output-expression (nodes)
  (let ((tail (find t nodes :key #'output)))
    (cond (tail
           (assert (= 1 (count t nodes :key #'output)))
           (assert (+bound+p (expansion-output
                              (info tail))))
           (expansion-output (info tail)))
          (t
           (let* ((forms '())
                  (vars
                   (loop for node in nodes
                         for output = (output node)
                         for form = (expansion-output (info node))
                         when (plusp output)
                           append
                        (let ((vars (gensym-list output)))
                          (assert (+bound+p form))
                          (push `(multiple-value-bind ,vars ,form)
                                forms)
                          vars))))
             (reduce (lambda (form k)
                       `(,@form ,k))
                     (nreverse forms)
                     :from-end t
                     :initial-value `(values ,@vars)))))))

(defun build-bindings (nodes)
  (let ((info (mapcar #' info nodes)))
    (lambda (k)
      (reduce (lambda (info k)
                (let ((bindings (expansion-bindings info))
                      (declare  (expansion-declarations info)))
                  (setf declare (remove-if (lambda (declaration)
                                             (typep declaration '(cons (eql close))))
                                           declare))
                  (cond (bindings
                         `(let* ,bindings
                            ,@(when declare
                                `((declare ,@declare)))
                            ,k))
                        (declare
                         `(locally (declare ,@declare)
                            ,k))
                        (t k))))
              info
              :from-end t :initial-value k))))

(defun bound-vars (nodes)
  (loop for node in nodes
        for info = (info node)
        nconc (mapcar (lambda (binding)
                        (if (atom binding)
                            binding
                            (first binding)))
                      (expansion-bindings info))))

(defun closed-vars (nodes)
  (let ((vars '()))
    (loop for node in nodes
          for info = (info node)
          do (loop for declaration in (expansion-declarations info)
                   do (when (typep declaration '(cons (eql close)))
                        (setf vars (union vars (rest declaration))))))
    vars))

(defun declarations (nodes)
  (loop for node in nodes
        for info = (info node)
        append (remove-if (lambda (declaration)
                            (typep declaration '(cons (eql close))))
                          (expansion-declarations info))))

(defun compose (&rest functions)
  (lambda (x)
    (reduce #'funcall functions :from-end t :initial-value x)))

(defvar *suspend-var*)

(defun compile-nodes (nodes &optional environment)
  (assert (dag-ordered-p nodes))
  (let* ((uses  (annotate-uses nodes))
         (clock (make-instance 'clock))
         (domains (propagate-clock-domain nodes clock))
         (*suspend-var* (gensym "SUSPEND")))
    (setf nodes (merge-iotas nodes))
    (annotate-uses nodes)
    (setf domains (propagate-clock-domain nodes clock))
    (annotate-with-expansion nodes uses)
    (let* ((outer-env-builder (environment-builder
                               nodes
                               #'expansion-outer-wrap))
           (inner-env-buider  (environment-builder
                               nodes
                               #'expansion-inner-wrap))
           (binding-builder   (build-bindings nodes))
           (bound-vars        (bound-vars nodes))
           (closed-vars       (closed-vars nodes))
           (copy-vars         (set-difference bound-vars closed-vars))
           (declarations      (declarations nodes))
           (self              (gensym "SELF"))
           (suspend           *suspend-var*)
           (gensyms           (gensym-list (length copy-vars)))
           (loop   (gensym "LOOP"))
           (middle (lambda (k)
                     `(flet ((,suspend ()
                               (return-from ,self
                                 (let ,(mapcar 'list gensyms copy-vars)
                                   (declare (optimize (safety 0)))
                                   (lambda ()
                                     (,self ,@gensyms))))))
                        (declare (inline ,suspend))
                        (tagbody
                           ,loop
                           (let ((,*suspend-var* nil))
                             (unless (or
                                      ,@(loop for node in nodes
                                              when (sourcep node)
                                                collect (expansion-test
                                                         (info node))))
                               (when ,*suspend-var*
                                 (,suspend))
                               (let ((,*suspend-var* nil))
                                 ,k
                                 (unless
                                     (and
                                      ,@(loop for node in nodes
                                              for test = (expansion-test
                                                          (info node))
                                              unless (sourcep node)
                                                collect (if (+bound+p test)
                                                            test
                                                            (eql 0 (output node)))))
                                   (when ,*suspend-var*
                                     (,suspend))
                                   (go ,loop))))))
                        ,(build-output-expression nodes))))
           (fun     (lambda (k)
                      `(labels ((,self (,@copy-vars &aux ,@(mapcar #'list closed-vars
                                                                 closed-vars))
                                  (declare ,@declarations)
                                  (let ,(mapcar #'list bound-vars bound-vars)
                                    (declare ,@declarations)
                                    ,(funcall middle k))))
                         (,self ,@copy-vars)))))
      (wrap-body-substitutions nodes
                               (macroexpand-1 '%node-expansions%
                                              environment))
      (combine-forms (compose outer-env-builder
                              binding-builder
                              inner-env-buider
                              fun)
                     domains clock))))
