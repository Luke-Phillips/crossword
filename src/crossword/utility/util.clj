(ns crossword.utility.util)

(def sfirst (comp second first))

(defn kmn-links
  "Returns the number of links of a complete bipartite graph, K_{m,n}."
  ([m+n]
   (quot (* m+n m+n) 4))

  ([m n]
   (* m n)))

;; error to fix in ternary arity. (rrange 2 10 3) => (3 6 9) opposed to (2 5 8)
(defn rrange
  "Equivalent to (reverse range).
  Faster than (reverse range) when resulting sequence count exceeds ~10,000,000.
  Also faster than (range x 0 -1) when resulting sequence count < ~1000."
  ([start]
   (if (> start 0)
     (let [dec-start (dec start)]
       (lazy-seq (cons dec-start (rrange dec-start))))
     nil))
  ([stop start]
   (if (> start stop)
     (let [dec-start (dec start)]
       (lazy-seq (cons dec-start (rrange stop dec-start))))
     nil))
  #_([stop possible-start by]
     (let [start (- possible-start (dec (rem possible-start by)))]
       (if (> start stop)
         (let [dec-start (dec start)]
           (lazy-seq (cons dec-start (rrange* stop (- start by) by))))
         nil))))

(defn zipvector
  [xs ys]
  (map #(vector %1 %2) xs ys))

(defn permutations
  "Return all permutations of the elements of a collection"
  [coll]
  (lazy-seq
   (if (seq (rest coll))
       (apply concat (for [x coll]
                       (map #(cons x %) (permutations (remove #{x} coll)))))
       [coll])))

(def factorials (reductions * (iterate inc 1)))

(defn factorial [n]
  (reduce * (range 1 (inc n))))

(defn big-fact [n]
  (reduce #(* (bigint %1) %2)
          (range 1 (inc n))))

(defn choose [n k]
  (/ (big-fact n) (* (big-fact (- n k)) (big-fact k))))


(defn big-choose [n k]
  (/ (big-fact n) (* (factorial (- n k)) (factorial k))))

(defn num-K-mn
  "Finds the number of combinations of K_{m,n} complete bipartite graphs, where
  m,n is constant and the links differ."
  [m n]
  (let [num-nodes (* m n)]
    (reduce +
            (map (partial choose num-nodes)
                 (range 0 (inc num-nodes))))))

(defn unchunk
  "Private function from clojure.math.combinatorics.
  Given a sequence that may have chunks, return a sequence that is 1-at-a-time
  lazy with no chunks. Chunks are good for efficiency when the data items are
  small, but when being processed via map, for example, a reference is kept to
  every function result in the chunk until the entire chunk has been processed,
  which increases the amount of memory in use that cannot be garbage
  collected."
  [s]
  (lazy-seq
   (when (seq s)
     (cons (first s) (unchunk (rest s))))))

(defmacro ifn-let
  ([pred bindings then]
   `(ifn-let ~pred ~bindings ~then nil))
  ([pred bindings then else & oldform]
   ;; (assert-args
   ;;  (vector? bindings) "a vector for its binding"
   ;;  (fn? pred) "a function for its predicate"
   ;;  (nil? oldform) "1 or 2 forms after binding vector"
   ;;  (= 2 (count bindings)) "exactly 2 forms in binding vector")
   ;; (let [form (bindings 0) val (bindings 1)]
   ;;   `(let [temp# ~val]
   ;;      (let [~form temp#]
   ;;          (if (~pred temp#)
   ;;            ~then
   ;;            ~else))
   (let [form (bindings 0) val (bindings 1)]
     `(let [temp# ~val]
        (if (~pred temp#)
          (let [~form temp#]
            ~then)
          ~else)))))

;; one recursive call by combining wet-paint with wetter-paint
#_(defn bipartite
  "Given the NODES and an adjacency list, ADJS, of a graph, determine whether it
  is bipartite.
  Returns two sets of colored nodes if bipartite or nil if not.
  The repetitive code in the 4-ary is for time efficiency."
  ([nodes adjs]
   (when (seq nodes)
     (let [node (first nodes)
           neighbors (get adjs node)]
       (if-let [{reds :reds, blues :blues, :as colored} (bipartite adjs neighbors {:reds #{node}, :blues (into #{} neighbors)} :blue)]
         (if-let [disjoint-node (some #(if ((set/union reds blues) %)
                                         false %)
                                      nodes)]
           (let [disjoint-neighbors (get adjs disjoint-node)
                 new-colored (update colored :blues into disjoint-neighbors)]
           (bipartite adjs disjoint-neighbors new-colored :blue))
           colored)))))

  ([adjs wet-paint {reds :reds, blues :blues, :as colored} color]
   (let [node (first wet-paint)
         neighbors (get adjs node)
         #_neighbors-color #_(if (= color :red) :blue :red)
         #_node-set #_(if (= color :red) reds blues)
         #_neighors-set #_(if (= color :blue) reds blues)]
     #_(when-not (some node-set neighbors)
       (if (every? neighbor-set neighbors)
         colored
         (let [wetter-paint (set/difference neighbors neighbor-set)
               new-neighbor-set (into neighbor-set neighbors)]
           (if-let [new-colored (bipartite adjs wetter-paint {:reds reds :blues new-blues} neighbors-color)]
             (recur adjs (rest wet-paint) new-colored color)))))
     (if (= color :red)
       (when-not (some reds neighbors)
         (if (every? blues neighbors)
           colored
           (let [wetter-paint (set/difference neighbors blues)
                 new-blues (into blues neighbors)]
             (if-let [new-colored (bipartite adjs wetter-paint {:reds reds :blues new-blues} :blue)]
               (recur adjs (rest wet-paint) new-colored color)))))
       (when-not (some blues neighbors)
         (if (every? reds neighbors)
           colored
           (let [wetter-paint (set/difference neighbors reds)
                 new-reds (into reds neighbors)]
             (if-let [new-colored (bipartite adjs wetter-paint {:reds new-reds :blues blues} :red)]
               (recur adjs (rest wet-paint) new-colored color)))))))))

;OLD IDEAS;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defn- combo-partitions
;;   "Returns every combination of partitioning collection 'n' into two parts,
;;   with k elements in one of the partitions."
;;   [n k]
;;   (let [num-elts (count n)
;;         num-combos (c/count-combinations n k)
;;         portion (if (= num-elts (* 2 k))
;;                   (/ num-combos 2)
;;                   num-combos)]
;;     (if-let [combos (take portion (c/combinations n k))]
;;       (map (fn [combo]
;;              (vector (vec combo)
;;                      (vec (seq (apply disj (set n) combo)))))
;;            combos)
;;       nil)))

;; (defn- bipartite-nodes
;;   "Returns lazy-seq of all combinations of nodes partitioned into two groups."
;;   [nodes]
;;   (let [half (quot (count nodes) 2)
;;         choose-ks (butlast (rrange (inc half)))]
;;     (mapcat (partial combo-partitions nodes) choose-ks)))
