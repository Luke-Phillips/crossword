(ns crossword.core
  (:require [crossword.utility.util :refer [rrange sfirst kmn-links #_choose #_bipartite]]
            [clojure.set :as set]
            [clojure.string :as str]
            #_[clojure.core.memoize :as m]
            [clojure.math.combinatorics :as c])
  (:gen-class))

(defrecord Puzzle [words adj-list placed-words initials levels cells])
(defrecord ConfigGraph [nodes links adj-list])

;;;; Printing a puzzle

(defn- letter-coords
  [cells]
  (map (fn [cell]
         (vector (first cell)
                 (get (second cell) :letter)))
       cells))

(defn- printable-letter
  "Returns a string of the letter padded with NUM-SPACES spaces.
  Ex.
  (printable-letter \"a\" 1)
  => \" a\""
  [letter num-spaces]
  (str (reduce (fn [s _]
                 (str s \space))
               "" (range num-spaces))
       letter))

(defn- printable-row
  ([pad row]
   (printable-row "" row pad))

  ([acc row pad]
   (if-not (seq row) acc
     (let [letter (second (first row))
           col (ffirst (first row))
           num-spaces (- col pad)
           printable (printable-letter letter num-spaces)]
       (recur (str acc printable) (rest row) (inc col))))))

(defn printable-puzzle
  [puzzle]
  (let [cells (:cells puzzle)]
    (when-not (empty? cells)
      (let [letter-coords (letter-coords cells)
            x-sorted (sort-by ffirst letter-coords)
            xy-sorted (sort-by sfirst > x-sorted)
            sorted (sort-by (comp last first) xy-sorted)
            left-justification (apply min (map ffirst sorted))
            components (partition-by (comp last first) sorted)
            components-rows (map #(partition-by sfirst %) components)
            unplaced-words (set/difference (:words puzzle) (:placed-words puzzle))]
        (str/join "\n\n"
                  (into (map (fn [rows]
                               (str/join "\n"
                                         (map (partial printable-row left-justification)
                                              rows)))
                             components-rows)
                        unplaced-words))))))

(defn print-puzzle
  "Prints a visually pleasing ascii crossword puzzle"
  [puzzle]
  (println (printable-puzzle puzzle)))

;;;; Miscellaneous

(defmulti adj-coords (fn [_ dir] dir))
(defmethod adj-coords :up
  [[x y z] dir]
  [x (inc y) z])
(defmethod adj-coords :down
  [[x y z] dir]
  [x (dec y) z])
(defmethod adj-coords :left
  [[x y z] dir]
  [(dec x) y z])
(defmethod adj-coords :right
  [[x y z] dir]
  [(inc x) y z])
(defmethod adj-coords :default
  [[x y z] dir]
  [x y z])

(defn level
  "Returns the level of a cell or initial (works on either)."
  [cell-or-initial]
  ((first cell-or-initial) 2))

(defn adjacency-list
  "Returns an adjacency list implemented as a map of words to sets of adjacent
  words."
  [words crosses]
  (as-> {} adj-list
    (reduce #(assoc %1 %2 #{}) adj-list words)
    (reduce (fn [word-adjs cross]
              (let [word1 (first cross)
                    word2 (second cross)]
                (-> word-adjs
                    (update word1 conj word2)
                    (update word2 conj word1))))
            adj-list crosses)))

;;;; Validating a puzzle

(defn- valid-cell-pair?
  [cell1 cell2]
  (some (:memberships (second cell1))
        (:memberships (second cell2))))

(defn- valid-puzzle?
  [puzzle]
  (let [cells (get puzzle :cells)
        cells-to-check (filter #(even? (+ (ffirst %) (sfirst %))) cells)]
    (every? (fn [cell]
              (let [cell-coords (first cell)
                    adj-cell-coords (map (partial adj-coords cell-coords)
                                         [:up :down :left :right])
                    adj-cells (keep #(find cells %) adj-cell-coords)]
                (every? (partial valid-cell-pair? cell) adj-cells)))
            cells-to-check)))

;;;; Constructing a puzzle

(defn- place-letter
  "Returns an updated PUZZLE with the LETTER and its associated WORD
  placed/updated in the CELL, or nil if the LETTER cannot be placed."
  [puzzle coord letter word]
  (if-let [{placed-letter :letter memberships :memberships} (get-in puzzle [:cells coord])]
    (if-let [adj-words (get-in puzzle [:adj-list word])]
        (when (and (= placed-letter letter)
                   (= 1 (count memberships))
                   (adj-words (first memberships)))
          (update-in puzzle [:cells coord :memberships] conj word)))
    (assoc-in puzzle [:cells coord] {:letter letter
                                    :memberships #{word}})))

(defn- place-letters
  "Returns an updated PUZZLE with the LETTERS and their associated WORD
  placed/updated in their respective CELLS, or nil if the LETTERS cannot be
  placed."
  [puzzle coords letters word]
  (if (empty? coords)
    puzzle
    (when-let [updated-puzzle (place-letter puzzle (first coords) (first letters) word)]
      (recur updated-puzzle (rest coords) (rest letters) word))))

(defn- word-cell-coords
  "Return a line of adjacent cells starting at START-CELL."
  ([initial-coord num-coords direction]
   (when-not (= 0 num-coords)
     (let [next-coord (adj-coords initial-coord direction)]
       (word-cell-coords [initial-coord] next-coord num-coords direction))))

  ([acc-coords coord num-coords direction]
   (if (<= num-coords 1) acc-coords
       (let [next-coord (adj-coords coord direction)
             coords (conj acc-coords coord)]
         (recur coords next-coord (dec num-coords) direction)))))

(defn- place-word
  "Return an updated PUZZLE with the WORD placed horizontally or vertically
  (according to ORIENTATION) starting at COORD, or nil if the WORD cannot
  be placed.
  Words can be placed iff all their letters can be placed (see place-letter)."
  [puzzle [coord orientation :as initial] word]
  (let [num-coords (count word)
        direction (if (= orientation :vertical) :down :right)
        cell-coords (word-cell-coords coord num-coords direction)
        letters (str/split word #"")]
    (when-let [updated-puzzle (place-letters puzzle cell-coords letters word)]
      (-> updated-puzzle
          (update :placed-words conj word)
          (update :initials assoc word initial)))))

(defn consolidate-levels
  "Returns an updated PUZZLE with all cells above level LVL shifted down a
  level."
  [puzzle lvl]
  (let [cells (:cells puzzle)]
    (when cells
      (assoc puzzle :cells
             (reduce (fn [consolidated-cells [[x y z] contents :as cell]]
                       (if (< lvl (level cell))
                         (-> consolidated-cells
                             (dissoc (first cell))
                             (assoc [x y (dec z)] contents))
                         consolidated-cells))
                     cells cells)))))

(defn delete-level
  "Returns an updated PUZZLE with all cells on level LVL removed."
  [puzzle lvl]
  (let [cells (:cells puzzle)]
    (when cells
      (-> puzzle
          (assoc :cells
                 (reduce (fn [remaining-cells cell]
                           (if (= lvl (level cell))
                             (dissoc remaining-cells (first cell))
                             remaining-cells))
                         cells cells))
          (update :levels dec)))))

(defn transplant-initial
  "Returns an updated PUZZLE.
  Transplants an initial (already translated and reflected) from one level to
  another. Does not actually remove any cells from original level (done later
  for optimization)."
  [puzzle [word [[x y _] orientation]] lvl]
  (place-word puzzle [[x y lvl] orientation] word))

(defn transplant-initials
  [puzzle initials lvl]
  (reduce (fn [puz i]
            (or (transplant-initial puz i lvl)
                (reduced nil)))
          puzzle initials))

(defn reflect-point
  "Returns a point representing a reflection of POINT across the line of
  reflection, y = -x + b, which contains ORIGIN.
  The supplied point may be in 3D-space, but the reflection occurs on the x-y plane
  leaving Zs untouched."
  [[origin-x origin-y :as origin] [x y & zs :as point]]
  (let [b (+ origin-x origin-y)]
    (into [(+ b (- y)) (+ b (- x))] zs)))

(defn reflect-initial
  [origin [word [coord orientation]]]
  (let [orient (if (= orientation :horizontal)
                 :vertical
                 :horizontal)]
    [word [(reflect-point origin coord) orient]]))

(defn translate-point
  "Returns a translation of POINT according to a TRANSLATION VECTOR."
  [trans-vec point]
  (mapv #(+ %1 %2) trans-vec point))

(defn translate-initial
  [trans-vec [word [coord orientation] :as initial]]
  [word [(translate-point trans-vec coord) orientation]])

(defn translation-vector
  "Returns a vector representing the translation distance between two POINTs."
  [old-point new-point]
  (mapv #(- %1 %2) new-point old-point))

(defn- initial-from
  "Returns the initial of a word based off the initial of a reference word and
  their index pair.
  The ref-orientation is the direction of the reference word. The cross indices are the
  indices of the shared letter in the new word and crossing word, respectively.
  The start-coord is the starting coordinates of the other crossing word."
  [[[ref-x ref-y ref-z] ref-orientation] [ref-index index]]
  (if (= ref-orientation :horizontal)
    (let [x (+ ref-x ref-index)
          y (+ ref-y index)]
      [[x y ref-z] :vertical])
    (let [x (- ref-x index)
          y (- ref-y ref-index)]
      [[x y ref-z] :horizontal])))

(defn transplant
  "Returns an updated PUZZLE with all contents on the donor level moved to the
  recipient level."
  [puzzle
   [recip-coord recip-orient :as recip-initial]
   [donor-coord donor-orient :as donor-initial] index-pair]
  (let [donor-level (level donor-initial)
        recip-level (level recip-initial)
        graft-initial (initial-from recip-initial index-pair)
        graft-coord (first graft-initial)
        donor-initials (filter #(= donor-level (level (second %))) (:initials puzzle))
        trans-vec (translation-vector donor-coord graft-coord)
        graft-ready-initials (as-> donor-initials initials
                               (map (partial translate-initial trans-vec) initials)
                               (if (distinct? (second graft-initial) (second donor-initial))
                                 (map (partial reflect-initial graft-coord) initials)
                                 initials))]
    (-> puzzle
        (transplant-initials graft-ready-initials recip-level)
        (delete-level donor-level)
        (consolidate-levels donor-level))))

(defn- place-cross
  "Return an updated PUZZLE with both words in CROSS placed and intersecting
  at INDEX-PAIR, or nil if the CROSS cannot be placed."
  [puzzle [word1 word2 :as cross] index-pair]
  (case (count (keep (:placed-words puzzle) cross))
    ;; neither words have been placed in the puzzle yet
    0 (let [word1-initial [[0 0 (:levels puzzle)] :horizontal]
            word2-initial (initial-from word1-initial index-pair)]
        (-> puzzle
            (place-word word1-initial word1)
            (place-word word2-initial word2)
            (update :levels inc)))
    ;; both words have been placed in the puzzle already
    2 (let [word1-initial (get-in puzzle [:initials word1])
            word2-initial (get-in puzzle [:initials word2])
            word1-level (level word1-initial)
            word2-level (level word2-initial)]
        (cond
          ;; same level
          (= word1-level word2-level)
          (when (= word2-initial (initial-from word1-initial index-pair))
            puzzle)
          ;; different levels
          (< word1-level word2-level)
          (transplant puzzle word1-initial word2-initial index-pair)
          :else
          (transplant puzzle word2-initial word1-initial (reverse index-pair))))
    ;; only one word has been placed in the puzzle already
    (if-let [word1-initial (get-in puzzle [:initials word1])]
      (let [word2-initial (initial-from word1-initial index-pair)]
        (place-word puzzle word2-initial word2))
      (when-let [word2-initial (get-in puzzle [:initials word2])]
        (let [word1-initial (initial-from word2-initial (reverse index-pair))]
          (place-word puzzle word1-initial word1))))))

(defn try-puzzle
  "Returns a puzzle or nil if impossible with given crosses."
  [puzzle links]
  (if-not (seq links) puzzle
          (let [link (first links)
                cross (first link)
                index-pairs (second link)]
            (some (fn [index-pair]
                    (when-let [puz (place-cross puzzle cross index-pair)]
                      (when-let [p (try-puzzle puz (rest links))]
                        (when (valid-puzzle? p) p))))
                  index-pairs))))

;;;; Finding a Dense Puzzle

(defn empty-puzzle
  "Returns an empty crossword puzzle.
  Empty puzzles have no placed-words or initials, but do have words and a
  cross-matrix to help during the construction of a puzzle."
  [words crosses]
  (->Puzzle (set words)                    ; words
            (adjacency-list words crosses) ; adj-list
            #{}                            ; placed-words
            {}                             ; initials
            0                              ; levels
            {}))                           ; cells

(defn min-partition-sum
  "Returns the minimum of the sums of two collections, where the collections are
  the result of partitioning COLL into two such that the difference between each
  sum is as low as possible."
  ([coll]
   (let [half (quot (apply + coll) 2)]
     (min-partition-sum 0 half (sort > coll))))

  ([sum half coll]
   (if-not (seq coll)
     sum
     (let [potential-sum (+ (first coll) sum)
           new-sum (if (> potential-sum half) sum potential-sum)]
       (recur new-sum half (rest coll))))))

(defn max-degree
  "Returns the maximum degree (number of crosses) of a word."
  [word adjs]
  (min (count word) (count adjs)))

(defn maximum-links
  "Returns the maximum number of links a crossword puzzle can have, taking into
  account the number of links of a complete bipartite graphs, the length of the
  given words, and the words' adjacencies."
  [words adj-list]
  (let [num-words (count words)
        deg-seq (map (fn [word]
                       (max-degree word (get adj-list word)))
                     words)]
    (min (kmn-links num-words)
         (min-partition-sum deg-seq))))

(defn dense-puzzle
  "Returns a puzzle satisfying the constraint that it must have the highest
  possible density (most number of links)."
  [graph]
  (let [words (:nodes graph)
        num-words (count words)
        links (:links graph)
        sorted-links (sort-by (comp count second) links)
        num-links (count links)
        adj-list (:adj-list graph)
        max-links (maximum-links words adj-list)
        #_debug #_(atom 0)]
    (some #(do #_(reset! debug 0) #_(println "num crosses: " %)
               (some (fn [links]
                       ;; potential optimization for long-worded puzzles
                       #_(when (bipartite (adj-list a b)))
                       ;; uncomment to see progress
                       #_(if (= 0 (mod (swap! debug inc) 1000))
                         (println @debug "/" (choose num-links %)))
                       (let [crosses (map first links)]
                         (try-puzzle (empty-puzzle words crosses) links)))
                     (c/combinations sorted-links %)))
          (rrange 1 (inc max-links)))))

;;;; Configuration Graph

(defn index-pairs-from-cross
  "Returns all index pairs of CROSS.
  Example:
    (index-pairs-from-cross [\"fire\" \"earth\"])
    => [2 2] [3 0]
  The 'r' in both strings is at index 2.
  The 'e' in both strings is at index 3 in \"fire\" and 0 in \"earth\"."
  [[word1 word2 :as cross]]
  (seq (for [i (range (count word1))
             j (range (count word2))
             :let [letter1 (nth word1 i)
                   letter2 (nth word2 j)]
             :when (= letter1 letter2)]
         [i j])))

(defn links-from-words
  "Returns a map of all the links given WORDS.
  Links include a cross and the cross's index pairs."
  [words]
  (let [potential-crosses (c/combinations words 2)]
         (reduce (fn [links pot-cross]
                   (if-let [index-pairs (index-pairs-from-cross pot-cross)]
                     (conj links (vector (vec pot-cross) index-pairs))
                     links))
                 [] potential-crosses)))

(defn config-graph
  "Returns a graph of nodes, links, and an adjacency list used for the
  construction of puzzles.
  The nodes represent the WORDS.
  The links between nodes represent words that share at least one letter and can
  cross. A link contains the cross and index pairs. A cross is the pair of
  words (eg. [\"some\" \"words\"]). An index pair (eg. [0 4]) represents the
  indices of the letters where the words can cross."
  [words]
  (let [nodes words
        links (links-from-words words)
        crosses (map first links)
        adj-list (adjacency-list nodes crosses)]
        (->ConfigGraph nodes links adj-list)))

;;;; User Input

(defn cleaned-words
  "Returns vector of cleaned up words input by the user.
  Duplicate words and words less than 2 characters are eliminated, and all words
  are upper-cased."
  [raw]
  (as-> raw words
    (str/upper-case words)
    (str/split words #" ")
    (filter #(> (count %) 1) words)
    (vec (set words))))

;;;; Driver

(defn crossword
 [& args]
 (let [raw-words (or (first args) (read-line))
       words (cleaned-words raw-words)
       graph (config-graph words)
       puzzle (dense-puzzle graph)]
   puzzle))

(defn -main
  [& args]
  (crossword (first args)))
