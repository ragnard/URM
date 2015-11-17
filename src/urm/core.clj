(ns urm.core
  (:refer-clojure :exclude [inc pop])
  (:require [clojure.pprint :refer [pprint]]
            [clojure.math.numeric-tower :as math]
            [clojure.core.unify :refer :all]))

(defn inc [register jump-to]
  [:inc register jump-to])

(defn deb [register jump-to branch-on-zero]
  [:deb register jump-to branch-on-zero])

(defn end []
  [:end])

(defn apply-statement
  [[instruction register jump-to branch-on-zero :as statement] state]
  (let [current (get-in state [:registers register] 0)
        branch? (= current 0)]
    (case instruction
      :inc (-> state
               (assoc-in [:registers register] (+ 1 current))
               (assoc :position jump-to))
      :deb (-> state
               (assoc-in [:registers register] (if branch? current (dec current)))
               (assoc :position (if branch? branch-on-zero jump-to)))
      :end state)))


;;--------------------------------------------------------------------
;; "intrinsics"

(def acc
  {:pattern '[[?start :deb ?from ?next ?done]
              [?next  :inc ?to ?start]]
   :impl    (fn [bindings {:keys [registers] :as state}]
              (println "ACC")
              (let [?from (bindings '?from)
                    ?to (bindings '?to)]
                (-> state
                    (update-in [:registers ?to] (fnil + 0) 1 (get registers ?from 0))
                    (assoc-in [:registers ?from] 0)
                    (assoc :position (bindings '?done)))))})

(def zero-intrinsic
  {:pattern  '[[?start :deb ?r ?start ?done]]
   :impl     (fn [bindings {:keys [registers] :as state}]
               (println "ZERO")
               (let [?r (bindings '?r)]
                 (-> state
                     (assoc-in [:registers ?r] 0)
                     (assoc :position (bindings '?done)))))})

(def dup-intrinsic
  {:pattern   '[[?0 :deb ?from ?1 ?done]
                [?1 :inc ?scratch ?2]
                [?2 :inc ?to ?0]]
   :impl      (fn [bindings {:keys [registers] :as state}]
                (println "DUP")
                (let [?from (bindings '?from)
                      ?to (bindings '?to)
                      ?scratch (bindings '?scratch)]
                  (-> state
                      (assoc-in [:registers ?to] (get-in state [:registers ?from]))
                      (assoc-in [:registers ?scratch] (get-in state [:registers ?from]))
                      (assoc :position (bindings '?done)))))})

(def parity-intrinsic
  {:pattern  '[[?0 :deb ?scratch ?1 ?odd]
               [?1 :deb ?scratch ?2 ?even]
               [?2 :inc ?t ?0]]
   :impl     (fn [bindings {:keys [registers] :as state}]
               #_(println "PARITY")
               (let [?scratch (bindings '?scratch)
                     scratch (get-in state [:registers ?scratch])
                     ?t (bindings '?t)]
                 (if (zero? (mod scratch 2))
                   (-> state
                       ;; not needed #_(assoc-in [:registers ?t] (* scratch ))
                       (assoc :position (bindings '?even)))
                   (-> state
                       (assoc :position (bindings '?odd))))))})

;; [14 :inc 4 11]
;; [11 :deb 8 12 13]
;; [13 :deb 9 15 14]

(def queue clojure.lang.PersistentQueue/EMPTY)

(defn apply-intrinsic
  [statement {:keys [position intrinsics history] :as state}]
  (let [statement' (into [position] statement)
        max-history (apply max (map (comp count :pattern) intrinsics))
        history (let [history' ((fnil conj queue) history statement')]
                  (if (<= (count history') max-history)
                    history'
                    (clojure.core/pop history')))
        intrinsic (first (keep (fn [{:keys [pattern impl] :as intrinsic}]
                                 (when-let [subst (unify pattern (take (count pattern) history))]
                                   (partial impl subst)))
                               intrinsics))]
    #_[false (assoc state :history history)]
    (if intrinsic
      [true  (assoc (intrinsic state) :history nil)]
      [false (assoc state :history history)])))

;;--------------------------------------------------------------------

(defn next-state [{:keys [position program intrinsics] :as state}]
  (let [next-statement (nth program position)]
    (let [[intrinsified? state'] (apply-intrinsic next-statement state)]
      (if intrinsified?
        state'
        (apply-statement next-statement state')))))

(defn run [state]
  (let [next (next-state state)]
    (if (< (Math/random) 0.0001) (pprint (:history state)))
    (if (= (select-keys next  [:program :position :registers])
           (select-keys state [:program :position :registers]))
      state
      (recur next))))

(defn urm->fn [statements]
  (fn [& args]
    (let [final-state (run {:program statements
                            :position 0
                            :registers (zipmap (drop 1 (range)) args)
                            :intrinsics [acc
                                         zero-intrinsic
                                         dup-intrinsic
                                         parity-intrinsic]})]
      (get-in final-state [:registers 0]))))

(defn eval-urm [statements args]
  (apply (urm->fn statements) args))

(defn inc-by [n]
  (fn [[instruction register jump-to branch-on-zero :as statement]]
    (case instruction
      :deb (deb register
                (if (number? jump-to)
                  (+ jump-to n)
                  jump-to)
                (if (number? branch-on-zero)
                  (+ branch-on-zero n)
                  branch-on-zero))
      :inc (inc register (if (number? jump-to)
                           (+ jump-to n)
                           jump-to))
      :end (end))))

(defn increment-instruction-numbers-by [urm n]
  (map (inc-by n) urm))

(defn zero [register]
  [(deb register 0 1)
   (end)])

(defn comp-urm
  ([urm1 urm2 & urms]
   (comp-urm urm1
             (apply comp-urm urm2 urms)))
  ([urm1 urm2]
   (let [length1 (dec (count urm1))
         start-of-program (take length1 urm1)
         rest-of-program (increment-instruction-numbers-by urm2 length1)]
     (concat start-of-program
             rest-of-program))))

(defn divides? [n div]
  (= 0 (rem n div)))

(defn factors-of-2
  ([n] (factors-of-2 n 0))
  ([n so-far]
   (if (divides? n 2)
     (recur (/ n 2)
            (+ 1 so-far))
     so-far)))

(defn <<>> [x y]
  (* (math/expt 2 x)
     (+ (* 2 y) 1)))

(defn un<<>> [n]
  (let [x (factors-of-2 n)
        y (/ (dec (/ n (math/expt 2 x)))
             2)]
    [x y]))

(defn <> [x y]
  (dec (<<>> x y)))

(defn un<> [n]
  (un<<>> (+ n 1)))

(defn code-list [[h & t :as number-list]]
  (if (empty? number-list)
    0
    (<<>> h (code-list t))))

(defn decode-list [code]
  (if (= code 0)
    '()
    (let [[h code'] (un<<>> code)]
      (cons h
            (decode-list code')))))

(defn code-instruction [[instruction register jump-to branch-on-zero]]
  (case instruction
    :inc (<<>> (* 2 register) jump-to)
    :deb (<<>> (+ (* 2 register) 1)
               (<> jump-to branch-on-zero))
    :end 0))

(defn decode-instruction [code]
  (if (= code 0)
    (end)
    (let [[y z] (un<<>> code)]
      (if (even? y)
        (inc (/ y 2) z)
        (let [[j k] (un<> z)]
          (deb (/ (dec y) 2)
               j
               k))))))

(defn code-program [instructions]
  (code-list (map code-instruction instructions)))

(defn decode-program [code]
  (map decode-instruction (decode-list code)))

(defn copy [from to & [go-to]]
  (comp-urm
   (zero to)
   (zero 9)
   [(deb from 1 3)
    (inc 9 2)
    (inc to 0)
    (deb 9 4 5)
    (inc from 3)
    (if go-to
      (deb 10 99 go-to)
      (end))
    ]))

(defn push [x l & [go-to]]
  ;; 9 here is the spare register in the UURM
  [(inc 9 1)
   (deb l 2 3)
   (inc 9 0)
   (deb 9 4 5)
   (inc l 3)
   (deb 9 1 6)
   (if go-to
     (deb 10 99 go-to)
     (end))])

(defn pop [l x & [exit-to go-to]]
  ;; 9 here is the spare register in the UURM
  [(deb x 0 1)
   (deb l 2 exit-to)
   (inc l 3)
   (deb l 4 5)
   (inc 9 3)
   (deb 9 7 6)
   (inc x 3)
   (deb 9 8 9 )
   (inc l 5)
   (if go-to
     (deb 10 99 go-to)
     (end))])

(defn urm-with-goto [urm go-to]
  ;; 10 here is known-zero
  (let [l (count urm)]
    (concat (take (dec l) urm)
            [(deb 11 99 go-to)])))

(def p 1)
(def a 2)
(def pc 3)
(def n 4)
(def c 5)
(def r 6)
(def s 7)
(def t 8)
(def z 9)

(def uurm
  [[:start (copy p t :pop_t_n)]
   [:pop_t_n  (pop t n :deb_pc :halt)]
   [:deb_pc [(deb pc :pop_t_n :pop_n_c)]]
   [:pop_n_c (pop n c :pop_a_r :halt)]
   [:pop_a_r (pop a r :deb_c :deb_c)]
   [:deb_c [(deb c :deb_c2 :inc_r)]]
   [:deb_c2 [(deb c :push_r_s :inc_n)]]
   [:push_r_s (push r s :pop_a_r)]
   [:inc_r [(inc r :copy_n_pc)]]
   [:inc_n [(inc r :pop_n_pc)]]
   [:copy_n_pc (copy n pc :push_r_a)]
   [:pop_n_pc (pop n pc :deb_r :deb_r)]
   [:push_r_a (push r a :pop_s_r)]
   [:deb_r [(deb r :push_r_a :copy_n_pc)]]
   [:pop_s_r (pop s r :push_r_a :start)]

   [:halt [(end)]]])

(def lengths (cons 0 (reductions + (map (comp count second) uurm))))
(def startline-lookup (zipmap (map first uurm)
                              lengths))

(defn lookup-jumps [[instruction register & line-numbers]]
  (concat [instruction register]
          (map (fn [n]
                 (if (startline-lookup n)
                   (startline-lookup n)
                   n))
               line-numbers)
          ))

(def full-urm (map lookup-jumps (mapcat (fn [[name urm] offset]
                                          (increment-instruction-numbers-by urm offset))
                                        uurm
                                        lengths)))

(defn -main []
  (pprint full-urm))

;;

(def add [(deb 2 1 2)
          (inc 0 0)
          (deb 1 3 4)
          (inc 0 2)
          (end)])

(def add-fn (urm->fn add))

(time (+ 132 34982))
(time (add-fn 132 34982))

(comment
  
  (eval-urm full-urm
            [(code-program add)
             (code-list [1 1])
             0])

  )
