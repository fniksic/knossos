(ns knossos.hitting
  "A linearizability checking approach based on strong hitting families:
  https://github.com/burcuku/check-lin"
  (:require [knossos [history :as history]
                     [search :as search]
                     [model :as model]
                     [util :refer [deref-throw]]
                     [op :as op]]
            [knossos.model.memo :as memo :refer [memo]]
            [clojure.pprint :refer [pprint]])
  (:import (java.util ArrayDeque)))

(defn prepare-history
  "Assigns operation ids that identify invoke-ok/fail/info pairs and fills in the
  missing values on invoke actions. Returns a map containing the following information:

    :m         -- the number of processes
    :n         -- the number of operations (invoke-ok/fail/info pairs)
    :history   -- prepared history
    :processes -- a vector of process ids"
  [history]
  (loop [h'        (transient [])  ; prepared history
         processes (transient #{}) ; a set of processes
         index     (transient {})  ; a map of processes to indices of op invocations
         i         0               ; index into the history
         next-id   0]              ; next operation id
    (if (<= (count history) i)
      ; We are done, return the map
      {:m         (count processes)
       :n         next-id
       :history   (persistent! h')
       :processes (-> processes persistent! vec)}

      ; Normal processing
      (let [op (nth history i)
            p  (:process op)]
        (cond (op/invoke? op)
              (do (assert (not (get index p)))
                  (let [op'  (assoc op :id next-id)]
                    (recur (conj! h' op')
                           (conj! processes p)
                           (assoc! index p i)
                           (inc i)
                           (inc next-id))))

              (op/ok? op)
              (let [invoke-i (get index p)
                    invoke   (nth h' invoke-i)
                    id       (:id invoke)
                    value    (:value op)
                    invoke'  (assoc invoke :value value)
                    op'      (assoc op :id id)]
                (recur (-> h'
                           (assoc! invoke-i invoke')
                           (conj!  op'))
                       processes
                       (dissoc! index p)
                       (inc i)
                       next-id))

              (op/fail? op)
              (let [invoke-i (get index p)
                    invoke   (nth h' invoke-i)
                    id       (:id invoke)
                    invoke'  (assoc invoke :fails? true)
                    op'      (assoc op :id id)]
                (recur (-> h'
                           (assoc! invoke-i invoke')
                           (conj!  op'))
                       processes
                       (dissoc! index p)
                       (inc i)
                       next-id))

              (op/info? op)
              (let [id  (->> p
                             (get index)
                             (nth h')
                             :id)
                    op' (assoc op :id id)]
                (recur (conj! h' op')
                       processes
                       index
                       (inc i)
                       next-id)))))))

(defmacro coalesce-schedule
  ([] [nil nil])
  ([x] x)
  ([x & rest]
    `(let [[l# op#] ~x]
       (if (not (nil? op#))
         [l# op#]
         (coalesce-schedule ~@rest)))))

(defn advance
  "Advances the model according to the schedule up to the operation with
  the given id. The schedule consists of three parts:

    sch         -- contains non-delayed operations
    sch-chain   -- contains operations delayed due to being in a chain
    sch-labeled -- contains operations delayed due to being labeled

  The first two parts (sch, sch-chain) are ArrayDeques, and the last
  part is a sorted map from labels to operations.

  The operation with the given id is assumed to be in one of the
  parts of the schedule.

  The function returns a vector of the form [model' sch-labeled' dropped'],
  consisting of the new versions of the model and the auxiliary data
  structures. (No need to return the ArrayDeques.)"
  [model sch sch-chain sch-labeled dropped id]
  (let [[label op]   (coalesce-schedule [nil (.pollFirst sch)]
                                        [nil (.pollFirst sch-chain)]
                                        (first sch-labeled))
        model'       (model/step model op)
        sch-labeled' (dissoc sch-labeled label)]
    (if (or (= (:id op) id)
            (model/inconsistent? model'))
      ; We have reached the operation with the given id, or the
      ; model is inconsistent. Return the new model and the new
      ; auxiliary structures.
      [model' sch-labeled' dropped]

      ; Otherwise, recurse
      (recur model'
             sch
             sch-chain
             sch-labeled'
             (conj! dropped (:id op))
             id))))

(defn check-with-schedule-index
  "Given a model, a history, and a schedule index, generate a strong-hitting
  schedule and run a model against it to see if it witnesses linearizability."
  [model history sch-index]
  (let [p           (:process sch-index)
        labels      (:labels sch-index)
        ids->labels (into {} (map-indexed #(vector %2 %1) labels))
        sch         (ArrayDeque.)
        sch-chain   (ArrayDeque.)]
    (loop [model       model
           i           0                ; index in the history
           ; Ids of invoked ops whose completion we haven't seen, but they
           ; were stepped through by the model
           dropped     (transient #{})
           sch-labeled (sorted-map)]
      (if (<= (count history) i)
        ; We are done, return the model
        model

        ; Otherwise process the current op
        (let [op (nth history i)
              id (:id op)]
          (if (op/invoke? op)
            ; The main case: insert the operation into the schedule
            (if-let [label (get ids->labels id)]
              ; The operation is labeled, so we must delay it appropriately
              (recur model
                     (inc i)
                     dropped
                     (assoc sch-labeled label op))

              ; Otherwise, place it to the right position in the schedule
              (do (if (= (:process op) p)
                    (.addLast sch-chain op)
                    (.addLast sch op))
                  (recur model
                         (inc i)
                         dropped
                         sch-labeled)))

            ; Otherwise, op is a completion (ok/fail/info)
            (if (or (op/info? op)
                    (contains? dropped id))
              ; We ignore the op in this case and remove it from dropped
              (recur model
                     (inc i)
                     (disj! dropped id)
                     sch-labeled)

              ; We advance the model up to the op
              (let [[model' sch-label' dropped'] (advance model
                                                          sch
                                                          sch-chain
                                                          sch-labeled
                                                          dropped
                                                          id)]
                (if (model/inconsistent? model')
                  ; Return the model
                  model'

                  (recur model'
                         (inc i)
                         dropped'
                         sch-label'))))))))))

(defn next-num
  "Given a set of numbers s, return the first number greater than or equal
  to i and less than n that is not in s. Return nil if no such number exists."
  [n s i]
  (cond (= n i)
        nil

        (contains? s i)
        (recur n s (inc i))

        :else
        i))

(defn next-perm
  ([n p]
   (let [[p' _] (next-perm n p (transient (set p)) (dec (count p)))]
     p'))

  ([n p s i]
   (if (< i 0)
     [nil s]
     (if-let [pi (next-num n s (inc (p i)))]
       (loop [p' (assoc! (transient p) i pi)
              s' (-> s (disj! (p i)) (conj! pi))
              pj 0
              j  (inc i)]
         (if (<= (count p) j)
           [(persistent! p') s']
           (let [pj (next-num n s' pj)]
             (recur (assoc! p' j pj)
                    (conj! s' pj)
                    (inc pj)
                    (inc j)))))
       (recur n p (disj! s (p i)) (dec i))))))

(defn permutations
  ([n k]
   (let [p  (vec (range k))]
     (permutations n p (transient (set p)))))

  ([n p s]
    (when p
      (lazy-seq
        (cons p (lazy-seq
                  (let [[p' s'] (next-perm n p s (dec (count p)))]
                    (permutations n p' s'))))))))

(defn exhaustive-check
  [model history]
  (let [{:keys [m n history processes]} (-> history
                                            history/complete
                                            history/without-failures
                                            history/ensure-indexed
                                            history/parse-ops
                                            prepare-history)
        memo    (memo model history)
        model   (:model memo)
        history (:history memo)]
    (loop [d 1]
      ;(println " d=" d)
      (if (> d n)
        ; We didn't find a linearizability witness for d <= n,
        ; so the history is not linearizable
        {:valid? false}

        ; Otherwise, generate schedule indices and perform the check
        ; in parallel
        (let [sch-indices (for [p processes
                                l (permutations n (dec d))]
                            {:process p, :labels l})]
          (if (every? model/inconsistent?
                      (pmap #(check-with-schedule-index model history %)
                            sch-indices))
            ; Every model is inconsistent; recurse with the next d
            (recur (inc d))

            ; Otherwise a linearizability witness was found
            {:valid? true
             :d      d}))))))

(defn start-analysis
  "Spawns a thread to check a history; returns Search"
  [model history]
  (let [state   (atom {:running? true})
        results (promise)
        worker  (Thread.
                  (fn []
                    (try
                      (deliver results
                               (exhaustive-check model history))
                      (catch InterruptedException _
                        (let [{:keys [cause]} @state]
                          (deliver results {:valid? :unknown
                                            :cause  cause})))
                      (catch Throwable t
                        (deliver results t)))))]
    (.start worker)
    (reify search/Search
      (abort! [_ cause]
        (swap! state assoc
               :running? false
               :cause cause)
        (.interrupt worker))
      (report [_] {})
      (results [_] (deref-throw results))
      (results [_ timeout timeout-val] (deref-throw results timeout timeout-val)))))

(defn analysis
  "Given an initial model state and a history, check to see if the history is
  linearizable. Returns a map with a :valid? bool and additional debugging
  information."
  [model history]
  (assoc (search/run (start-analysis model history))
    :analyzer :hitting))