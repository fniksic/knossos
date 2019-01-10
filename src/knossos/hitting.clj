(ns knossos.hitting
  "A linearizability checking approach based on strong hitting families:
  https://github.com/burcuku/check-lin"
  (:require [knossos [search :as search]
                     [op :as op]]))

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

(defn start-analysis
  "Spawns a thread to check a history; returns Search"
  [model history]
  (let [state   (atom {:running? true})
        results (promise)
        worker  (Thread.)]
    (.start worker)
    (reify search/Search
      (abort! [_ cause]
        (swap! state assoc
               :running? false
               :cause cause))
      (report [_] {})
      (results [_] )
      (results [_ timeout timeout-val] ))))

(defn analysis
  "Given an initial model state and a history, check to see if the history is
  linearizable. Returns a map with a :valid? bool and additional debugging
  information."
  [model history]
  (assoc (search/run (start-analysis model history))
    :analyzer :hitting))