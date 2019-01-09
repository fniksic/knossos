(ns knossos.hitting
  "A linearizability checking approach based on strong hitting families:
  https://github.com/burcuku/check-lin"
  (require [knossos.search :as search])
  )

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