/* The distribution of the sum of two dice, conditioned on the dice being equal. */
(query
  (let ((d1 (random 6)) (d2 (random 6)))
    (let ((checked (observe (= d1 d2))))
      (+ d1 d2))))
