// Two dice, each uniform on 0..5, conditioned on the two showing the same face.
// There is no sequencing in this language, so the observe is placed in a let
// binding: its conditioning happens while the bindings are evaluated, before the
// body (+ d1 d2) is returned. The result is the distribution of the sum given
// equal dice: outcomes 0, 2, 4, 6, 8, 10, each with probability ~1/6.
// Run with:  run dice.scm
(query
  (let ((d1 (random 6)) (d2 (random 6)))
    (let ((checked (observe (= d1 d2))))
      (+ d1 d2))))
