# Abstract Transition Systems

An implementation of several classic transition systems that describe
algorithms for SAT or SMT. The purpose is to make it very easy to experiment
with new calculi or variants of existing calculi.

- Calculi
  * [x] DPLL
  * [ ] CDCL
  * [ ] mcsat '13
  * [ ] mcsat '17 (with non boolean propagations)
  …
- Interfaces
  * [x] linenoise
  * [ ] interactive web UI

## Example of a session

```
$ dune exec src/bin/main.exe -- -s dpll
picked ats dpll    
> init ((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 2))
> show
state:
  (st :status searching
   :cs ((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 2)) :trail ())
> next
choices:
  (0: (st :status searching
       :cs ((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 2)) :trail (3*)) by "decide 3")
  (1: (st :status searching
       :cs ((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 2)) :trail (2*)) by "decide 2")
  (2: (st :status searching
       :cs ((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 2)) :trail (1*)) by "decide 1")
> pick 0
picked 0: next state by "decide 3"
  (st :status searching
   :cs ((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 2)) :trail (3*))
> next 5
deterministic transition "propagate 2 from (-3 2)" to
  (st :status searching
   :cs ((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 2)) :trail (2 3*))
deterministic transition "propagate -1 from (-2 -1 -3)" to
  (st :status searching
   :cs ((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 2)) :trail (-1 2 3*))
done by "all vars decided", last state:
  (st :status sat :cs ((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 2))
   :trail (-1 2 3*))
```
