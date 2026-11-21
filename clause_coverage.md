opp = {∧ ∨ ¬ ⊕ ↔ ⇒}

# the predicate

p = (a ∨ (b ∧ c)) ∧ d

## clause

a = curTemp < dTemp - thresholdDiff

b = override

c = curTemp < overTemp - thresholdDiff

d = timeSinceLastRun > minLag

p = turn heat

## var types

- curTemp: Integer
- thresholdDiff: Integer
- timeSinceLastRun: Integer
- minLag: Integer
- override = b : boolean
- overTemp: Integer
- runTime: Integer
- heaterOn = p: boolean

## Active clause

p_a = d ∧ (¬b ∨ ¬c)

p_b = c ∧ d ∧ ¬a

p_c = b ∧ d ∧ ¬a

p_d = a ∨ (b ∧ c)
