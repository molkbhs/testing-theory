from z3 import *
# ====the predicate====
#
# p = (a ∨ (b ∧ c)) ∧ d
#
#  ====clause====
#
# a = curTemp < dTemp - thresholdDiff
#
# b = override
#
# c = curTemp < over_temp - thresholdDiff
#
# d = timeSinceLastRun > minLag
#
# p = turn heat
#
# ====var types====

#  curTemp: Integer
#  thresholdDiff: Integer
#  timeSinceLastRun: Integer
#  minLag: Integer
#  override = b : boolean
#  over_temp: Integer
#  runTime: Integer
#  heaterOn = p: boolean
#
# ====Active clause====
#
# p_a = d ∧ (¬b ∨ ¬c)
#
# p_b = c ∧ d ∧ ¬a
#
# p_c = b ∧ d ∧ ¬a
#
# p_d = a ∨ (b ∧ c)
#
# ====Inactive clause==== (c_i does NOT determine p  =>  ¬p_i)
#
# ¬p_a = ¬d ∨ (b ∧ c)
#
# ¬p_b = ¬c ∨ ¬d ∨ a
#
# ¬p_c = ¬b ∨ ¬d ∨ a
#
# ¬p_d = ¬a ∧ (¬b ∨ ¬c)
#
# ====Inactive clause coverage====
#
# GICC : for each major clause c_i, minors chosen so that c_i does not determine p.
#        4 test requirements per clause : (c_i , p) = (T,T) (T,F) (F,T) (F,F)
#        the minor clauses may take different values from one requirement to another.
#
# RICC : same, but the minor clauses must have the SAME truth values when c_i is true
#        and when c_i is false.
#        2 pairs per clause : one pair with p = T , one pair with p = F
#        (each pair = one test with c_i = T and one test with c_i = F)


D_TEMP = 65

cur_temp = Int("cur_temp")

threshold_diff = Int("threshold_diff")

time_since_last_run = Int("time_since_last_run")

min_lag = Int("min_lag")

override = Bool("override")

over_temp = Int("over_temp")

run_time = Int("run_time")

clauses ={
"a" : cur_temp < D_TEMP - threshold_diff,
"b" : override,
"c" : cur_temp < over_temp - threshold_diff,
"d" : time_since_last_run > min_lag,
}

major_clauses ={
"a" : And(clauses["d"] , Or(Not(clauses["b"]) , Not(clauses["c"]))),
"b" : And(clauses["c"] , clauses["d"] ,Not(clauses["a"])),
"c" : And(clauses["b"] , clauses["d"] ,Not(clauses["a"])),
"d" : Or(clauses["a"] , And(clauses["b"], clauses["c"])),
}

# c_i does not determine p  <=>  not (p_i)
inactive_clauses = {key : Not(major) for key , major in major_clauses.items()}

p = And(Or(clauses["a"] , And(clauses["b"] , clauses["c"])) , clauses["d"])

# variables that appear in the predicate (run_time is not used by p)
pred_vars = [cur_temp , threshold_diff , time_since_last_run , min_lag , override , over_temp]

# ====helpers====

# expression e forced to the value v (True / False)
def lit(e , v):
    return e if v else Not(e)

# a copy of the expression where every variable is renamed with the suffix `tag`
# (needed by RICC: the two tests of a pair are two independent states of the program)
def copy_of(expr , tag):
    if tag is None:
        return expr
    return substitute(expr , *[(v , Const(f"{v}_{tag}" , v.sort())) for v in pred_vars])

# returns a model, or None when unsat / unknown
def solve(s , label , *constraints):
    s.reset()
    s.add(*constraints)
    is_solvable = s.check()
    if(is_solvable == unsat):
        print(f"\nNot solvable, {label}")
        return None
    elif(is_solvable == unknown):
        print(f"\nz3 failed, {label}")
        return None
    return s.model()

# GACC P_i = 1 for each i = {1, 0} => pair ()
def gacc(s , p_i , i , i_key):
    sol_i_t = solve(s , f"active clause {i_key} when {i_key} is true"  , p_i , i)
    sol_i_f = solve(s , f"active clause {i_key} when {i_key} is false" , p_i , Not(i))
    return (sol_i_f , sol_i_t)

# GICC : 4 independent test requirements (c_i , p) = (T,T) (T,F) (F,T) (F,F)
# with c_i inactive. Returns {(c_i value , p value) : model or None}
def gicc(s , inactive_i , i , i_key):
    results = {}
    for c_val in (True , False):
        for p_val in (True , False):
            label = f"inactive clause {i_key} with {i_key} = {c_val} and p = {p_val}"
            results[(c_val , p_val)] = solve(s , label , inactive_i , lit(i , c_val) , lit(p , p_val))
    return results

# RICC : for p = T and for p = F, a pair of tests (c_i = T , c_i = F) with c_i inactive
# and the minor clauses having the same truth value in both tests.
# Returns {p value : model or None}; the model contains the two states (suffix _t and _f)
def ricc(s , inactive_i , i , i_key):
    results = {}
    for p_val in (True , False):
        constraints = [
            copy_of(i , "t"),                  # test 1 : c_i = True
            Not(copy_of(i , "f")),             # test 2 : c_i = False
            copy_of(inactive_i , "t"),         # c_i inactive in both tests
            copy_of(inactive_i , "f"),
            lit(copy_of(p , "t") , p_val),     # p has the same value in both tests
            lit(copy_of(p , "f") , p_val),
        ]
        # RICC : every minor clause has the same truth value in both tests
        for key , clause in clauses.items():
            if key != i_key:
                constraints.append(copy_of(clause , "t") == copy_of(clause , "f"))
        label = f"inactive clause {i_key} (restricted) with p = {p_val}"
        results[p_val] = solve(s , label , *constraints)
    return results

def pretty_log_model(model):
    for d in model.decls():
        print ("\n%s = %s" % (d.name(), model[d]))

# this need to be updated to suit RACC , CACC
def pretty_log(result , clause_name):
    for i in range(len(result)):
        print(f"\nfor clause ({clause_name}) = {'False' if i == 0 else 'True'}:")
        if result[i] is None:
            print("no solution")
        else:
            pretty_log_model(result[i])

# values of the variables and truth value of the clauses / p for the state `tag`
def pretty_log_state(model , tag = None):
    for v in pred_vars:
        print(f"{v}{'' if tag is None else '_' + tag} = {model.eval(copy_of(v , tag) , model_completion = True)}")
    values = {k : is_true(model.eval(copy_of(c , tag) , model_completion = True)) for k , c in clauses.items()}
    values["p"] = is_true(model.eval(copy_of(p , tag) , model_completion = True))
    print("  -> " + "  ".join(f"{k} = {'T' if v else 'F'}" for k , v in values.items()))

def pretty_log_gicc(result , clause_name):
    for (c_val , p_val) , model in result.items():
        print(f"\nfor clause ({clause_name}) = {c_val} and p = {p_val}:")
        if model is None:
            print("no solution")
        else:
            pretty_log_state(model)

def pretty_log_ricc(result , clause_name):
    for p_val , model in result.items():
        print(f"\nfor clause ({clause_name}) pair with p = {p_val}:")
        if model is None:
            print("no solution")
        else:
            print(f"test 1, {clause_name} = True:")
            pretty_log_state(model , "t")
            print(f"test 2, {clause_name} = False:")
            pretty_log_state(model , "f")

def main():
    s = Solver()
    #======GACC======
    print("\n====GACC====")
    for key , clause in clauses.items():
        print(f"\n====for clause ({key})==== ")
        gacc_i = gacc(s , major_clauses[key], clause , key)
        pretty_log(gacc_i , key)
    #======CACC======
    #======RACC======
    #======GICC======
    print("\n====GICC====")
    for key , clause in clauses.items():
        print(f"\n====for clause ({key})==== ")
        gicc_i = gicc(s , inactive_clauses[key] , clause , key)
        pretty_log_gicc(gicc_i , key)
    #======RICC======
    print("\n====RICC====")
    for key , clause in clauses.items():
        print(f"\n====for clause ({key})==== ")
        ricc_i = ricc(s , inactive_clauses[key] , clause , key)
        pretty_log_ricc(ricc_i , key)

if (__name__ == "__main__"):
    main()
