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

p = And(Or(clauses["a"] , And(clauses["b"] , clauses["c"])) , clauses["d"])

# evaluate solution is it correct ?
def eval_predicate_a_c(cur_temp , threshold_diff , d_temp=D_TEMP):
    return True if cur_temp < d_temp - threshold_diff else False

def eval_predicate_d(time_since_lastRun ,min_lag):
    return True if time_since_lastRun > min_lag else False


def eval_pa(cur_temp , override_temp , threshold_diff , b ,time_since_lastRun ,min_lag):
    c = eval_predicate_a_c(cur_temp, threshold_diff ,d_temp=override_temp)
    d = eval_predicate_d(time_since_lastRun ,min_lag)
    return(d and (not b or not c))

def eval_pb_pc(pi,cur_temp, threshold_diff, time_since_lastRun ,min_lag):
    a = eval_predicate_a_c(cur_temp, threshold_diff)
    d = eval_predicate_d(time_since_lastRun ,min_lag)
    return (pi and d and not a)

def eval_pb_pc(b,cur_temp, override_temp , threshold_diff, time_since_lastRun ,min_lag):
    a = eval_predicate_a_c(cur_temp, threshold_diff)
    c = eval_predicate_a_c(cur_temp, threshold_diff ,d_temp=override_temp)
    return (a or ( b and c ))

def clause_a(cur_temp, override_temp, threshold_diff, b, t, min_lag):
    return eval_predicate_a_c(cur_temp, threshold_diff)

def clause_b(cur_temp, override_temp, threshold_diff, b, t, min_lag):
    return b

def clause_c(cur_temp, override_temp, threshold_diff, b, t, min_lag):
    return eval_predicate_a_c(cur_temp, threshold_diff, override_temp)

def clause_d(cur_temp, override_temp, threshold_diff, b, t, min_lag):
    return eval_predicate_d(t, min_lag)

def eval_p(cur_temp , override_temp , threshold_diff , b ,time_since_lastRun ,min_lag):
    a = eval_predicate_a_c(cur_temp, threshold_diff)
    c = eval_predicate_a_c(cur_temp, threshold_diff ,override_temp)
    d = eval_predicate_d(time_since_lastRun ,min_lag)
    return True if ((a or (b and c)) and d) else False

def eval_pa(cur_temp, override_temp, threshold_diff, b, t, min_lag):
    c = clause_c(cur_temp, override_temp, threshold_diff, b, t, min_lag)
    d = clause_d(cur_temp, override_temp, threshold_diff, b, t, min_lag)
    return d and (not b or not c)

def eval_pb(cur_temp, override_temp, threshold_diff, b, t, min_lag):
    a = clause_a(cur_temp, override_temp, threshold_diff, b, t, min_lag)
    c = clause_c(cur_temp, override_temp, threshold_diff, b, t, min_lag)
    d = clause_d(cur_temp, override_temp, threshold_diff, b, t, min_lag)
    return c and d and not a

def eval_pc(cur_temp, override_temp, threshold_diff, b, t, min_lag):
    a = clause_a(cur_temp, override_temp, threshold_diff, b, t, min_lag)
    d = clause_d(cur_temp, override_temp, threshold_diff, b, t, min_lag)
    return b and d and not a

def eval_pd(cur_temp, override_temp, threshold_diff, b, t, min_lag):
    a = clause_a(cur_temp, override_temp, threshold_diff, b, t, min_lag)
    c = clause_c(cur_temp, override_temp, threshold_diff, b, t, min_lag)
    return a or (b and c)

# GACC P_i = 1 for each i = {1, 0} => pair ()
def gacc(s , p_i , i , i_key):
    s.reset()
    s.add(p_i)
    s.push()
    s.add(i)
    is_solvable = s.check()
    if(is_solvable == "unsat"):
        print(f"\nNot solvabale, active clause {i_key}  when  {i_key} is true")
        sol_i_t = None
    elif(is_solvable == "unknown"):
        print(f"\n z3 failed, active clause {i_key}")
        sol_i_t = None
    else :
        sol_i_t = s.model()
    s.pop()
    s.push()
    s.add(Not(i))
    is_solvable = s.check()
    #  we need find a way for this to not be redundant
    if(is_solvable == "unsat"):
        print(f"\nNot solvabale, active clause {i_key}  when  {i_key} is false ")
        sol_i_f = None
    elif(is_solvable == "unknown"):
        print(f"\n z3 failed, active clause {i_key}")
        sol_i_f = None
    else :
        sol_i_f = s.model()
    return (sol_i_f , sol_i_t)

def pretty_log_model(model):
    for d in model.decls():
        print ("\n%s = %s" % (d.name(), model[d]))

# this need to be updated to suit RACC , CACC , GICC , RICC
def pretty_log(result , clause_name):
    for i in range(len(result)):
        print(f"\nfor clause ({clause_name}) = {"False" if i == 0 else "True"}:")
        pretty_log_model(result[i])

# transform to value can be used by python
def py_val(m, var):
    v = m.eval(var, model_completion=True)    # concrete Z3 value
    return is_true(v) if is_bool(v) else v.as_long()

def model_to_input(m):
    return (py_val(m, cur_temp), py_val(m, over_temp), py_val(m, threshold_diff),
            py_val(m, override), py_val(m, time_since_last_run), py_val(m, min_lag))


# test GACC
def check_pair(name, in_f, in_t, eval_px, eval_clause):
    # 1. the clause has the value the test claims
    assert eval_clause(*in_f) is False, f"clause {name} should be False: {in_f}"
    assert eval_clause(*in_t) is True,  f"clause {name} should be True: {in_t}"
    # 2. P_x holds in both tests, so the other clauses don't mask x
    assert eval_px(*in_f), f"P_{name} is False for the {name}=False test: {in_f}"
    assert eval_px(*in_t), f"P_{name} is False for the {name}=True test: {in_t}"
    # 3. p actually changes with x
    assert eval_p(*in_f) is False, f"p should be False when {name} is False: {in_f}"
    assert eval_p(*in_t) is True,  f"p should be True when {name} is True: {in_t}"

def test_gacc(key, sol):
    if sol[0] is None or sol[1] is None:
        print(f"clause {key}: no GACC pair (one side unsat), skipping")
        return
    in_f, in_t = model_to_input(sol[0]), model_to_input(sol[1])
    match key:
        case "a": check_pair("a", in_f, in_t, eval_pa, clause_a)
        case "b": check_pair("b", in_f, in_t, eval_pb, clause_b)
        case "c": check_pair("c", in_f, in_t, eval_pc, clause_c)
        case "d": check_pair("d", in_f, in_t, eval_pd, clause_d)
    print(f"clause {key}: GACC pair OK")



def main():
    s = Solver()
    gacc_dic = {}
    #======GACC======
    print("\n====GACC====")
    for key , clause in clauses.items():
        print(f"\n====for clause ({key})====")
        gacc_i = gacc(s , major_clauses[key], clause , key)
        pretty_log(gacc_i , key)
        gacc_dic[key] = gacc_i
    print("\n==== TEST GACC====")
    for key, sol in gacc_dic.items():
        test_gacc(key, sol)

    #======CACC======
    #======RACC======

if (__name__ == "__main__"):
    main()
