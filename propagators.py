#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.  

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newVar=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newVar (newly instaniated variable) is an optional argument.
      if newVar is not None:
          then newVar is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method).
      bt_search NEEDS to know this in order to correctly restore these
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newVar = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated
        constraints)
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newVar = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''


########################################################################################################################
def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''

    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []
########################################################################################################################


'''
    gets the index of where var is located, and a list of assigned variables
'''
########################################################################################################################
def get_assgn_list(c, var):

    all_vars = c.get_scope()
    i = 0 # WARNING
    if var:
        i = all_vars.index(var)

    assgn_list = []
    for v in all_vars:
        assgn_list.append(v.get_assigned_value())
    return [i, assgn_list]
########################################################################################################################

'''
    gets constraints with newVar if newVar is not None
    otherwise get all constraints
'''
########################################################################################################################
def get_constraints(csp, newVar):
    if not newVar: # if newVar is None forward check all constraints
        return csp.get_all_cons() # forward checks all constraints
    else:
        return csp.get_cons_with_var(newVar)
########################################################################################################################


########################################################################################################################
def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return'''
    constraints = get_constraints(csp,newVar)
    pruned = []
    for c in constraints:
        if c.get_n_unasgn() == 1:  # checks constraints that have exactly one uninstantiated variable in their scope
            unsgn_var = c.get_unasgn_vars()[0] # the unassigned variable
            i, assgn_list = get_assgn_list(c,unsgn_var)
            # we want to assign it the different possible values and see
            # if they work, if they don't then add them to pruned list
            # assign the variables v's value to be a values in its cur_domain
            check_vals = unsgn_var.cur_domain()
            # loop through and check different values
            for val in check_vals:
                assgn_list[i] = val
                if not c.check(assgn_list):
                    if (unsgn_var,val) not in pruned: # avoids pruning a value twice
                        unsgn_var.prune_value(val)
                        pruned.append((unsgn_var,val))

            if unsgn_var.cur_domain_size() == 0: # domain wipe out
                return False, pruned
    return True, pruned
########################################################################################################################


########################################################################################################################
def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    constraints = get_constraints(csp, newVar)
    pruned = []
    gac_queue = []

    for c in constraints:
        gac_queue.append(c)

    # GACEnforce
    while len(gac_queue) > 0:
        c = gac_queue.pop(0)
        for v in c.get_scope(): # loop through each member of c
            # prune all values of V not equal to d from CurDom[V]
            for val in v.cur_domain():
                '''Test if a variable value pair has a supporting tuple (a set of assignments satisfying the constraint
                where each value is still in the corresponding variables current domain'''
                if not c.has_support(v,val): # tests
                    if (v, val) not in pruned:  # avoids pruning a value twice
                        v.prune_value(val)
                        pruned.append((v, val))
                    if v.cur_domain_size() == 0:
                        gac_queue = []
                        return False, pruned
                    else: # push all constraints C' such that:
                        c_prime = csp.get_cons_with_var(v) # V is in the cope of C
                        for new_cons in c_prime:
                            gac_queue_tuple = tuple(gac_queue)

                            # check to see if constraint is in gac_queue
                            if gac_queue_tuple.count(new_cons) == 0:
                                gac_queue.append(new_cons)
    return True, pruned
########################################################################################################################