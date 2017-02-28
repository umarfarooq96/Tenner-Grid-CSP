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

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with
       only one uninstantiated variable. Remember to keep
       track of all pruned variable,value pairs and return '''
    #IMPLEMENT
    '''
    FC(Level)
        If all variables are assigned:
            return or exit
        V = pick an unassigned variable
        Assigned[V} = True
        for d := each member of CurDom(V)
            Value of V = d
            DWO_occurred = False
            for each constraint C over V such that
                    a) C has only one unassigned variable X in its scope
                if (FCCheck(C,X) = DWO)
                    DWO_occurred = True
                    break -- stop checking constraint

             ~~THIS PART DONE BY BT_SEARCH~~ ~~DON'T NEED THIS~~
            if (not DWO_occurred) -- all constraints were ok
                FC(Level+1)
            RestoreAllValuesPrunedByFCCheck()
             ~~THIS PART DONE BY BT_SEARCH~~ ~~DON'T NEED THIS~~

        Assigned[V} = False
         return;

    FCCheck(C, x)
        for each member of CurDom[x]
            if making x = d together with previous assignments to variables in scope C FALSIFIES C
            then remove d from CurDom[x]
        If CurDom[x] = {} then return DWO
        Else return ok
    '''
    if newVar is None:
        constraints = csp.get_all_cons()
    else:
        constraints = csp.get_cons_with_var(newVar)

    # return (bool,list) where bool is false iff dead-end found, list is (Variable,value) pruned
    # list of (Variable, value) tuples that have been pruned
    pruned_list = []

    #we look for unary constraints of the csp (constraints whose scope
    #contains only ONE variable) and we forward_check these constraints.
    for con in constraints:
        if con.get_n_unasgn() == 1:

            unassigned = pick_an_unasgn_vars(con)
            dwo_occurred, pruned = fc_check(con, unassigned)
            pruned_list += pruned

            if dwo_occurred: #stop checking constraints
                return False, pruned_list

    return True, pruned_list


#return var,val pruned, True iff DWO.
def fc_check(C, x):
    pruned = []
    dwo = True
    for d in x.cur_domain():
        if C.has_support(x, d) is False:
            x.prune_value(d)
            pruned.append((x, d))

    if x.cur_domain_size() is 0:
        return dwo, pruned
    else:
        return False, pruned

def pick_an_unasgn_vars(con):
    '''get_unasgn_vars but no appending, just return immediatley
    safe because we check if it has at least 1 first'''
    for v in con.scope:
        if not v.is_assigned():
            return v


def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    #IMPLEMENT
    if newVar is None:
        constraints = csp.get_all_cons()
    else:
        constraints = csp.get_cons_with_var(newVar)

    gac_queue = Queue(constraints)

    # return (bool,list) where bool is false iff dead-end found, list is (Variable,value) pruned
    # list of (Variable, value) tuples that have been pruned
    pruned_list = []
    dwo_occurred, pruned = gac_enforce(csp, gac_queue)
    pruned_list += pruned

    if dwo_occurred:
        return False, pruned_list
    else:
        return True, pruned_list


def gac_enforce(csp, gac_queue):
    pruned = []
    dwo = True
    while not gac_queue.empty():
        c = gac_queue.dequeue()
        for V in c.get_scope():
            for d in V.cur_domain():
                if c.has_support(V, d) is False:  #A not found
                    V.prune_value(d)
                    pruned.append((V, d))

                    if V.cur_domain_size() is 0:
                        return dwo, pruned
                    else:
                        for c_prime in csp.get_cons_with_var(V):  #all C' s.t. V is in scope(C')
                            if not gac_queue.contains(c_prime):  #and C' not in gac_queue
                                gac_queue.enqueue(c_prime)  #push to gac_queue
    return False, pruned

#SOURCE: http://stackoverflow.com/questions/20557440/queue-class-dequeue-and-enqueue-python
#the import queue doesn't have contains plus it has weird multi-threading stuff
class Queue(object):
    def __init__(self, queue=None):
        if queue is None:
            self.queue = []
        else:
            self.queue = list(queue)

    def dequeue(self):
        return self.queue.pop(0)

    def enqueue(self, element):
        self.queue.append(element)

    def contains(self, item):
        return item in self.queue

    def empty(self):
        return len(self.queue) == 0