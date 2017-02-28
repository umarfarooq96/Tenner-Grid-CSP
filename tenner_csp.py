#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.  

'''
Construct and return Tenner Grid CSP models.
'''

from cspbase import *
import itertools
import time
import numpy as np

def tenner_csp_model_1(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along 
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner grid using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from 
       (0,0) to (n,9)) where n can be 3 to 8.
       
       
       The input board is specified as a pair (n_grid, last_row). 
       The first element in the pair is a list of n length-10 lists.
       Each of the n lists represents a row of the grid. 
       If a -1 is in the list it represents an empty cell. 
       Otherwise if a number between 0--9 is in the list then this represents a 
       pre-set board position. E.g., the board
    
       ---------------------  
       |6| |1|5|7| | | |3| |
       | |9|7| | |2|1| | | |
       | | | | | |0| | | |1|
       | |9| |0|7| |3|5|4| |
       |6| | |5| |0| | | | |
       ---------------------
       would be represented by the list of lists
       
       [[6, -1, 1, 5, 7, -1, -1, -1, 3, -1],
        [-1, 9, 7, -1, -1, 2, 1, -1, -1, -1],
        [-1, -1, -1, -1, -1, 0, -1, -1, -1, 1],
        [-1, 9, -1, 0, 7, -1, 3, 5, 4, -1],
        [6, -1, -1, 5, -1, 0, -1, -1, -1,-1]]
       
       
       This routine returns model_1 which consists of a variable for
       each cell of the board, with domain equal to {0-9} if the board
       has a -1 at that position, and domain equal {i} if the board has
       a fixed number i at that cell.
       
       model_1 contains BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.).
       model_1 also constains n-nary constraints of sum constraints for each 
       column.
    '''
    """
    initial_tenner_board = (n_grid, last_row) tuple
    need to build a CSP object and variable_array list of lists
    model1 = built only using binary not-equal constraints for the row and contiguous cells constraints
             and n-ary sum constraints

    for the row, we have ten variables. v0 != v1, v0 != v2, v0 != v3 , ... , v8 != v9
        need to remember that v0 != v1 and v1 != v0 is the same. so should have 10c2 constraints

    for the contiguous, we already check left and right from row constraint. so check up/down, diagonal (top left,
        top rigt, bottom left, bottom right) for total of 6 spots
        make sure up/down and down/up aren't duplicates <~ is this even worth the time to check???

    for sum, the jth column need to sum to the jth entry in the last row

    """
    #IMPLEMENT
    board = initial_tenner_board[0]
    last_row = initial_tenner_board[1]
    variable_array = [[] for n in range(len(board))]

    #variables
    for i in range(len(board)):
        for j in range(len(board[0])):
            var_name = "V" + str(i) + str(j)
            if board[i][j] is not -1:
                #the domain is simply value of board[i][j]
                var = Variable(var_name, [board[i][j]])
            else:
                #the domain is 1-9 inclusive
                var = Variable(var_name, list(range(0,10)))
            variable_array[i].append(var)
    tenner_csp = CSP("tenner_csp_model_1", [var for var_list in variable_array for var in var_list])
    cons_list = []

    #making row constraints
    for row in variable_array:
        cons_list += row_not_eq_cons(row)

    #make contiguous constraints
    for con in contiguous_cons(variable_array):
        cons_list.append(con)

    #make column sum constraint
    np_vars = np.array(variable_array)
    for i in range(len(variable_array[0])):
        col_list = np_vars[:,i].tolist()
        con = Constraint("", col_list)
        con.add_satisfying_tuples(build_nary_sum_sat_tuples(col_list, last_row[i]))
        cons_list.append(con)

    #print(build_nary_sum_sat_tuples(variable_array[0], 10))
    for con in cons_list:
        tenner_csp.add_constraint(con)

    return tenner_csp, variable_array


def contiguous_cons(var_array):
    #want up, down, top left, top right, bottom left, bottom right
    cons_list = []

    max_y = len(var_array)-1
    max_x = len(var_array[0])-1

    for y in range(len(var_array)):
        for x in range(len(var_array[0])):
            temp_list = []
            this = var_array[y][x]

            if y > 0: #then y-1 is at least 0
                neighbour = var_array[y-1][x]
                con = Constraint("", [this, neighbour])
                con.add_satisfying_tuples(build_binary_sat_tuples(this, neighbour))
                temp_list.append(con)

                if x > 0:
                    neighbour = var_array[y - 1][x-1]
                    con = Constraint("", [this, neighbour])
                    con.add_satisfying_tuples(build_binary_sat_tuples(this, neighbour))
                    temp_list.append(con)
                if x < max_x:
                    neighbour = var_array[y - 1][x + 1]
                    con = Constraint("", [this, neighbour])
                    con.add_satisfying_tuples(build_binary_sat_tuples(this, neighbour))
                    temp_list.append(con)

            if y < max_y:
                neighbour = var_array[y + 1][x]
                con = Constraint("", [this, neighbour])
                con.add_satisfying_tuples(build_binary_sat_tuples(this, neighbour))
                temp_list.append(con)

                if x > 0:
                    neighbour = var_array[y + 1][x-1]
                    con = Constraint("", [this, neighbour])
                    con.add_satisfying_tuples(build_binary_sat_tuples(this, neighbour))
                    temp_list.append(con)
                if x < max_x:
                    neighbour = var_array[y + 1][x+1]
                    con = Constraint("", [this, neighbour])
                    con.add_satisfying_tuples(build_binary_sat_tuples(this, neighbour))
                    temp_list.append(con)

            cons_list += temp_list

    return cons_list

def row_not_eq_cons(row_list):
    cons_list = []
    for i in range(0,10):
        for j in range(i+1,len(row_list)):
            con = Constraint("", [row_list[i], row_list[j]])
            con.add_satisfying_tuples(build_binary_sat_tuples(row_list[i], row_list[j]))
            cons_list.append(con)

    return cons_list

def build_binary_sat_tuples(v1, v2):
    sat_tuples = []
    dom_v1 = v1.domain()
    dom_v2 = v2.domain()
    for t in itertools.product(dom_v1, dom_v2):
        if t[0] != t[1]:
            sat_tuples.append(t)

    return sat_tuples

def build_nary_sum_sat_tuples(var_list, _sum):
    dom_list = []
    sat_tuples = []
    for var in var_list:
        dom_list.append(var.domain())

    for t in itertools.product(*dom_list):
        if sum(t) == _sum:
            sat_tuples.append(t)

    return sat_tuples


##############################

def tenner_csp_model_2(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along 
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from 
       (0,0) to (n,9)) where n can be 3 to 8.

       The input board takes the same input format (a list of n length-10 lists
       specifying the board as tenner_csp_model_1.
    
       The variables of model_2 are the same as for model_1: a variable
       for each cell of the board, with domain equal to {0-9} if the
       board has a -1 at that position, and domain equal {i} if the board
       has a fixed number i at that cell.

       However, model_2 has different constraints. In particular,
       model_2 has a combination of n-nary 
       all-different constraints and binary not-equal constraints: all-different 
       constraints for the variables in each row, binary constraints for  
       contiguous cells (including diagonally contiguous cells), and n-nary sum 
       constraints for each column. 
       Each n-ary all-different constraint has more than two variables (some of 
       these variables will have a single value in their domain). 
       model_2 should create these all-different constraints between the relevant 
       variables.
    '''
    """
    for the row, we have all-different constraint for variables in each row
    """
    #IMPLEMENT
    board = initial_tenner_board[0]
    last_row = initial_tenner_board[1]
    variable_array = [[] for n in range(len(board))]

    #variables
    for i in range(len(board)):
        for j in range(len(board[0])):
            var_name = "V" + str(i) + str(j)
            if board[i][j] is not -1:
                #the domain is simply value of board[i][j]
                var = Variable(var_name, [board[i][j]])
            else:
                #the domain is 1-9 inclusive
                var = Variable(var_name, list(range(0,10)))
            variable_array[i].append(var)
    tenner_csp = CSP("tenner_csp_model_1", [var for var_list in variable_array for var in var_list])
    cons_list = []

    #making row constraints
    for row in variable_array:
        con = Constraint("", row)
        con.add_satisfying_tuples(row_all_diff_cons(row))
        cons_list.append(con)

    #make contiguous constraints
    for con in contiguous_cons(variable_array):
        cons_list.append(con)

    #make column sum constraint
    np_vars = np.array(variable_array)
    for i in range(len(variable_array[0])):
        col_list = np_vars[:,i].tolist()
        con = Constraint("", col_list)
        con.add_satisfying_tuples(build_nary_sum_sat_tuples(col_list, last_row[i]))
        cons_list.append(con)

    #print(build_nary_sum_sat_tuples(variable_array[0], 10))
    for con in cons_list:
        tenner_csp.add_constraint(con)

    return tenner_csp, variable_array

def row_all_diff_cons(row_list):
    dom_list = []
    sat_tuples = []
    blacklist_dom = []
    for var in row_list:
        temp_dom = var.domain()
        if len(temp_dom) == 1:
            blacklist_dom += temp_dom

    for var in row_list:
        temp_dom = var.domain()

        if len(temp_dom) == 1:
            dom_list.append(temp_dom)
        else:
            temp_dom = [val for val in temp_dom if val not in blacklist_dom]
            dom_list.append(temp_dom)

    for t in itertools.product(*dom_list):
        if len(set(t)) == 10:
            sat_tuples.append(t)

    return sat_tuples

b1 = ([[-1, 0, 1,-1, 9,-1,-1, 5,-1, 2],
       [-1, 7,-1,-1,-1, 6, 1,-1,-1,-1],
       [-1,-1,-1, 8,-1,-1,-1,-1,-1, 9],
       [ 6,-1, 4,-1,-1,-1,-1, 7,-1,-1],
       [-1, 1,-1, 3,-1,-1, 5, 8, 2,-1]],
      [29,16,18,21,24,24,21,28,17,27])

b2 = ([[6, -1, 1, 5, 7, -1, -1, -1, 3, -1],
       [-1, 9, 7, -1, -1, 2, 1, -1, -1, -1],
       [-1, -1, -1, -1, -1, 0, -1, -1, -1, 1],
       [-1, 9, -1, 0, 7, -1, 3, 5, 4, -1],
       [6, -1, -1, 5, -1, 0, -1, -1, -1, -1],],
      [21, 26, 21, 21, 29, 10, 28, 26, 21, 22])

if __name__ == "__main__":
    start_time = time.time()
    tenner_csp_model_1(b1)
    print("--- %s seconds for model1 b1 ---" % (time.time() - start_time))

    start_time = time.time()
    tenner_csp_model_1(b2)
    print("--- %s seconds for model1 b2 ---" % (time.time() - start_time))

    start_time = time.time()
    tenner_csp_model_2(b1)
    print("--- %s seconds for model2 b1 ---" % (time.time() - start_time))

    start_time = time.time()
    tenner_csp_model_2(b2)
    print("--- %s seconds for model2 b2 ---" % (time.time() - start_time))
