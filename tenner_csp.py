'''
Construct and return Tenner Grid CSP models.
Author: Richard Salas Chavez
'''

from cspbase import *
import itertools

########################################################################################################################
def tenner_csp_model_1(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner grid using model_1 and variable_array is a list of lists such that
       variable_array[i][j] is the Variable (object) that you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from (0,0) to (n,9)) where n can be 3 to 8.

       The input board is specified as a pair (n_grid, last_row).
       The first element in the pair is a list of n length-10 lists.
       Each of the n lists represents a row of the grid.
       If a -1 is in the list it represents an empty cell.
       Otherwise if a number between 0--9 is in the list then this represents a pre-set board position.
       E.g., the board

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
       has a 0 at that position, and domain equal {i} if the board has
       a fixed number i at that cell.

       model_1 contains BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.).
       model_1 also constains n-nary constraints of sum constraints for each
       column.
    '''

    board = initial_tenner_board[0] # initial_tenner_board is a list with two entries: the board and the sum of the cols
    col_sums = initial_tenner_board[1]

    var_array, var_array_csp = make_variable_array(board)
    tenner_csp = CSP("model_1", var_array_csp)  # make model_1 csp object

    sum_constraints(var_array, col_sums, tenner_csp)
    no_rep_row_bi(var_array, tenner_csp)
    check_adjacent_bi(var_array, tenner_csp)

    return tenner_csp, var_array
########################################################################################################################




'''
    makes an Variable object array the same size as the initial tenner board
    initializes each variables domain as a specific value if a value is specified
    otherwise if the value is -1 initializes the value to a list of the possible values it can be
'''
########################################################################################################################
def make_variable_array(initial_tenner_board):
    var_array = []
    csp_array = []
    for i, row in enumerate(initial_tenner_board):
        new_row = []
        var_array.append(new_row)
        for j, val in enumerate(row):
            value = []
            if val == -1:
                for n in range(10):
                    if n not in initial_tenner_board[i]:
                        value.append(n)  # make a variable
            else:
                value.append(val)

            variable = Variable("tenner_grid_var", value)
            new_row.append(variable)
            csp_array.append(variable)

    return var_array, csp_array
########################################################################################################################


'''
    generates n-nary constraints (constraint between n variables, in our case n is the number of rows) that ensures that
    all values in a column add up to the specified sum provided.
    loop through the variable arrays rows
    ery row has 10 entries so we should make 10 + 9 + 8 + 7 + 6 + 5 + 4 + 3 + 2 + 1 combinations of constraints
    he above is accomplished with a offset double for loop
'''
########################################################################################################################
def sum_constraints(variable_array, sums, csp):
    num_rows = len(variable_array)
    name = "sum_col_"

    for col in range(10):  # goes through every column
        scope = [variable_array[i][col] for i in range(num_rows)] # gets column

        name += str(col)
        new_c = Constraint(name, scope)  # make constraint for
        tot_sum = sums[col]  # what the variables in that column should add up to

        cur_domains = []
        for v in scope:  # go through scope and get cur_domains of each var
            cur_domains.append(tuple(v.cur_domain()))

        all_pos_sums = list(itertools.product(*cur_domains))

        satisfying_sums = []
        for s in all_pos_sums:
            if sum(s) == tot_sum:
                satisfying_sums.append(s)  # add to constraint

        new_c.add_satisfying_tuples(satisfying_sums)
        csp.add_constraint(new_c)
########################################################################################################################


'''
    generates binary constraints (constraint between two variables) that ensure that all values in row are different.
    loop through the variable arrays rows
    every row has 10 entries so we should make 10 + 9 + 8 + 7 + 6 + 5 + 4 + 3 + 2 + 1 combinations of constraints
    the above is accomplished with a offset double for loop
'''
#######################################################################################s#################################
def no_rep_row_bi(variable_array, csp):
    name = "no_rep_binary_row_"
    for n, row in enumerate(variable_array): # loop through each row
        name += str(row) + "_"

        # double for loop to accomplish different combinations of variables. That is, given 10 variables
        # (a, b, c, ..., h, i, j) => (a,b),(a,c), ..., (a,j) constraints are necessary to ensure value doesn't repeat
        for i in range(0, 9):
            v1 = row[i]
            name += str(v1) + "_"

            for j in range(i+1, 10):
                v2 = row[j]
                name += str(v2) + "_"

                c = Constraint(name, [v1, v2])
                c_flip = Constraint(name, [v2, v1])  # since order matters in scope

                sat_pairs = binary_not_equal_constraints(v1, v2, False)
                c.add_satisfying_tuples(sat_pairs)
                csp.add_constraint(c)

########################################################################################################################


'''
    given two variables will generate all permutations for those variables current domains given that the same
    value does not repeat
'''
########################################################################################################################
def binary_not_equal_constraints(v1, v2, flip=False):
    v1_dom = v1.cur_domain()
    v2_dom = v2.cur_domain()
    all_doms = [v1_dom,v2_dom]

    sat_pairs = []
    sat_pairs_flipped = []

    for tup in itertools.product(*all_doms):
        if no_repeat(tup):
            sat_pairs.append(tup)
            flip_tup = [tup[1],tup[0]]
            sat_pairs_flipped.append(tuple(flip_tup))

    if flip:
        return sat_pairs, sat_pairs_flipped

    return sat_pairs
########################################################################################################################


'''
    given a position in a tenner board variable array returns a list of tuples (x,y) that must be added to the current
    location indexes to get to the surrounding cells
'''
########################################################################################################################
def get_surr_cells_loc(num_rows, i, j):
    if (0 < i < (num_rows - 1)) and (0 < j < 9):  # check if in middle
        check = [(1, 0), (-1, 0), (-1, -1), (-1, 1), (1, 1), (1, -1)]  # checks cells above , below and diagonal to it

    elif (i == 0) and (0 < j < 9):  # if top row not top corners
        check = [(1, 0), (1, -1), (1, 1)]

    elif (i == (num_rows - 1)) and (0 < j < 9):  # if bottom row not bottom corners
        check = [(-1, 0), (-1, -1), (-1, 1)]

    elif (j == 0) and (0 < i < (num_rows - 1)):  # left column but not corners
        check = [(1, 0), (-1, 0), (-1, 1), (1, 1)]

    elif (j == 9) and (0 < i < (num_rows - 1)):  # right column but not corners
        check = [(1, 0), (-1, 0), (-1, -1), (1, -1)]

    elif (i == 0) and (j == 0):  # top left corner
        check = [(1, 0), (1, 1)]

    elif (i == 0) and (j == 9):  # top right corner
        check = [(1, 0), (1, -1)]

    elif (i == (num_rows - 1)) and (j == 0):  # bottom left corner
        check = [(-1, 0), (-1, 1)]

    elif (i == (num_rows - 1)) and (j == 9):  # bottom right corner
        check = [(-1, 0), (-1, -1)]

    else:
        check = [(0, 0)] # should not get here but if it does returning (0,0) wil not create any wrong constraints

    return check
########################################################################################################################


'''
    Checks adjacent cells including diagonals to apply correct contraints
    The constraint is that any cell cannot have any of the value directly around it being the same (including diagonals)
    we don't add adjacent row constraints since these are taken care of by no_rep_row_bi
    just need to check columns and diagonals
'''
########################################################################################################################
def check_adjacent_bi(var_array, csp):
    # loop through array
    num_rows = len(var_array)

    for i, row in enumerate(var_array):
        for j in range(10):
            # for columns we will only find constraints with cell below and flip constraints as they will be the same
            check = get_surr_cells_loc(num_rows, i, j)
            cur_cell = var_array[i][j]

            for tup in check:
                x = tup[0]
                y = tup[1]

                cell = var_array[i + x][j + y]

                sat_pairs = binary_not_equal_constraints(cur_cell, cell, False)

                c = Constraint("", [cur_cell, cell])
                c.add_satisfying_tuples(sat_pairs)
                csp.add_constraint(c)
########################################################################################################################


'''
    given a tuple of length n
    checks if that tuple has an entry more than once
    if it does it returns False as there is a repeat
    if it doesnt it return True as there isn't
'''
########################################################################################################################
def no_repeat(v_tup):
    for val in v_tup: # loop through v_tup (variables) and check if distinct
        if v_tup.count(val) > 1:  # found value more than once
            return False
    return True
########################################################################################################################




########################################################################################################################
def tenner_csp_model_2(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner using model_1
       and variable_array is a list of lists

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

    board = initial_tenner_board[0]  # initial_tenner_board is a list with two entries: the board and the sum of the cols
    col_sums = initial_tenner_board[1]

    var_array, var_array_csp = make_variable_array(board)
    tenner_csp = CSP("model_2", var_array_csp)

    sum_constraints(var_array, col_sums, tenner_csp)
    no_rep_row_n(var_array, tenner_csp)
    check_adjacent_bi(var_array, tenner_csp)

    return tenner_csp, var_array
########################################################################################################################




'''
    similar to no_rep_row_n
    given n variables will generate all permutations for those variables current domains given that the same
    value does not repeat
'''
########################################################################################################################
def no_rep_row_n(var_array, csp):
    name = "no_repeat_n_row_"
    for r, v in enumerate(var_array):
        name += str(r)
        c = Constraint(name, v)

        all_row_doms = []
        for val in v:
            all_row_doms.append(val.cur_domain()) # get all domains

        sat_vals = []
        for tup in itertools.product(*all_row_doms):
            if no_repeat(tup):
                sat_vals.append(tup)

        c.add_satisfying_tuples(sat_vals)
        csp.add_constraint(c)
########################################################################################################################
