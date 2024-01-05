import random
import time

import Constraint
import ConstraintNetwork
import Domain
import SudokuBoard
import Trail
import Variable

class BTSolver:
    """
    BTSolver (Backtracking Solver) for constraint satisfaction problems (CSPs)
    using backtracking techniques.
    """

    # ==================================================================
    # Constructors
    # ==================================================================
    def __init__(self, gb, trail, val_sh, var_sh, cc):
        """
        Initializes the BTSolver.

        :param gb: Game board.
        :param trail: Trail object for tracking assignments.
        :param val_sh: Value heuristic.
        :param var_sh: Variable heuristic.
        :param cc: Consistency checks.
        """
        self.network = ConstraintNetwork.ConstraintNetwork(gb)  # Initialize the constraint network
        self.hassolution = False                                # Initially, no solution is found
        self.gameboard = gb                                     # The game board
        self.trail = trail                                      # Trail for storing decisions

        # Heuristics and consistency checks
        self.varHeuristics = var_sh
        self.valHeuristics = val_sh
        self.cChecks = cc

    # ==================================================================
    # Consistency Checks
    # ==================================================================    
    def assignmentsCheck(self):
        """
        Perform a basic consistency check without propagation. 
        This method checks if the current assignments are consistent across all constraints.

        Returns:
            bool: True if the assignments are consistent, False otherwise.
        """
        for constraint in self.network.getConstraints():
            if not constraint.isConsistent():
                return False
        return True    

    def update_neighbor_domains(self, variable, assigned_value):
        updated_variables = {}
        for neighbor in self.network.getNeighborsOfVariable(variable):
            if neighbor.isChangeable and not neighbor.isAssigned():
                if neighbor.getDomain().contains(assigned_value):
                    neighbor.removeValueFromDomain(assigned_value)
                    updated_variables[neighbor] = neighbor.getDomain()
                    if neighbor.getDomain().size() == 0:
                        return {}, False
        return updated_variables, True

    def forwardChecking(self):
        """
        Implement the Forward Checking Heuristic. This method performs constraint 
        propagation and checks the consistency of the network. When a variable is 
        assigned, this method eliminates that value from the neighbors' domains.

        Returns:
            tuple: A pair (modified, consistent) where 'modified' is a dictionary of 
            modified variables with their updated domains, and 'consistent' is a bool 
            indicating whether the assignment is consistent.
        """
        modified = {}
        consistent = True
        assignedVars = [v for v in self.network.getVariables() if v.isAssigned()]

        for av in assignedVars:
            updated, is_consistent = self.update_neighbor_domains(av, av.getAssignment())
            if not is_consistent:
                return {}, False
            modified.update(updated)

        return modified, consistent
        
    # =================================================================
	# Arc Consistency
	# =================================================================

    def arcConsistency(self):
        """
        Implements arc consistency algorithm. This method iteratively removes values 
        from the domains of unassigned variables that are inconsistent with the current
        assignments, aiming to reduce the search space.
        """
        for variable in self.network.getVariables():
            if variable.isAssigned():
                updated, is_consistent = self.update_neighbor_domains(variable, variable.getAssignment())
                if not is_consistent:
                    return False
                for neighbor, domain in updated.items():
                    if domain.size() == 1:
                        neighbor.assignValue(domain.values[0])
        return True
    def norvigCheck(self):
        """
        Implements Norvig's heuristic for constraint propagation in a Sudoku solver. The method is now 
        structured to improve readability and modularity. It involves two main strategies:
        1. If a variable is assigned, eliminate that value from the square's neighbors.
        2. If a constraint has only one possible place for a value, then put the value there.

        This function orchestrates the process by first gathering all assigned variables and 
        then processing each for constraint propagation.

        Returns:
            tuple: A pair (ret, consistent) where 'ret' is a dictionary of variables that were
            assigned during propagation, mapped to the values they were assigned, and 'consistent'
            is a bool indicating whether the assignment is consistent.
        """
        assigned_vars = self.get_assigned_vars()
        return self.process_assigned_vars(assigned_vars)

    def get_assigned_vars(self):
        """
        Collects all currently assigned variables from the constraint network.

        Returns:
            list: A list of variables that are currently assigned.
        """
        return [v for v in self.network.getVariables() if v.isAssigned()]

    def process_assigned_vars(self, assigned_vars):
        """
        Processes each assigned variable to enforce constraints and propagate changes.

        Args:
            assigned_vars (list): List of assigned variables.

        Returns:
            tuple: A dictionary of newly assigned variables due to propagation and a boolean
            indicating whether the assignments are consistent.
        """
        ret = {}
        for av in assigned_vars:
            updated, consistent = self.update_neighbors(av)
            if not consistent:
                return {}, False
            ret.update(updated)
        return ret, self.network.isConsistent()

    def update_neighbors(self, variable):
        updated_variables, is_consistent = self.update_neighbor_domains(variable, variable.getAssignment())
        if not is_consistent:
            return {}, False

        # Check for single remaining value in domain and assign it
        for neighbor, domain in updated_variables.items():
            if domain.size() == 1:
                single_value = domain.values[0]
                neighbor.assignValue(single_value)
                updated_variables[neighbor] = neighbor.getDomain()

        return updated_variables, True

    def getTournCC(self):
        """
        Optional method for implementing an advanced constraint propagation strategy. 
        This is intended for use in a tournament setting.

        Returns:
            bool: The result of the advanced constraint propagation, if implemented.
        """
        return False
    
    # ==================================================================
    # Variable Selectors
    # ==================================================================

    def getfirstUnassignedVariable(self):
        """
        Selects the first unassigned variable from the network. This serves as a basic 
        variable selector.

        Returns:
            Variable: The first unassigned variable, or None if all variables are assigned.
        """
        for variable in self.network.getVariables():
            if not variable.isAssigned():
                return variable
        return None

    def getMRV(self):
        """
        Implements the Minimum Remaining Value (MRV) heuristic. It selects the unassigned 
        variable with the smallest domain.

        Returns:
            Variable: The unassigned variable with the smallest domain, or None if all 
            variables are assigned.
        """
        minDomainSize = float('inf')
        mrvVariable = None
        for variable in self.network.getVariables():
            if not variable.isAssigned() and variable.getDomain().size() < minDomainSize:
                minDomainSize = variable.getDomain().size()
                mrvVariable = variable
        return mrvVariable

    def MRVwithTieBreaker(self):
        """
        Implements the MRV heuristic with a degree heuristic as a tie breaker. This method 
        selects the unassigned variable with the smallest domain and affecting the most 
        unassigned neighbors.

        Returns:
            list: A list of unassigned variables with the smallest domain and most unassigned 
            neighbors. If there's only one such variable, returns a list of size 1 containing 
            that variable.
        """
        minDomainSize = float('inf')
        maxUnassignedNeighbors = -1
        candidates = []
        for variable in self.network.getVariables():
            if not variable.isAssigned():
                domainSize = variable.getDomain().size()
                unassignedNeighbors = len([n for n in self.network.getNeighborsOfVariable(variable) if not n.isAssigned()])

                if domainSize < minDomainSize or (domainSize == minDomainSize and unassignedNeighbors > maxUnassignedNeighbors):
                    minDomainSize = domainSize
                    maxUnassignedNeighbors = unassignedNeighbors
                    candidates = [variable]
                elif domainSize == minDomainSize and unassignedNeighbors == maxUnassignedNeighbors:
                    candidates.append(variable)

        return candidates

    def getTournVar(self):
        """
        Optional method for implementing an advanced variable selection heuristic for 
        tournament play.

        Returns:
            Variable: The variable selected by the advanced heuristic, or None if not implemented.
        """
        return None
    
    # ==================================================================
    # Value Selectors
    # ==================================================================

    def getValuesInOrder(self, v):
        """
        Provides a default value ordering for a given variable. 

        Args:
            v (Variable): The variable for which values are to be ordered.

        Returns:
            list: A list of values in the variable's domain, sorted in ascending order.
        """
        return sorted(v.getDomain().getValues())

    def getValuesLCVOrder(self, v):
        """
        Implements the Least Constraining Value (LCV) heuristic. This heuristic selects the 
        value that rules out the fewest choices for the neighboring variables in the constraint 
        network.

        Args:
            v (Variable): The variable for which values are to be ordered by LCV.

        Returns:
            list: A list of v's values sorted from least to most constraining on its neighbors.
        """
        constraintImpact = {}
        for value in v.getDomain().getValues():
            constraintImpact[value] = 0
            for neighbor in self.network.getNeighborsOfVariable(v):
                if not neighbor.isAssigned() and value in neighbor.getDomain().getValues():
                    constraintImpact[value] += 1

        # Sort the values based on how many choices they rule out for neighbors
        return sorted(v.getDomain().getValues(), key=lambda val: constraintImpact[val])


    def getTournVal(self, v):
        """
        Optional method for implementing an advanced value selection heuristic for tournament play.
        """
        return None

    # ==================================================================
    # Engine Functions
    # ==================================================================
    def solve(self, time_left=600):
        """
        Solves the constraint satisfaction problem using backtracking search. 

        Args:
            time_left (int): The remaining time to solve the problem.

        Returns:
            int: 0 if a solution is found, -1 if the solver runs out of time.
        """
        if time_left <= 0:
            return -1

        start_time = time.time()

        if self.hassolution:
            return 0

        variable = self.selectNextVariable()

        if variable is None:
            self.hassolution = True
            return 0

        for value in self.getNextValues(variable):
            self.trail.placeTrailMarker()
            self.trail.push(variable)

            variable.assignValue(value)

            if self.checkConsistency():
                elapsed_time = time.time() - start_time
                if self.solve(time_left - elapsed_time) == 0:
                    return 0

            self.trail.undo()

        return -1
    
    def checkConsistency(self):
        """
        Checks the consistency of the current assignments based on the selected consistency 
        check strategy.

        Returns:
            bool: True if the assignments are consistent, False otherwise.
        """
        consistencyCheckMethods = {
            "forwardChecking": self.forwardChecking,
            "norvigCheck": self.norvigCheck,
            "tournCC": self.getTournCC,
            "default": self.assignmentsCheck
        }
        return consistencyCheckMethods.get(self.cChecks, self.assignmentsCheck)()

    def selectNextVariable(self):
        """
        Selects the next variable to assign based on the selected variable selection heuristic.

        Returns:
            Variable: The next variable to assign, or None if no unassigned variables remain.
        """
        selectionMethods = {
            "MinimumRemainingValue": self.getMRV,
            "MRVwithTieBreaker": self.MRVwithTieBreaker,
            "tournVar": self.getTournVar,
            "default": self.getfirstUnassignedVariable
        }
        return selectionMethods.get(self.varHeuristics, self.getfirstUnassignedVariable)()

    def getNextValues(self, v):
        """
        Determines the next values to try for a given variable based on the selected value 
        selection heuristic.

        Args:
            v (Variable): The variable for which the next values are determined.

        Returns:
            list: A list of values to try for the variable.
        """
        valueSelectionMethods = {
            "LeastConstrainingValue": self.getValuesLCVOrder,
            "tournVal": self.getTournVal,
            "default": self.getValuesInOrder
        }
        return valueSelectionMethods.get(self.valHeuristics, self.getValuesInOrder)(variable)

    def getSolution(self):
        """
        Retrieves the solution to the constraint satisfaction problem, if one has been found.

        Returns:
            SudokuBoard: The solution as a Sudoku board, or the appropriate representation 
            based on the type of CSP.
        """
        return self.network.toSudokuBoard(self.gameboard.p, self.gameboard.q)