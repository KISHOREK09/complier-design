import copy
# perform grammar augmentation
def grammarAugmentation(rules, nonterm_userdef,
						start_symbol):

	# newRules stores processed output rules
	newRules = []

	# create unique 'symbol' to
	# - represent new start symbol
	newChar = start_symbol + "'"
	while (newChar in nonterm_userdef):
		newChar += "'"

	# adding rule to bring start symbol to RHS
	newRules.append([newChar,
					['.', start_symbol]])

	# new format => [LHS,[.RHS]],
	# can't use dictionary since
	# - duplicate keys can be there
	for rule in rules:
	
		# split LHS from RHS
		k = rule.split("->")
		lhs = k[0].strip()
		rhs = k[1].strip()
		
		# split all rule at '|'
		# keep single derivation in one rule
		multirhs = rhs.split('|')
		for rhs1 in multirhs:
			rhs1 = rhs1.strip().split()
			
			# ADD dot pointer at start of RHS
			rhs1.insert(0, '.')
			newRules.append([lhs, rhs1])
	return newRules
# find closure
def findClosure(input_state, dotSymbol, aug):
    start_symbol = dotSymbol
    separatedRulesList = aug

    # closureSet stores processed output
    closureSet = []

    # if findClosure is called for
    # - 1st time i.e. for I0,
    # then LHS is received in "dotSymbol",
    # add all rules starting with
    # - LHS symbol to closureSet
    if dotSymbol == start_symbol:
        for rule in separatedRulesList:
            if rule[0] == dotSymbol:
                closureSet.append(rule)
    else:
        # for any higher state than I0,
        # set initial state as
        # - received input_state
        closureSet = input_state

    # iterate till new states are
    # - getting added in closureSet
    prevLen = -1
    while prevLen != len(closureSet):
        prevLen = len(closureSet)

        # "tempClosureSet" - used to eliminate
        # concurrent modification error
        tempClosureSet = []

        # if dot pointing at new symbol,
        # add corresponding rules to tempClosure
        for rule in closureSet:
            indexOfDot = rule[1].index('.')
            if rule[1][-1] != '.':
                dotPointsHere = rule[1][indexOfDot + 1]
                for in_rule in separatedRulesList:
                    if dotPointsHere == in_rule[0] and \
                            in_rule not in tempClosureSet:
                        tempClosureSet.append(in_rule)

        # add new closure rules to closureSet
        for rule in tempClosureSet:
            if rule not in closureSet:
                closureSet.append(rule)

    return closureSet
def compute_GOTO(state):
	global statesDict, stateCount

	# find all symbols on which we need to
	# make function call - GOTO
	generateStatesFor = []
	for rule in statesDict[state]:
		# if rule is not "Handle"
		if rule[1][-1] != '.':
			indexOfDot = rule[1].index('.')
			dotPointsHere = rule[1][indexOfDot + 1]
			if dotPointsHere not in generateStatesFor:
				generateStatesFor.append(dotPointsHere)

	# call GOTO iteratively on all symbols pointed by dot
	if len(generateStatesFor) != 0:
		for symbol in generateStatesFor:
			GOTO(state, symbol)
	return


def GOTO(state, charNextToDot):
	global statesDict, stateCount, stateMap

	# newState - stores processed new state
	newState = []
	for rule in statesDict[state]:
		indexOfDot = rule[1].index('.')
		if rule[1][-1] != '.':
			if rule[1][indexOfDot + 1] == \
					charNextToDot:
				# swapping element with dot,
				# to perform shift operation
				shiftedRule = copy.deepcopy(rule)
				shiftedRule[1][indexOfDot] = \
					shiftedRule[1][indexOfDot + 1]
				shiftedRule[1][indexOfDot + 1] = '.'
				newState.append(shiftedRule)

	# add closure rules for newState
	# call findClosure function iteratively
	# - on all existing rules in newState

	# addClosureRules - is used to store
	# new rules temporarily,
	# to prevent concurrent modification error
	addClosureRules = []
	for rule in newState:
		indexDot = rule[1].index('.')
		# check that rule is not "Handle"
		if rule[1][-1] != '.':
			closureRes = \
				findClosure(newState, rule[1][indexDot + 1])
			for rule in closureRes:
				if rule not in addClosureRules \
						and rule not in newState:
					addClosureRules.append(rule)

	# add closure result to newState
	for rule in addClosureRules:
		newState.append(rule)

	# find if newState already present
	# in Dictionary
	stateExists = -1
	for state_num in statesDict:
		if statesDict[state_num] == newState:
			stateExists = state_num
			break

	# stateMap is a mapping of GOTO with
	# its output states
	if stateExists == -1:
	
		# if newState is not in dictionary,
		# then create new state
		stateCount += 1
		statesDict[stateCount] = newState
		stateMap[(state, charNextToDot)] = stateCount
	else:
	
		# if state repetition found,
		# assign that previous state number
		stateMap[(state, charNextToDot)] = stateExists
	return


def generateStates(I0):
        statesDict[0] = I0
        stateCount = 0
        prev_len = -1
        called_GOTO_on = []
        # run loop till new states are getting added
        while (len(statesDict) != prev_len):
                prev_len = len(statesDict)
                keys = list(statesDict.keys())
                # make compute_GOTO function call
                # on all states in dictionary
                for key in keys:
                        if key not in called_GOTO_on:
                                called_GOTO_on.append(key)
                                compute_GOTO(key)
        return statesDict

# calculation of first
# epsilon is denoted by '#' (semi-colon)

# pass rule in first function
def first(rule):
	global rules, nonterm_userdef, \
		term_userdef, diction, firsts
	
	# recursion base condition
	# (for terminal or epsilon)
	if len(rule) != 0 and (rule is not None):
		if rule[0] in term_userdef:
			return rule[0]
		elif rule[0] == '#':
			return '#'

	# condition for Non-Terminals
	if len(rule) != 0:
		if rule[0] in list(diction.keys()):
		
			# fres temporary list of result
			fres = []
			rhs_rules = diction[rule[0]]
			
			# call first on each rule of RHS
			# fetched (& take union)
			for itr in rhs_rules:
				indivRes = first(itr)
				if type(indivRes) is list:
					for i in indivRes:
						fres.append(i)
				else:
					fres.append(indivRes)

			# if no epsilon in result
			# - received return fres
			if '#' not in fres:
				return fres
			else:
			
				# apply epsilon
				# rule => f(ABC)=f(A)-{e} U f(BC)
				newList = []
				fres.remove('#')
				if len(rule) > 1:
					ansNew = first(rule[1:])
					if ansNew != None:
						if type(ansNew) is list:
							newList = fres + ansNew
						else:
							newList = fres + [ansNew]
					else:
						newList = fres
					return newList
				
				# if result is not already returned
				# - control reaches here
				# lastly if eplison still persists
				# - keep it in result of first
				fres.append('#')
				return fres


# calculation of follow
def follow(nt):
	global start_symbol, rules, nonterm_userdef, \
		term_userdef, diction, firsts, follows
	
	# for start symbol return $ (recursion base case)
	solset = set()
	if nt == start_symbol:
		# return '$'
		solset.add('$')

	# check all occurrences
	# solset - is result of computed 'follow' so far

	# For input, check in all rules
	for curNT in diction:
		rhs = diction[curNT]
		
		# go for all productions of NT
		for subrule in rhs:
			if nt in subrule:
			
				# call for all occurrences on
				# - non-terminal in subrule
				while nt in subrule:
					index_nt = subrule.index(nt)
					subrule = subrule[index_nt + 1:]
					
					# empty condition - call follow on LHS
					if len(subrule) != 0:
					
						# compute first if symbols on
						# - RHS of target Non-Terminal exists
						res = first(subrule)
						
						# if epsilon in result apply rule
						# - (A->aBX)- follow of -
						# - follow(B)=(first(X)-{ep}) U follow(A)
						if '#' in res:
							newList = []
							res.remove('#')
							ansNew = follow(curNT)
							if ansNew != None:
								if type(ansNew) is list:
									newList = res + ansNew
								else:
									newList = res + [ansNew]
							else:
								newList = res
							res = newList
					else:
					
						# when nothing in RHS, go circular
						# - and take follow of LHS
						# only if (NT in LHS)!=curNT
						if nt != curNT:
							res = follow(curNT)

					# add follow result in set form
					if res is not None:
						if type(res) is list:
							for g in res:
								solset.add(g)
						else:
							solset.add(res)
	return list(solset)

# use statesDict to store the states
# use stateMap to store GOTOs
statesDict = {}
stateMap = {}
