from flask import Flask,render_template,request
import copy
app= Flask(__name__)
@app.route('/')
def home():
    return render_template('home.html')
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
def findClosure(input_state, dotSymbol):
	global statesDict,aug1
	start_symbol=aug1[0][0][0]
	# closureSet stores processed output
	closureSet = []
	# if findClosure is called for
	# - 1st time i.e. for I0,
	# then LHS is received in "dotSymbol",
	# add all rules starting with
	# - LHS symbol to closureSet
	if dotSymbol == start_symbol:
		for rule in aug1[0]:
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
				for in_rule in aug1[0]:
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
		print('statecount',stateCount)
		statesDict[stateCount] = newState
		print(statesDict)
		stateMap[(state, charNextToDot)] = stateCount
	else:
	
		# if state repetition found,
		# assign that previous state number
		stateMap[(state, charNextToDot)] = stateExists
	return


def generateStates(statesDict):
	prev_len = -1
	called_GOTO_on = []

	# run loop till new states are getting added
	while (len(statesDict) != prev_len):
		prev_len = len(statesDict)
		keys = list(statesDict.keys())
		print('keys',keys)
		# make compute_GOTO function call
		# on all states in dictionary
		for key in keys:
			if key not in called_GOTO_on:
				called_GOTO_on.append(key)
				compute_GOTO(key)
	return

# calculation of first
# epsilon is denoted by '#' (semi-colon)

# pass rule in first function
def first(rule):
	global strl, nonl, \
		terl, diction, firsts
	
	# recursion base condition
	# (for terminal or epsilon)
	if len(rule) != 0 and (rule is not None):
		if rule[0] in terl:
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
	global  rules, nonterm_userdef, \
		term_userdef, diction, firsts, follows
	start_symbol=aug1[0][0][0]
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
def createParseTable(statesDict, stateMap, T, NT):
	global aug1, diction
	# create rows and cols
	rows = list(statesDict.keys())
	cols = T+['$']+NT
	print(rows)
	print(cols)
	# create empty table
	Table = []
	tempRow = ['']
	for y in range(len(cols)):
		tempRow.append('')
	for x in range(len(rows)):
		Table.append(copy.deepcopy(tempRow))

	# make shift and GOTO entries in table
	for entry in stateMap:
		state = entry[0]
		symbol = entry[1]
		# get index
		a = rows.index(state)
		b = cols.index(symbol)
		if symbol in NT:
			Table[a][b] = Table[a][b]\
				+ f"{stateMap[entry]} "
		elif symbol in T:
			Table[a][b] = Table[a][b]\
				+ f"S{stateMap[entry]} "

	# start REDUCE procedure

	# number the separated rules
	numbered = {}
	key_count = 0
	for rule in aug1[0]:
		tempRule = copy.deepcopy(rule)
		tempRule[1].remove('.')
		numbered[key_count] = tempRule
		key_count += 1

	# start REDUCE procedure
	# format for follow computation
	addedR = f"{aug1[0][0][0]} -> " \
		f"{aug1[0][0][1][1]}"
	strl.insert(0, addedR)
	for rule in strl:
		k = rule.split("->")
		
		# remove un-necessary spaces
		k[0] = k[0].strip()
		k[1] = k[1].strip()
		rhs = k[1]
		multirhs = rhs.split('|')
		
		# remove un-necessary spaces
		for i in range(len(multirhs)):
			multirhs[i] = multirhs[i].strip()
			multirhs[i] = multirhs[i].split()
		diction[k[0]] = multirhs

	# find 'handle' items and calculate follow.
	for stateno in statesDict:
		for rule in statesDict[stateno]:
			if rule[1][-1] == '.':
			
				# match the item
				temp2 = copy.deepcopy(rule)
				temp2[1].remove('.')
				for key in numbered:
					if numbered[key] == temp2:
					
						# put Rn in those ACTION symbol columns,
						# who are in the follow of
						# LHS of current Item.
						follow_result = follow(rule[0])
						for col in follow_result:
							index = cols.index(col)
							if key == 0:
								Table[stateno][index] = "Accept"
							else:
								Table[stateno][index] =\
									Table[stateno][index]+f"R{key} "
	coll.append(cols)
	return Table
@app.route('/parse_input', methods=['POST','GET'])
def parse_input():
    if request.method=="POST":
        global stateCount
        if(len(strl)>0 or len(terl)>0 or len(nonl)>0 or len(aug1)>0 or len(coll)>0 or len(statesDict)>0 or len(stateMap)>0 or len(diction)>0):
            strl.clear()
            terl.clear()
            nonl.clear()
            aug1.clear()
            coll.clear()
            statesDict.clear()
            stateMap.clear()
            diction.clear()
            stateCount = stateCount-stateCount
        result=[]
        str1=""
        str2=""
        str3=""
        string=request.form.get('inputString')
        terminal=request.form.get('terminal')
        nonterminal=request.form.get('nonterminal')
        for i in string:
            if(i=="\r"):
                pass
            elif(i=="\n"):
                strl.append(str1)
                str1=""
            else:
                str1+=i
        strl.append(str1)
        '''---------------------------'''
        for i in nonterminal:
            if(i==","):
                nonl.append(str2)
                str2=""
            else:
                str2+=i
        nonl.append(str2)
        '''---------------------------'''
        for i in terminal:
            if(i==","):
                terl.append(str3)
                str3=""
            else:
                str3+=i
        terl.append(str3)
        '''---------------------------'''
        '''----------Augmentation-------'''
        start=nonl[0]
        aug=grammarAugmentation(strl,nonl,start)
        aug1.append(aug)
        '''-------calculated closure------'''
        start_sym=aug[0][0]
        I0=findClosure(0,start_sym)
        '''-----------State Generate--------'''
        #print('i0',I0)
        statesDict[0] = I0
        generateStates(statesDict)
        #print('statedict',statesDict)
        table=createParseTable(statesDict, stateMap,
				terl,
				nonl)
        return render_template('slr.html',org=strl,aug=aug,I0=I0,state=statesDict,statemap=stateMap,table1=table,col2=coll[0])
    return render_template('slr.html')
@app.route('/about')
def about():
    return render_template('about.html')
statesDict = {}
stateMap = {}
diction = {}
stateCount = 0
strl=[]
terl=[]
nonl=[]
aug1=[]
coll=[]
if __name__ == '__main__':
    app.run(debug=True)
