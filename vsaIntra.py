### modifies tempDataFlow6.py to enhance memory W/R related operations.Now the memory
### is accessed in chunks, separately for each offset.

import os
import sys

sys.path.append(os.path.join(os.path.dirname(__file__), "BinNavi.jar"))
sys.path.append(os.path.join(os.path.dirname(__file__), "REIL.jar"))
sys.path.append(os.path.join(os.path.dirname(__file__), "mysql-connector-java-5.1.15-bin.jar"))
#print sys.path
from javax.swing import JButton, JFrame, JTextArea, JTextField, SwingUtilities, JOptionPane
from java.awt import BorderLayout, Graphics
from java.awt.Window import dispose
from BinNavi.API.plugins import StandAlone
from BinNavi.API.reil.mono import *
from BinNavi.API.helpers import *
from BinNavi.API.helpers.Tree import *
from BinNavi.API.reil.ReilHelpers import *
from sets import Set
from operator import itemgetter
import time
from struct import pack, unpack

##################### Global definitions ############################
ANYVAL = 'anyval' # represents any instruction node
NOVAL = 'noval' # represents no instruction node
INITVAL = 'initval' # represents initial instruction node which is used to initialize operands
INIT_ESP='initESP' # represents the initial value for ESP register.
MAX_NUM=10 # this is the maximal size of the different possible offsets in memory
####################################################################


###############################################################################
### The following methods are used for the calculation of Dataflow solution. ##
###############################################################################

###### Reaching definitions calculation #######   
# This function creates the initial state of the state vector passed to the
# monotone framework. In the beginning the state of each instruction is defined
# as <INITVAL, {0}>. Note: this assumption will change in Interprocedural analysis.

def generateStartVector(graph):
	startVector = DefaultStateVector()

	for node in graph:
		element = SkeletonLatticeElement()
        #element.inVal.add((u'esp', 'initval_esp', frozenset([0])))
		startVector.setState(node, element)

	return startVector

# This class is used for the elements of the lattice. Each lattice element
# is used to keep track of the known state for a REIL instruction during
# analysis. Since this plugin keeps track of reached variables, the kept
# state says what definitions are present at the beginning and at the end of state.
# the state is address descriptor defined as A=<I, X>, where I is statement address or
# special tags - ANYVAL, NOVAL, INITVAL. X is the result of the instruction on the register.
# For constants c (immediate values), A = <INITVAL, {c}>.
class SkeletonLatticeElement(ILatticeElement):
	def __init__(self):
		self.inVal  = Set()
		self.out = Set()
		self.memoryWritten=None # this is for recording the memory location

	def equals(self, rhs):
		#  This function helps MonoREIL to end the fixed point iteration.
		# rhs is the value set of previous iteration i.e. currentOUT in this implementation.
		if len(self.out) != len(rhs.out):
			return False
		for (op, adr, val) in self.out:
			for (op1, adr1, val1) in rhs.out:
				if op == op1:
					#if adr == adr1 and adr != INIT_ESP and val != val1:
					if adr == adr1:
						if len(val) < MAX_NUM or len(val1) < MAX_NUM:
							if val != val1:
								return False
					if adr != adr1:
						return False
					break
			else:
				return False
		return True
		
		#return self.out == rhs.out

	def lessThan(self, rhs):
		# This function helps MonoREIL to check the monotonous requirement.
		# rhs is the value set of previous iteration i.e. currentOUT in this implementation.
		#print "LESS THAN RHS", sorted(rhs.out,key=itemgetter(0))
		#print "LESS THAN SELF", sorted(self.out,key=itemgetter(0))
		return False
		for (op, adr, val) in rhs.out:
			regAbsent=True
			for (op1, adr1, val1) in self.out:
				if op == op1:
					regAbsent=False
					if adr == ANYVAL and adr1 != ANYVAL:
						print 'ANYVAL case ', op, adr1, val, val1
						return True
										
					if adr1 != ANYVAL and adr == adr1:
						if val1 < val:
							print 'different X', op, adr
							return True
					
			if regAbsent == True:
				print 'reg absence', op, sorted(rhs.out,key=itemgetter(0)), '\n',sorted(self.out,key=itemgetter(0))
				# this condition checks that one particular register is not present in the last iteration.
				return True
		#print "ALL case"
		return False
	
	def lessThanIn(self, rhs):
		# This function helps MonoREIL to check the monotonous requirement.
		# rhs is the value set of previous iteration i.e. currentOUT in this implementation.
		if len(self.inVal) == 0:
			return False
		for (op, adr, val) in self.inVal:
			regAbsent=True
			for (op1, adr1, val1) in rhs.inVal:
				if op == op1:
					if adr1 == ANYVAL and adr != ANYVAL:
						print 'ANYVAL IN case', op, adr, val, val1
						return True
					if adr1 ==INITVAL:
						return False
					regAbsent=False
					if adr == ANYVAL:
						return False
					if adr == adr1 and val >= val1:
						return False
					if adr != adr1:
						return False
			if regAbsent == True:
				# this condition checks that one particular register is not present in the last iteration.
				return False		
		return True
	#def equalMod

		#return self.inVal < rhs.inVal and self.out < rhs.out

## for RD, we use the equ. RDin(S)= \union _ p\in pred(S) {RDout(p)}

# This class defines the lattice used by the monotone framework. Its only
# purpose is to defined a function that is used to combine a list of states
# into one state.
class SkeletonLattice(ILattice):
	''' Apart from doing a meet for different states (predecessors of the the current
	node), this class also does widening operation on individual instruction.
	When a register r has address descriptors on two or more predecessors (r, I1, X1)
	and (r, I2, X2), it has to be merged into one address descriptor by the following rules:
	1. If I1=I2, the (r, I1, {X1 U X2})
	2. If I1 <> I2 and I1, I2 not Top, then widening is bot ie. (r, I,{}). '''
	
	def combine(self, states):
		combinedState = SkeletonLatticeElement()
		combinedState2 = SkeletonLatticeElement()
		# this si a local set to determine the addition of the last element.
		# the reason to use this is: in the case of the last element, we canot compare
		# it with other elements as there are none. So, should we add it or discard it?
		usedRegs=Set()
						
		for state in states:
			print 'state', sorted(state.element.out,key=itemgetter(0))
		#combinedState.inVal = combinedState.inVal.union(state.element.out)
			combinedState.inVal.update(state.element.out)
		
		tempinVal=Set().union(combinedState.inVal)# create a copy set to be used as working list
		for (op, adr, val) in combinedState.inVal:
			#addedElement=False
			tempinVal.discard((op, adr, val))
			if op in usedRegs:
				# if the operand has been anlayzed, skip it.
				continue
			usedRegs.add(op)
			opCousins=Set() #set to contain all the address descriptors for the same operand s.t I != INITVAL
			opCousinsINIT=Set() #set to contain all the address descriptors for the same operand s.t I=INITVAL
			for (op1, adr1, val1) in Set().union(tempinVal):
				if op == op1:
					opCousins.add((op1, adr1, val1))
			if len(opCousins)==0:
				# this means that the current op has no other entry
				combinedState2.inVal.add((op, adr, val))
			else:
				# remove these elemensts as they are going to be analyzed in this
				# iteration and should not appear in the next iteration

				tempinVal.difference_update(opCousins)
				# add the current element in the set of opCousins
				opCousins.add((op, adr, val))
				opCousinsINIT=Set()
				for (op1, adr1, val1) in Set().union(opCousins):
					if adr1 == INITVAL:
						opCousinsINIT.add((op1, adr1, val1))
						opCousins.discard((op1, adr1, val1))
				
				if len(opCousins) !=0:
					
					howMany=0
					for (op2,adr2,val2) in opCousins:
						
						tempVal=Set()
						for (op3,adr3,val3) in opCousins:
							if adr2 == adr3:
								#combinedState2.inVal.add((op2, ANYVAL, frozenset()))
								tempVal.update(val3)
								howMany=howMany+1
								
								
						break
					if howMany == len(opCousins):
						combinedState2.inVal.add((op2, adr2, frozenset(tempVal)))	   
					else:
						combinedState2.inVal.add((op2, ANYVAL, frozenset()))
						
							
						
								

				else:
					tempVal=Set()
					for (op2,adr2,val2) in opCousinsINIT:
						tempVal.update(val2)
					combinedState2.inVal.add((op, INITVAL, frozenset(tempVal)))
		#print 'combined', combinedState2.inVal			
		return combinedState2						
				
					
					

## transfer function is defined => how does REIL instruction affect a state.

# This class provides the transformations each instruction has on a state. For
# each instruction of the instruction graph, the current state of the instruction
# and the combined state of the influencing nodes is passed to the function.
# The function returns the state of the instruction while considering the input
# states.
class SkeletonTransformationProvider(ITransformationProvider):
	''' This is the transfer fucntion for the LFP solution. The transfer function
	is defined for each REIL instruction as per its semantic. there will be a address
	descriptor for each operand op at each instruction I s.t. (op, I, frozenset()).
	The frozenset() is a set of values that are calculated for op at instruction I.
	Each operand is assumed to have an initial value (op, INITVAL, (0)).'''
	
	def __init__(self):
		#self.defs=Set() #defs is the set that contains all the definitions made in the code. This method is called more than once so avoid duplicates
		#self.usedRegs=Set() # set to keep information about the first use of registers
		self.allAdr=Set()
		self.iterCount=0
		#self.REPEAT=False
		self.FLAGS=['CF','PF','AF','ZF','SF','TF','IF','DF','OF','IOPL','NT','RF','VM','AC','VIF','VIP','ID']
		self.allMemoryWritten=True
		self.memoryLocVisited=Set()
		self.firstCall=True
	
	def get_memory_locations(self,pre,offsets):
		'''
		This is the helper function to get memory chunks from the a-loc denoted
		by <pre, offsets>. It creates a list of memory locations wherein each 
		member is of the form "pre<f>", where f \in offsets.
		
		'''
		return [str(pre)+'+'+str(f) for f in offsets]
	
	
	def transform(self, node, currentState, influencingState):
##		if influencingState.lessThanIn(currentState) ==True:
##			print "influence Current compare \n"
##			print node.getInstruction(), '\n'
##			print influencingState.inVal,'\n',currentState.inVal
##			print "#######################################"
##			sys.exit()  
			
			
		
		

		#assignments made by this node
		gen = Set()
		#assignments killed by this node
		#kill = Set()
		transformed_state = SkeletonLatticeElement()
		transformed_state2 = SkeletonLatticeElement() # related to widening
		instruction = node.getInstruction()
		if isFunctionCall(instruction):
			print "\nThis is a function call at ", instruction.getAddress(),"\n"
		#### to print the iteration #########
		
		if instruction.getAddress() not in self.allAdr:
				self.allAdr.add(instruction.getAddress())
		else:
			self.allAdr.clear()
			#self.allAdr.add(instruction.getAddress())
			self.iterCount=self.iterCount+1
			print '@@@ iteration ', self.iterCount
		######################################	
		
			
				
		
		#if instruction.getAddress() in (0x40101A00, 0x40101702):
		#print '#### ',instruction
		# check if the operands are used first time to initialize their value
		# as (op, init_op, {0})
		#print "usedReg", self.usedRegs
##		print "f op", instruction.firstOperand.value
##		print "s op", OP2+4
##		print "t op", instruction.thirdOperand.value
		#### Initialization of operands #############
		## check for the first instruction of the 1st iteration and initialized ESP in
		## influencingState
		if self.firstCall == True:
			influencingState.inVal.add((u'esp',INIT_ESP,  frozenset([0])))
			self.firstCall=False
		### Let us do a check in the begining of the instruction to check if this is a
		### STM instruction with third op as ESP. If so, skip this inst as this 
		### inst is not required to be computed. It is only pushing some value onto
		### the stack. In this case, we'll juct return the inVal as outVal.
		if instruction.mnemonic == 'stm' and instruction.thirdOperand.value == 'esp':
			transformed_state.inVal.update(influencingState.inVal)
			transformed_state.out.update(influencingState.inVal)
			
			return transformed_state
		##############################################
		firstConst= True
		secondConst= True
		firstOP=False
		secondOP=False
		thirdOP=False
		if isRegister(instruction.getFirstOperand()) or instruction.firstOperand.value in self.FLAGS:
			firstConst=False
			for (opr, adr, val) in influencingState.inVal:
				if opr == instruction.firstOperand.value:
					src1=(opr, adr, val)
					firstOP=True
					break
##			else:
##				if instruction.firstOperand.value == 'esp':
##					influencingState.inVal.add((instruction.firstOperand.value, INIT_ESP, frozenset([0])))
##					src1=(instruction.firstOperand.value, INIT_ESP, frozenset([0]))
##					firstOP=True
##				else:
##					influencingState.inVal.add((instruction.firstOperand.value, INITVAL, frozenset([0])))
##					src1=(instruction.firstOperand.value, INITVAL, frozenset([0]))
		else:
			if instruction.firstOperand.value:
				#print "OP1", instruction.firstOperand.value
				OP1=unpack('l',pack('L',int(instruction.firstOperand.value)&0xffffffff))[0]
				#print OP1
		
		if isRegister(instruction.getSecondOperand()) or instruction.secondOperand.value in self.FLAGS:
			secondConst=False
			
			for (opr, adr, val) in influencingState.inVal:
				if opr == instruction.secondOperand.value:
					src2=(opr, adr, val)
					secondOP=True
					break
##			else:
##				if instruction.secondOperand.value =='esp':
##					influencingState.inVal.add((instruction.secondOperand.value, INIT_ESP, frozenset([0])))
##					src2=(instruction.secondOperand.value, INIT_ESP, frozenset([0]))
##					secondOP=True
##				else:
##					influencingState.inVal.add((instruction.secondOperand.value, INITVAL, frozenset([0])))
##					src2=(instruction.secondOperand.value, INITVAL, frozenset([0]))
		else:
			if instruction.secondOperand.value:
				#print "OP2", instruction.secondOperand.value
				OP2=unpack('l',pack('L',int(instruction.secondOperand.value)&0xffffffff))[0]
				#print OP2
		### We need to know the 3dr operand address descriptor for STM instruction
		if instruction.mnemonic == 'stm':
			for (opr, adr, val) in influencingState.inVal:
				if opr == instruction.thirdOperand.value:
					src3=(opr, adr, val)
					thirdOP=True
					break
##			else:
##				if instruction.thirdOperand.value =='esp':
##					#influencingState.inVal.add((instruction.thirdOperand.value, INIT_ESP, frozenset([0])))
##					src3=(instruction.thirdOperand.value, INIT_ESP, frozenset([0]))
##					thirdOP=True
##				else:
##					#influencingState.inVal.add((instruction.thirdOperand.value, INITVAL, frozenset([0])))
##					src3=(instruction.thirdOperand.value, INITVAL, frozenset([0]))
					  
		transformed_state.inVal.update(influencingState.inVal)
		kill=Set() # variable to keep the cuurent value of the 3rd operand that will be killed after this instruction
##		uninitializedESP=False
##		if firstConst == False:
##			if src1[1] == INITVAL:
##				if instruction.thirdOperand.value == 'esp':
##					gen.add((instruction.thirdOperand.value, INIT_ESP, frozenset([0])))
##					for (o, a, v) in influencingState.inVal:
##						if o == instruction.thirdOperand.value:
##							kill=(o, a, v)
##							break
##					uninitializedESP=True
##		else:
##			if secondConst == False:
##				if src2[1] == INITVAL:
##					if instruction.thirdOperand.value == 'esp':
##						gen.add((instruction.thirdOperand.value, INIT_ESP, frozenset([0])))
##						for (o, a, v) in influencingState.inVal:
##							if o == instruction.thirdOperand.value:
##								kill=(o, a, v)
##								break
##						uninitializedESP=True
		
		#the third operand is always the defined one except from jumps and comparisons instructions
		if instruction.thirdOperand.value != '' and instruction.mnemonic not in ("jcc","bisz","nop"):# and uninitializedESP == False:
			#print instruction
			#print 'influence',influencingState.inVal
		   
##			print 'currentIn', currentState.inVal
##			print 'currentOut', currentState.out

			
			#print 'src1', src1
			#print 'src2', src2
			#transformed_state.inVal.update(influencingState.inVal)
			#print 'influence',influencingState.inVal		
			### for Kill, remove the existing address descriptor of thirdOperand. This is kept in kill and removed later in the out
			### this is NOT done for STM as it does not change the operand valye, but memory contents refrenced by it.
##			if instruction.mnemonic != 'stm':
##				
##				for (r, ad, vl) in transformed_state.inVal:
##					if instruction.thirdOperand.value == r:
##						kill=(r, ad, vl)
##						#transformed_state.inVal.discard((r, ad, vl))
##						break

			##### transfer functions for various instructions #################
			
			#### transfer function for ADD ###########
			if instruction.mnemonic == 'add':
				if firstConst == True and secondConst == True:
					gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1+OP2])))
				elif firstConst == True and secondConst == False and secondOP==True:
					#### TO DO case of ANYVAL
					gen.add((instruction.thirdOperand.value,src2[1],self.constSetOP(OP1, src2[2], 'add')))
				elif firstConst == False and secondConst==True and firstOP==True:
					gen.add((instruction.thirdOperand.value,src1[1],self.setConstOP(src1[2],OP2, 'add')))
				elif firstOP==True and secondOP==True:
					if src1[1] == src2[1]:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'add')))
					elif src1[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src2[1],self.setSetOP(src1[2],src2[2], 'add')))
					elif src2[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'add')))
						
					else:
						gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
				else:
					pass
			
			#### transfer function for AND ###########
			if instruction.mnemonic == 'and':
				if firstConst == True and secondConst == True:
					gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1&OP2])))
				elif firstConst == True and secondConst == False and secondOP==True:
					gen.add((instruction.thirdOperand.value,src2[1],self.constSetOP(OP1, src2[2], 'and')))
				elif firstConst == False and secondConst==True and firstOP==True:
					gen.add((instruction.thirdOperand.value,src1[1],self.setConstOP(src1[2],OP2, 'and')))
				elif firstOP==True and secondOP==True:
					if src1[1] == src2[1]:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'and')))
					elif src1[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src2[1],self.setSetOP(src1[2],src2[2], 'and')))
					elif src2[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'and')))
					else:
						gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
				else:
					pass
							   
				
			#### transfer function for BSH ###########
			if instruction.mnemonic == 'bsh':
				if firstConst == True and secondConst == True:
					if OP2 <0:
						gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1>>abs(OP2)])))
					else:
						gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1<<abs(OP2)])))
				elif firstConst == True and secondConst == False and secondOP==True:
					gen.add((instruction.thirdOperand.value,src2[1],self.constSetOP(OP1, src2[2], 'bsh')))
				elif firstConst == False and secondConst==True and firstOP==True:
					gen.add((instruction.thirdOperand.value,src1[1],self.setConstOP(src1[2],OP2, 'bsh')))
				elif firstOP==True and secondOP==True:
					if src1[1] == src2[1]:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'bsh')))
					elif src1[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src2[1],self.setSetOP(src1[2],src2[2], 'bsh')))
					elif src2[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'bsh')))
					else:
						gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
				else:
					pass
						
			
			#### transfer function for DIV ###########
			if instruction.mnemonic == 'div':
				if firstConst == True and secondConst == True:
					gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1/OP2])))
				
				elif firstConst == False and secondConst==True and firstOP==True:
					gen.add((instruction.thirdOperand.value,src1[1],self.setConstOP(src1[2],OP2, 'div')))
				elif firstOP==True and secondOP==True:
					# start a new definition
					gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
				else:
					pass
			
			#### transfer function for LDM ###########
			if instruction.mnemonic == 'ldm':

				if firstOP==True:			  
					## we first get the memory chunks
					op1Str=self.get_memory_locations(src1[1],src1[2])
					## now we have two cases:
					## 1. all of the above obtained memory chunks have same base address
					## in this case, we take the union over vals (offsets)
					## 2. Otherwise, we create ANY (top)
					## there is another possibility. Out of all memory chunks, some are still not defined
					## in this case also, we create ANY (top) 
					#memFound=False
					cAdr=None # create empty string to keep the cuurent base 'adr'
					cVal=Set()
					allSame=True
					for mem in op1Str:
						for (opr, adr, val) in influencingState.inVal:
							if mem == opr:
								if cAdr == None:
									cAdr=adr # this will be set only the first time
								if cAdr == adr: # to check that all the memory chunks have same base
									cVal.update(val) # take the union of the offsets
									break
								else:
									gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
									#gen.add((instruction.thirdOperand.value,ANYVAL, frozenset()))
									allSame=False
									break
								
						else: # This is the end of the inner FOR loop. If any memory chunks is not defined, we start a new definiton.
							print "added 2nd case of new definition"
							if len(op1Str) ==1:
							## it means there is only one entry for the adr.
								gen.add((instruction.thirdOperand.value,op1Str[0],frozenset([0])))
							else:
								gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
							#gen.add((instruction.thirdOperand.value,src1[1],src1[2]))
							allSame=False
							break
					# else:
						# if len(op1Str) ==1:
							# ## it means there is only one entry for the adr.
							# gen.add((instruction.thirdOperand.value,op1Str[0],frozenset([0])))
						# allSame=False		
					if allSame == True:
						gen.add((instruction.thirdOperand.value,adr,frozenset(cVal)))
					
					
					
				else:
					pass
						
					
			
			#### transfer function for MOD ###########
			if instruction.mnemonic == 'mod':
				if firstConst == True and secondConst == True:
					gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1%OP2])))
				
				elif firstConst == False and secondConst==True and firstOP==True:
					gen.add((instruction.thirdOperand.value,src1[1],self.setConstOP(src1[2],OP2, 'mod')))
				elif firstOP==True and secondOP==True:
					# start a new definition
					gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
				else:
					pass
			
			#### transfer function for MUL ###########
			if instruction.mnemonic == 'mul':
				if firstConst == True and secondConst == True:
					gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1*OP2])))
				elif firstConst == True and secondConst == False and secondConst==True:
					gen.add((instruction.thirdOperand.value,src2[1],self.constSetOP(OP1, src2[2], 'mul')))
				elif firstConst == False and secondConst==True and firstOP==True:
					gen.add((instruction.thirdOperand.value,src1[1],self.setConstOP(src1[2],OP2, 'mul')))
				elif firstOP==True and secondOP==True:
					if src1[1] == src2[1]:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'mul')))
					elif src1[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src2[1],self.setSetOP(src1[2],src2[2], 'mul')))
					elif src2[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'mul')))
					else:
						gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
				else:
					pass
						
			#### transfer function for OR ###########
			if instruction.mnemonic == 'or':
				if firstConst == True and secondConst == True:
					gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1|OP2])))
				elif firstConst == True and secondConst == False and secondConst==True:
					gen.add((instruction.thirdOperand.value,src2[1],self.constSetOP(OP1, src2[2], 'or')))
				elif firstConst == False and secondConst==True and firstOP==True:
					gen.add((instruction.thirdOperand.value,src1[1],self.setConstOP(src1[2],OP2, 'or')))
				elif firstOP==True and secondOP==True:
					if src1[1] == src2[1]:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'or')))
					elif src1[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src2[1],self.setSetOP(src1[2],src2[2], 'or')))
					elif src2[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'or')))
					else:
						gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
				else:
					pass
			
			#### transfer function for STM ###########
			## TO DO: Add another variable in lattice element to present the 
			## mapping between 3rd operand and its memory contents. THis is useful
			## for extracing infomation about memory once the result is obtained.
			
			if instruction.mnemonic == 'stm':
				if thirdOP ==False:
					pass
				else:
					op3Str=self.get_memory_locations(src3[1],src3[2])
					# update this memory location for the current STM node
					transformed_state.memoryWritten=op3Str
					self.memoryLocVisited.update(Set(op3Str))
					if src3[1] not in (ANYVAL, NOVAL):
						self.allMemoryWritten=False
						
						# also kill the existing descriptor for this memory loc chunks.
						for mem in op3Str:
							nVal=True
							fOP=True
							for (r, ad, vl) in transformed_state.inVal:
								if firstConst == True:
									print "STM-Const case"
									if mem == r:
										kill.add((r,ad,vl))
										print "killing ", r
										if len(src3[2])>1:
											# this is for weak update
											if ad == NOVAL:
												print "Doing week update at: ",instruction.getAddress()
												gen.add((mem, NOVAL, frozenset(vl.union(Set([OP1])))))
											else:
												gen.add((mem,ANYVAL,frozenset()))
										else:
											# strong update
											print "Doing string update at: ", instruction.getAddress()
											gen.add((mem, NOVAL, frozenset([OP1])))
										nVal=True
										break
									else:
										nVal=False
										#gen.add((mem, NOVAL, frozenset([OP1])))
								elif firstOP==True:
									if mem == r:
										print "kill entry added for ",r 	
										kill.add((r,ad,vl))
										if len(src3[2])>1:
											if ad == src1[1]:
												#print "val is greater"
												print "Doing week update at: ",instruction.getAddress(), mem
												gen.add((mem, src1[1], frozenset(vl.union(src1[2]))))
											else:
												gen.add((mem,ANYVAL,frozenset()))
										else:
											print "Doing strong update at: ",instruction.getAddress(), mem
											gen.add((mem, src1[1], src1[2]))
										fOP=True
										break
									else:
										fOP=False
										#gen.add((mem, src1[1], src1[2]))
								else:
									print "no STM case matched"
									pass
								#if mem == r:
									#kill.add((r, ad, vl))
									
								#transformed_state.inVal.discard((r, ad, vl))
									#break
							if nVal ==False:
								gen.add((mem, NOVAL, frozenset([OP1])))
							if fOP ==False:
								print "entry not found update", mem
								gen.add((mem, src1[1], src1[2]))
							
						# and now generate the new descriptor
##						if firstConst == True:
##							print "STM-Const case"
##							for mem in op3Str:
##								
##								gen.add((mem, NOVAL, frozenset([OP1])))
##						elif firstOP==True:
##							for mem in op3Str:
##								gen.add((mem, src1[1], src1[2]))
##						else:
##							pass
					elif src3[1] == NOVAL:
						print "writing NOVAL"
						pass
					else:
						self.allMemoryWritten=True
						## TODO: set all known mem locs to the union of src1[2]
								
			#### transfer function for STR ###########
			if instruction.mnemonic == 'str':
				if firstConst == True:
					gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1])))
				elif firstOP==True:
					gen.add((instruction.thirdOperand.value, src1[1], src1[2]))
				else:
					pass
						
						
			#### transfer function for SUB ###########
			if instruction.mnemonic == 'sub':
				if firstConst == True and secondConst == True:
					gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1-OP2])))
				elif firstConst == True and secondConst == False and secondConst==True:
					gen.add((instruction.thirdOperand.value,src2[1],self.constSetOP(OP1, src2[2], 'sub')))
				elif firstConst == False and secondConst==True and firstOP==True:
					gen.add((instruction.thirdOperand.value,src1[1],self.setConstOP(src1[2],OP2, 'sub')))
				elif firstOP==True and secondOP==True:
					if src1[1] == src2[1]:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'sub')))
					elif src1[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src2[1],self.setSetOP(src1[2],src2[2], 'sub')))
					elif src2[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'sub')))
					else:
						gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
				else:
					pass
						   
			
			#### transfer function for XOR ###########
			if instruction.mnemonic == 'xor':
				if firstConst == True and secondConst == True:
					gen.add((instruction.thirdOperand.value, NOVAL, frozenset([OP1^OP2])))
				elif firstConst == True and secondConst == False:
					gen.add((instruction.thirdOperand.value,src2[1],self.constSetOP(OP1, src2[2], 'xor')))
				elif firstConst == False and secondConst==True and firstOP==True:
					gen.add((instruction.thirdOperand.value,src1[1],self.setConstOP(src1[2],OP2, 'xor')))
				elif firstOP==True and secondOP==True:
					if src1[1] == src2[1]:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'xor')))
					elif src1[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src2[1],self.setSetOP(src1[2],src2[2], 'xor')))
					elif src2[1] == NOVAL:
						gen.add((instruction.thirdOperand.value,src1[1],self.setSetOP(src1[2],src2[2], 'xor')))
					else:
						gen.add((instruction.thirdOperand.value, str(instruction.getAddress()),frozenset([0])))
				else:
					pass
		#if instruction.getAddress()== 0x40101A00:				
		 #   print "gen", gen
		#out is defined as: gen U (inVal) Note: As we have already discarded Kill, we do not include it in this equation.
		if instruction.mnemonic != 'stm':# and len(gen)>0:
				
				for (r, ad, vl) in transformed_state.inVal:
					if instruction.thirdOperand.value == r:
						kill.add((r, ad, vl))
						#transformed_state.inVal.discard((r, ad, vl))
						break
					
		transformed_state.out.update(gen.union(transformed_state.inVal.difference(kill)))
		if self.allMemoryWritten ==True:
			for (rg, ad, vl) in Set().union(transformed_state.out):
				if rg in self.memoryLocVisited:
					transformed_state.out.discard((rg, ad, vl))
		#if instruction.getAddress() in (0x40101A00, 0x40101702):
		#print 'out', transformed_state.out
		### let us do a sort of widening by cutting the length of set of values (offsets)
		### We keep only the first MAX_NUM elements in the OUT:
		### Here we assume that memory locs are accessed "Nicely" i.e. no in between access
		transformed_state2.inVal.update(transformed_state.inVal)
		for (o,a,v) in transformed_state.out:
			transformed_state2.out.add((o,a,frozenset(list(sorted(v))[:MAX_NUM])))
		
		if len(transformed_state.out.symmetric_difference( currentState.out)) !=0:
			#print '\n$$$$$ elements added $$$$$\n'
			print 'Instruction ', instruction
			print "\n influencing ", sorted(influencingState.inVal, key=itemgetter(0)) #[(a,b,c) for (a,b,c) in influencingState.inVal if a == 'esp']#sorted(influencingState.inVal, key=itemgetter(0))
			#print '\n currentIn', sorted(currentState.inVal,key=itemgetter(0))
			print '\n currentOut', sorted(currentState.out,key=itemgetter(0))
			print '\n out', sorted(transformed_state.out,key=itemgetter(0))
			print '\n currentOUT ESP', [(a,b,c) for (a,b,c) in currentState.out if a == 'esp']
			print '\n OUT ESP', [(a,b,c) for (a,b,c) in transformed_state.out if a == 'esp']
			#print '\n difference A-B', transformed_state.out.difference(currentState.out)
			#print '\n difference B-A', currentState.out.difference(transformed_state.out)
   
			print '\n $$$$$$$$$$$$$$$$$$$$$$$$$$$$$'
		## added for debugging only ###
##		if len(gen) !=0:
##			for (o1,a1,v1) in gen:
##				for (o,a,v) in currentState.out:
##					if o1 == o and a == ANYVAL and a != a1:
##						print " changed inst", instruction, o
		else:
			print " \n$$$ exceptional inst \n"
			print 'Instruction ', instruction
			print "\n influencing ", sorted(influencingState.inVal, key=itemgetter(0))
			print '\n currentIn', sorted(currentState.inVal,key=itemgetter(0))
			print '\n currentOut', sorted(currentState.out,key=itemgetter(0))
			print '\n out', sorted(transformed_state.out,key=itemgetter(0))
			#print '\n difference A-B', transformed_state.out.difference(currentState.out)
			#print '\n difference B-A', currentState.out.difference(transformed_state.out)
				 

		return transformed_state2
	
	### functions to do setwise arithmetic operations..
	
	def constSetOP(self, const, myset, op):
		''' for the case where the first operand is immediate value.'''
		
		
		if op =='add':
			return frozenset([const+i for i in myset])
		if op == 'and':
			return frozenset([const & i for i in myset])
		if op == 'bsh':
			res=Set()
			for i in myset:
				if i <0:
					res.add(const>>abs(i))
				else:
					res.add(const<<abs(i))
			return frozenset(res)
		if op == 'div':
			return frozenset([const/i for i in myset])
		if op == 'mod':
			return frozenset([const%i for i in myset])
		if op == 'mul':
			return frozenset([const*i for i in myset])
		if op == 'or':
			return frozenset([const|i for i in myset])
		if op == 'sub':
			return frozenset([const-i for i in myset])
		if op == 'xor':
			return frozenset([const^i for i in myset])
		
		
	def setConstOP(self, myset, const, op):
		''' for the case where the second operand is immediate value.'''
		if op =='add':
			return frozenset([i+const for i in myset])
		if op == 'and':
			return frozenset([i & const for i in myset])
		if op == 'bsh':
			if const < 0:
				return frozenset([i>>abs(const) for i in myset])
			else:
				return frozenset([i<<abs(const) for i in myset])
		if op == 'div':
			return frozenset([i/const for i in myset])
		if op == 'mod':
			return frozenset([i%const for i in myset])
		if op == 'mul':
			return frozenset([i*const for i in myset])
		if op == 'or':
			return frozenset([i|const for i in myset])
		if op == 'sub':
			#print const, [g for g in myset]
			return frozenset([i-const for i in myset])
		if op == 'xor':
			return frozenset([i^const for i in myset])
		
		
	def setSetOP(self, myset1, myset2, op):
		''' for the case where both of the operands are sets.'''
		
		if op =='add':
			return frozenset([j+i for j in myset1 for i in myset2])
		if op == 'and':
			return frozenset([j & i for j in myset1 for i in myset2])
		if op == 'bsh':
			res=Set([j >> abs(i) for j in myset1 for i in myset2 if i<0])
			res.union(Set([ j << abs(i) for j in myset1 for i in myset2 if i>0]))
			return frozenset(res)
			
		if op == 'div':
			return frozenset([j/i for j in myset1 for i in myset2])
		if op == 'mod':
			return frozenset([j%i for j in myset1 for i in myset2])
		if op == 'mul':
			return frozenset([j*i for j in myset1 for i in myset2])
		if op == 'or':
			return frozenset([j|i for j in myset1 for i in myset2])
		if op == 'sub':
			return frozenset([j-i for j in myset1 for i in myset2])
		if op == 'xor':
			return frozenset([j^i for j in myset1 for i in myset2])
	
	def str2int(self, uni, adr):
		#reg= ''.join(str(ord(i)) for i in uni)
		
		return str(adr)+uni

		
def doAnalysis(instGraph): 

	# Generally the monotone framework works on graphs where each node represents
	# a REIL instruction. For this reason there is a helper function that creates
	# this instruction graph from a REIL graph.
	#instGraph = InstructionGraph.create(reilGraph.graph)
	#instGraph = InstructionGraph.create(reilGraph)

	# Define the lattice used by the monotone framework.
	lattice = SkeletonLattice()

	# Generate the initial state vector.
	startVector = generateStartVector(instGraph)

	# Define the transformations used by the monotone framework.
	transformationProvider = SkeletonTransformationProvider()

	# Reaching definitions starts at the beginning of a function and moves
	# downwards, so we use the default DownWalker class to move through
	# the graph.
	walker = DownWalker()

	# Use the monotone framework to find what registers are defined by the current function.
	solver = MonotoneSolver(instGraph, lattice, startVector, transformationProvider, walker)
	results = solver.solve()

	return results




####################### Dataflow methods ends here. ###########################
###############################################################################


def main():
	
	binNaviProxy = StandAlone.getPluginInterface()
	binNaviProxy.databaseManager.addDatabase("","com.mysql.jdbc.Driver","localhost","BINNAVI1","binnavi","binnavi",False,False)
	db=binNaviProxy.databaseManager.databases[0]
	db.connect()
	db.load()
	mods=db.getModules()
	
	### initiate dialogBox to setect the module that should be used.
	
	######################################################
	
	
	frame = JFrame('BinNavi Module Selector',layout=BorderLayout(),		
				defaultCloseOperation = JFrame.EXIT_ON_CLOSE,
				size = (1500, 800)
			)
	frame2 = JFrame('Function Selector',layout=BorderLayout(),		
				defaultCloseOperation = JFrame.EXIT_ON_CLOSE,
				size = (30, 30)
			)
			
	frame2.setFocusableWindowState(False)
	frame2.setFocusable(False)
	frame2.setAlwaysOnTop(False)
	#convert the module list into the string to be used in the TextBox.
	textTemp = map((lambda x,y:"[%d]%s"%(x,y)),range(len(mods)),mods) 
	textStr=''.join(textTemp)

	tx=JTextArea(textStr)
	tx.setLineWrap(True);
	tx.setWrapStyleWord(True);
	frame.add(tx,BorderLayout.PAGE_START)
	frame.visible = True
	modInd = JOptionPane.showInputDialog(frame2, "Enter the index of the chosen module", 
			 "Module selector");
	
	#Open the module returned by the index 
	bfname=mods[int(modInd)] # this modules correxponds to the chosen module
	bfname.load()
	funcViews=bfname.views
	#textTemp2 = ["[%d]%s"%(i,j) for i in range(len(funcViews)) for j in funcViews]
	textTemp2=map((lambda x,y:"[%d]%s"%(x,y.toString()[5:18])),range(len(funcViews)),funcViews)
	textStr1=''.join(textTemp2)
	## remove the older text from the frame view
	frame.remove(tx)
	frame.update(frame.getGraphics())
	frame.visible = False
	## create a new textArea with the string made from all the functions' name
	txStr=JTextArea(textStr1)
	#tx.setsrcollOffset(20)
	txStr.setLineWrap(True);
	txStr.setWrapStyleWord(True);
	frame.add(txStr,BorderLayout.PAGE_START)
	frame.update(frame.getGraphics())
	frame.visible = True
	funcInd = JOptionPane.showInputDialog(frame2, "Enter the index of the function", 
			 "Function selector");
   
 ######################################################
	
	
	bffunc=bfname.views[int(funcInd)] #this is the view of the buildfname function
	bffunc.load()
	
	frame2.setVisible(False)
	dispose(frame2)
	
	bfReil=bffunc.getReilCode() # this is the REIL code of the function
	bfReilGraph=bfReil.getGraph()
			
	instGraph = InstructionGraph.create(bfReilGraph)
	time.clock()
	results=doAnalysis(instGraph)
	totalTime=time.clock()
	#print "resultsLen", len([r for r in results])
			
	print "**** printing results *******\n"
	print "Total time:", totalTime, '\n'
	numNode=0
	for n in instGraph:
		numNode+=numNode
		
		nIn=list(results.getState(n).inVal)
		nIn.sort(key=itemgetter(0))
		nOut=list(results.getState(n).out)
		nOut.sort(key=itemgetter(0))
		print '@@ ',n.getInstruction(),'\n'
		print '\t In', nIn, '\n'
		print '\t OUT', nOut, '\n'
		print '\t memory: ',results.getState(n).memoryWritten, '\n'
	print "++++ Total instructions: %d +++++\n"%numNode		 
	#finally close the view of the function
	bffunc.close()
	#print bffunc.isLoaded()
	#junky=raw_input("function closed. enter any charater")
	


	print "Done! Closing the module selector window"
	frame.setVisible(False)
	dispose(frame)
	

if __name__ == '__main__':
	#sys.setrecursionlimit(600000)
	main()
