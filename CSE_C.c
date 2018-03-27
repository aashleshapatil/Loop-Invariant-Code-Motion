/*
 * File: CSE_C.c
 *
 * Description:
 *   This is where you implement the C version of project 4 support.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* LLVM Header Files */
#include "llvm-c/Core.h"
#include "dominance.h"
#include "transform.h"

/* Header file global to this project */
#include "cfg.h"
#include "CSE.h"
#include "worklist.h"

int CSE_Dead=0;
int CSE_Basic=0;
int CSE_Simplify=0;
int CSE_RLoad=0;
int CSE_Store2Load=0;
int CSE_RStore=0;
int globalflag=0;
static
int commonSubexpression(LLVMValueRef I, LLVMValueRef J) {
int i;
  /* return 1 if I and J are common subexpressions */
  /* check these things: */
  /*   - they have the same opcode */
  /*  - they have the same type */
  /*   - they have the same number of operands*/
  /*   - all operands are the same (pointer equivalence) LLVMValueRef */
  /* if any are false, return 0 */

  /* return 0 is always conservative, so by default return 0 */
  /* checking the opcodes*/
	if(LLVMGetInstructionOpcode (I)==LLVMGetInstructionOpcode(J))
		{
			/* checking the type */
		if(LLVMTypeOf(I)==LLVMTypeOf(J))	
			/* checking number of operands */
		 {
			if(LLVMGetNumOperands(I)==LLVMGetNumOperands(J))
			{
				/* checking if all the operands are same */
				for(i=0;i<LLVMGetNumOperands(I);i++)
				{
					if(LLVMGetOperand(I,i)!=LLVMGetOperand(J,i))
						return 0;
					
				}
				return 1;
			}
						
		 }

		}
  
  return 0;
}

static
int canHandle(LLVMValueRef I) 
{
/* Instructions that cannot be eliminated */
  return ! 
    (LLVMIsALoadInst(I) ||
      LLVMIsAStoreInst(I) ||
      LLVMIsATerminatorInst(I) ||
      LLVMIsACallInst(I) ||
      LLVMIsAPHINode(I) ||
      LLVMIsAAllocaInst(I) || 
     LLVMIsAFCmpInst(I) ||
     LLVMIsAVAArgInst(I)|| LLVMIsAExtractValueInst(I));
}

int isDead(LLVMValueRef I)
{
	 LLVMOpcode opcode = LLVMGetInstructionOpcode(I);

  /* Are there uses, if so not dead! */
  if (LLVMGetFirstUse(I)!=NULL)
    return 0;

  switch(opcode) {
  case LLVMRet:
  case LLVMBr:
  case LLVMSwitch:
  case LLVMIndirectBr:
  case LLVMInvoke: 	
  case LLVMUnreachable:
  case LLVMFence:
  case LLVMStore:
  case LLVMCall:
  case LLVMAtomicCmpXchg:
  case LLVMAtomicRMW:
  case LLVMResume:	
  case LLVMLandingPad: 
    return 0;

  case LLVMLoad: if(LLVMGetVolatile(I)) return 0;
  default:
    break;
  }

  // All conditions passed
  return 1;

}
// Perform CSE on I for BB and all dominator-tree children
static void DeadCodeElimination(LLVMModuleRef Module)
{
  LLVMValueRef F;
  int i;
  /* Iterate through the functions */
  for(F=LLVMGetFirstFunction(Module);
      F!=NULL;
      F=LLVMGetNextFunction(F))
    {
      /* Is this function defined? */
      if (LLVMCountBasicBlocks(F)) 
	{
	  /* insert all instructions of the function */
	  worklist_t worklist = worklist_for_function(F);
	  while(!worklist_empty(worklist)) {
		  /* pop each instruction to see if its dead */
	    LLVMValueRef I = worklist_pop(worklist);
	     if (isDead(I))
	      {	    
			  for(i=0; i<LLVMGetNumOperands(I); i++)
			  {
				LLVMValueRef J = LLVMGetOperand(I,i);
				if (LLVMIsAInstruction(J))
				/* Insert the operands in the list if they are instructions */
				  worklist_insert(worklist,J);
			  }
			  CSE_Dead++;
			  /* erase the instruction if dead */
			  LLVMInstructionEraseFromParent(I);
	      }
	  }	  
        worklist_destroy(worklist);
	}
    }

}
static
LLVMValueRef storeCSE(LLVMBasicBlockRef BB, LLVMValueRef I)
{
	LLVMValueRef J, temp,iter;
	int flag=0;
	J=LLVMGetNextInstruction(I);
	while(J!=NULL)
	{
		/* J is a load instruction, not volatile, having same address ,same type */
		if(LLVMIsALoadInst(J))
		{
			if(!LLVMGetVolatile(J))
			{
				if(LLVMGetOperand(J,0)==LLVMGetOperand(I,1))
				{
					if(LLVMTypeOf(J)==LLVMTypeOf(LLVMGetOperand(I,0)))
					{
						/* replace all uses of the load with the store’s data */
						LLVMReplaceAllUsesWith(J,LLVMGetOperand(I,0));
						temp=J;
						J=LLVMGetNextInstruction(J);
						/* remove the redundant instruction */
						LLVMInstructionEraseFromParent(temp);
						CSE_Store2Load++;
						continue;
					}
				}
			}
		}
		if(LLVMIsAStoreInst(J))
		{
			/* Inst is a store ,storing to the same address, not volatile, have the same address */
				if(LLVMGetOperand(J,1)==LLVMGetOperand(I,1))
				{
					if(LLVMTypeOf(LLVMGetOperand(J,0))==LLVMTypeOf(LLVMGetOperand(I,0)))
					{
						if(!LLVMGetVolatile(I))
						{
							iter=LLVMGetNextInstruction(I);
							flag=1;
							/* remove the redundant store */
							LLVMInstructionEraseFromParent(I);
							CSE_RStore++;
							break;
						}
					}
				}
			
		}
		/* move on to next instruction if any other load , store or call instruction is encountered */
		if(LLVMIsAStoreInst(J) || LLVMIsALoadInst(J)||LLVMIsACallInst(J))
		{
			break;
		}
		
		
		J=LLVMGetNextInstruction(J);
	}
	if(flag==0)
	{
		return(LLVMGetNextInstruction(I));
	}
	else
		return iter;
}
static
void LoadCSE(LLVMBasicBlockRef BB, LLVMValueRef I)
{
	LLVMValueRef J, temp;
	
	J=LLVMGetNextInstruction(I);
	while(J!=NULL)
	{	
		/* if the instruction is store, stop considering load, move on */
		if(LLVMIsAStoreInst(J))
		{	
			return;
		}
		/* the load should not be a volatile instruction */
		if(LLVMIsALoadInst(J) && !LLVMGetVolatile(J))
		{
		
			/* both have same addresses */
			if(LLVMGetOperand(J,0)==LLVMGetOperand(I,0))
			{
				/*both have same type */
				if(LLVMTypeOf(J)==LLVMTypeOf(I))
				{
					/* both will load the same data, so just replace the uses of later loads with the earlier load */
					LLVMReplaceAllUsesWith(J,I);
					temp=J;
					J=LLVMGetNextInstruction(J);
					/* erase the instruction , its redundant now */
					LLVMInstructionEraseFromParent(temp);
					CSE_RLoad++;
					continue;
				}
			}
		}
		J=LLVMGetNextInstruction(J);
	}
	return;
	
}
static
void processInst(LLVMBasicBlockRef BB, LLVMValueRef I) 
{
 LLVMBasicBlockRef DB; 
 LLVMValueRef J,M,temp;
 LLVMUseRef K;
 
int i;
  // do nothing if trivially dead
  // bale out if not an optimizable instruction
  if(!canHandle(I)) return;
 // DeadCodeElimination(BB,I);
  // CSE w.r.t. to I on BB
 
	  if(globalflag==0)
	  {
		  J=LLVMGetNextInstruction(I);
	  }
	  else
	  {
	  J=LLVMGetFirstInstruction(BB);
	  }
       while(J!= NULL) 
	   {
		   
		   if(commonSubexpression(I,J))
				{
					/* both imstructions are same giving same output. so replace the uses of latter instruction with earlier instruction */
						LLVMReplaceAllUsesWith (J , I);
						temp=J;
						J=LLVMGetNextInstruction(J);
						/* delete the redundant instruction */
						LLVMInstructionEraseFromParent(temp);
						CSE_Basic++;
						 continue;
				}
			J=LLVMGetNextInstruction(J);
   }
   /* iterate the through dominator-tree */
   DB = LLVMFirstDomChild(BB); 
   while (DB) {
	    globalflag=1;
	    processInst(DB,I);
  DB = LLVMNextDomChild(BB,DB);  // get next child of BB
   }



return;
}


static
void FunctionCSE(LLVMValueRef Function) 
{
//printf("entered functioncse");

  LLVMBasicBlockRef BB;
  LLVMValueRef I,S,temp,W;
  int i;
  worklist_t worklist = worklist_create();
  for(BB=LLVMGetFirstBasicBlock(Function);BB!=NULL;BB=LLVMGetNextBasicBlock(BB))
  	{
	 
		 I=LLVMGetFirstInstruction(BB);
	  
       while(I!= NULL) 
		{
		
			globalflag=0;
			/* simplify the instruction. Returns NULL if not simplified */
			S=InstructionSimplify(I);
			if(S!=NULL)
			{
				CSE_Simplify++;
				/*replace all uses of the instruction with the simplified form */
				LLVMReplaceAllUsesWith(I,S);
				temp=I;
				I=LLVMGetNextInstruction(I);
				 LLVMInstructionEraseFromParent(temp);
				 continue;
			}
			if (isDead(I))
			{
				worklist_insert(worklist,I);
				I=LLVMGetNextInstruction(I);
				continue;
			}
		    

			 processInst(BB,I);
			 
			 if(LLVMIsALoadInst(I))
			 {
				
				LoadCSE(BB,I);
			
				
			 }
			 if(LLVMIsAStoreInst(I))
			 {
				I=storeCSE(BB,I);
				continue;
				
			 }
			 
			I=LLVMGetNextInstruction(I);
			
		
		}
	}
	while(!worklist_empty(worklist)) {
	    W = worklist_pop(worklist);
	     if (isDead(W))
	      {
		
	   
		for(i=0; i<LLVMGetNumOperands(W); i++)
		  {
		    LLVMValueRef J = LLVMGetOperand(W,i);
              // Add to worklist only if J is an instruction
              // Note, J still has one use (in I) so the isDead
              // would return false, so we’d better not check that.
              // This forces us to check in the if statement above.
		    if (LLVMIsAInstruction(J))
		      worklist_insert(worklist,J);
		  }
		CSE_Dead++;
		LLVMInstructionEraseFromParent(W);
	      }
	  }	  
	
    worklist_destroy(worklist);

  
return;
}


void LLVMCommonSubexpressionElimination(LLVMModuleRef Module)
{


  // Loop over all functions
//  DeadCodeElimination(Module);
  LLVMValueRef Function;
  for (Function=LLVMGetFirstFunction(Module);Function!=NULL;
       Function=LLVMGetNextFunction(Function))
    {
      FunctionCSE(Function);
    }
	 printf("\nCSE_BASIC %d , \n CSE_Simplify %d,\n CSE_RLoad %d ,\nCSE_Store2Load  %d , \nCSE_RStore %d ,\n CSE_Dead %d",CSE_Basic,CSE_Simplify,CSE_RLoad,CSE_Store2Load, CSE_RStore,CSE_Dead);
return;

  // print out summary of results
}

