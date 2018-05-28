/*
 * File: LICM_C.c
 *
 * Description:
 *   Stub for LICM in C. This is where you implement your LICM pass.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* LLVM Header Files */
#include "llvm-c/Core.h"
#include "dominance.h"

/* Header file global to this project */
#include "cfg.h"
#include "loop.h"
#include "worklist.h"
#include "valmap.h"

static worklist_t list;

static LLVMBuilderRef Builder=NULL;

unsigned int LICM_Basic=0;
unsigned int LICM_NoPreheader=0;
unsigned int LICM_AfterLoop=0;
unsigned int LICM_LoadHoist=0;
unsigned int LICM_LoadSink=0;
unsigned int LICM_StoreSink=0;
unsigned int LICM_BadCall=0;
unsigned int LICM_BadStore=0;
int changes=0;
int find_use_in_loop(Loop,I)
{
	/* This function is to find use of instruction I in the loop */
  worklist_t wlist;
  LLVMBasicBlockRef bb;
  LLVMValueRef J;
  int num,i;
  /* put all the basic block in loop in the list */
   wlist = LLVMGetBlocksInLoop(Loop);
   /* iterate through the instructions to find a operand same as I */
   while(!worklist_empty(wlist))
   {
     bb = LLVMValueAsBasicBlock(worklist_pop(wlist));
     for(J=LLVMGetFirstInstruction(bb);J!=NULL;J=LLVMGetNextInstruction(J))
     {
       for(i=0;i<LLVMGetNumOperands(J);i++)
       {
         if(LLVMGetOperand(J,i)==I)
         {
           return 0;
           
         }
       }
     }
     
   }
   return 1;
}
LLVMValueRef sink(LLVMValueRef I,LLVMLoopRef L)
{
  worklist_t wlist_exit;
  wlist_exit= LLVMGetExitBlocks(L);
  LLVMBasicBlockRef bb,true_block,false_block,loop_block,outer_block,new_bb;
  LLVMValueRef last,cond,clone,temp,iter;
  int true_block_loop=0;
   while(!worklist_empty(wlist_exit))
    {
        bb = LLVMValueAsBasicBlock(worklist_pop(wlist_exit));
        for(iter=LLVMGetFirstPredecessor(bb);iter!=NULL;iter=LLVMGetNextPredecessor(bb, iter))
        {
          if(LLVMLoopContainsBasicBlock(L, iter))
          {
			  last=LLVMGetBasicBlockTerminator(iter);
			  /*check if conditional or non conditional branch*/
			  if(!LLVMValueIsBasicBlock(LLVMGetOperand(last,0)))
			  {
					last=LLVMGetBasicBlockTerminator(iter);
					cond=LLVMGetOperand(last,0);
					true_block =LLVMValueAsBasicBlock(LLVMGetOperand(last,1));
					false_block =LLVMValueAsBasicBlock(LLVMGetOperand(last,2));
					new_bb=LLVMAppendBasicBlock	(	LLVMGetBasicBlockParent(iter),"new_block");
					LLVMPositionBuilderBefore(Builder,last);
					/*if branches to the block when condition is true*/
					if(true_block==bb)
					{
						 LLVMValueRef br= LLVMBuildCondBr(Builder,cond,new_bb,false_block);
						 LLVMInstructionEraseFromParent	(last);
						 LLVMPositionBuilderAtEnd	(Builder,new_bb);
						 clone = LLVMCloneInstruction(I);
						 LLVMInsertIntoBuilder(Builder,clone);
						 LLVMValueRef directbr= LLVMBuildBr(Builder,bb);
					}
					if(false_block==bb)
					{
						LLVMValueRef br= LLVMBuildCondBr(Builder,cond,true_block,new_bb);
						LLVMInstructionEraseFromParent(last);
						LLVMPositionBuilderAtEnd(Builder,new_bb);
						clone = LLVMCloneInstruction(I);
						LLVMInsertIntoBuilder(Builder,clone);
						LLVMValueRef directbr= LLVMBuildBr(Builder,bb);
					}
			  }
			  else
			  {
			   
					LLVMBasicBlockRef uncond=LLVMValueAsBasicBlock(LLVMGetOperand(last,1));
					if(uncond==bb)
					{
						new_bb=LLVMAppendBasicBlock	(	LLVMGetBasicBlockParent(iter),"new_block");
						LLVMPositionBuilderBefore(Builder,last);
						LLVMValueRef directbr= LLVMBuildBr(Builder,new_bb);
						LLVMInstructionEraseFromParent	(last);
						LLVMPositionBuilderAtEnd	(Builder,new_bb);
						clone = LLVMCloneInstruction(I);
						LLVMReplaceAllUsesWith(I,clone);
						LLVMInsertIntoBuilder(Builder,clone);
						LLVMValueRef a= LLVMBuildBr(Builder,bb);
					}
				
			  }
  					
			}
        }
    }
             LLVMReplaceAllUsesWith(I,clone);
             temp=I;
             I=LLVMGetNextInstruction(I);
             LLVMInstructionEraseFromParent	(temp); 
             return I;
  
}
void LICM(LLVMValueRef funs)
{
  LLVMLoopInfoRef LI ;
  LLVMValueRef PH,I,addr,clone,temp,temp1,last,use_instr;
  LLVMBasicBlockRef bb;
  LLVMLoopRef Loop;
  LLVMOpcode branch;
  LLVMUseRef use;
  int i,num,use_in_loop=0;
  worklist_t wlist = worklist_create();
  
  LI = LLVMCreateLoopInfoRef(funs);
  /* Iterate through the loops in the function */
  for(Loop=LLVMGetFirstLoop(LI);
     Loop!=NULL;
     Loop=LLVMGetNextLoop(LI,Loop))
    {
     PH = LLVMGetPreheader(Loop);
     if( PH==NULL)
      {
	      LICM_NoPreheader++;
        continue ;
      }
	  /* put all the basic block involved in the particular loop in the list */
      wlist = LLVMGetBlocksInLoop(Loop);
      while(!worklist_empty(wlist))
       {
			bb = LLVMValueAsBasicBlock(worklist_pop(wlist));
			I=LLVMGetFirstInstruction(bb);
		    while(I!=NULL)
			{
			  
			   temp1=LLVMGetNextInstruction(I);
			   /* check if the instruction is loop invariant. If it is , then assume the instruction is blown away */
				if(LLVMMakeLoopInvariant(Loop,I))
				{
				  LICM_Basic++;
				  I=temp1;
				  continue;
			  
				}
		   
				else if (LLVMIsALoadInst(I))
				{                   
					
					addr = LLVMGetOperand(I,0);
					/* check if the load instruction can be moved out of the loop */
					if(canMoveOutOfLoop_load(Loop,I,addr))
					{
					   if(find_use_in_loop(Loop,I))
					   {
						   /*if no use then sink!*/
						LICM_LoadSink++;
						I=sink(I,Loop);
					   
					   continue;
					   }
					}
					
					if(canMoveOutOfLoop_hoist(Loop,I,addr))
					{
						clone = LLVMCloneInstruction(I);
						last=LLVMGetLastInstruction(PH);
						LLVMPositionBuilderBefore(Builder,last);
						LLVMInsertIntoBuilder(Builder,clone);
						LLVMReplaceAllUsesWith(I,clone);
						temp=I;
						I=LLVMGetNextInstruction(I);
						LLVMInstructionEraseFromParent	(temp); 
						LICM_LoadHoist++;
						continue;
					}
				}
				else if(LLVMIsAStoreInst(I))
				{
					addr = LLVMGetOperand(I,1);
					if(canMoveOutOfLoop_store(Loop,I,addr))
					{
						I=sink(I,Loop);
						LICM_StoreSink++;
						continue;
					}
				}
				I=LLVMGetNextInstruction(I);
			}     
       }
   }
  return;
}

int canMoveOutOfLoop_hoist(LLVMLoopRef L, LLVMValueRef I, LLVMValueRef addr)
{
    worklist_t wlist1 = worklist_create();
    worklist_t wlist2 = worklist_create();
    worklist_t wlist_exit = worklist_create();
    LLVMValueRef J;
    wlist1 = LLVMGetBlocksInLoop(L);
    LLVMOpcode opcode=LLVMGetInstructionOpcode(I);
    wlist_exit= LLVMGetExitBlocks(L);
    int dom=0;
    while(!worklist_empty(wlist1))
    {
        LLVMBasicBlockRef bb = LLVMValueAsBasicBlock(worklist_pop(wlist1));
        for(J=LLVMGetFirstInstruction(bb);J!=NULL;J=LLVMGetNextInstruction(J))
        {
			/* Load cannot be moved out if there is a call inst in the loop */
           if(LLVMIsACallInst(J))
           {
				LICM_BadCall++;
				return 0;
           }
		   /* If there is a store with same address in the loop, the load cannot be moved out*/
           if(LLVMIsAStoreInst(J))
           {
				LLVMValueRef store_address=LLVMGetOperand(J,1);
				if(store_address==addr)
				{
					LICM_BadStore++;
				   return 0;
				 
				}
             
           }
        }
          
    } 
       
   if(LLVMIsAConstant(addr))
	{
		/*address is constant and no stores to that address */
		return 1;
	}
	if(LLVMLoopContainsInst(L,addr))
	{
		/* address of load is defined in the loop*/
		return 0;
	}
	  if(opcode==LLVMAlloca)
		 {
		   if(!LLVMLoopContainsInst(L,addr))
		   {
			   /* address is an alloca and not defined in the loop */
			 LICM_BadStore++;
			 return 1;
		   }
		 }
	  
		
   while(!worklist_empty(wlist_exit))
  {
	LLVMBasicBlockRef be=LLVMValueAsBasicBlock(worklist_pop(wlist_exit));
	if(!LLVMDominates(LLVMGetBasicBlockParent(LLVMGetInstructionParent(I)),LLVMGetInstructionParent(I),be))
	{
		/* I doesnot dominate the loop exits*/
	 return 0;
	}
  }
  while(!worklist_empty(wlist1))
   {
	 LLVMBasicBlockRef bb = LLVMValueAsBasicBlock(worklist_pop(wlist1));
	 for(J=LLVMGetFirstInstruction(bb);J!=NULL;J=LLVMGetNextInstruction(J))
	 {
		 /*there are no stores to any address in Loop .addr is not defined inside the loop ,I dominates Loop’s exit*/
	   if(LLVMIsAStoreInst(J))
	   {
		 LICM_BadStore++;
		 return 0;
	   }
	 }
   }
       
}
int canMoveOutOfLoop_store(LLVMLoopRef L, LLVMValueRef I, LLVMValueRef addr)
{
     worklist_t wlist1 = worklist_create();
     worklist_t wlist2 = worklist_create();
     worklist_t wlist_exit = worklist_create();
     LLVMValueRef J;
     wlist1 = LLVMGetBlocksInLoop(L);
     LLVMOpcode opcode=LLVMGetInstructionOpcode(I);
     wlist_exit= LLVMGetExitBlocks(L);
      while(!worklist_empty(wlist_exit))
      {
        LLVMBasicBlockRef be=LLVMValueAsBasicBlock(worklist_pop(wlist_exit));
        if(!LLVMDominates(LLVMGetBasicBlockParent(LLVMGetInstructionParent(I)),LLVMGetInstructionParent(I),be))
        {
         return 0;
        } 
      }
      
       if(LLVMLoopContainsInst(L,addr))
         {
         return 0;
         }
     while(!worklist_empty(wlist1))
       {
         LLVMBasicBlockRef bb = LLVMValueAsBasicBlock(worklist_pop(wlist1));
         for(J=LLVMGetFirstInstruction(bb);J!=NULL;J=LLVMGetNextInstruction(J))
         {
            if(LLVMIsACallInst(J))
           {
            
             return 0;
           }
           if(LLVMIsALoadInst(J))
           {
             LLVMValueRef load_address=LLVMGetOperand(J,0);
             if(load_address==addr)
             {
               return 0;
             
             }
             
           }
         }  
       } 
        if(LLVMIsAConstant(addr))
             {
             
               return 1;
             }
          if(opcode==LLVMAlloca)
             {
               if(!LLVMLoopContainsInst(L,addr))
               {
                
                 return 1;
               }
             }
      while(!worklist_empty(wlist1))
       {
         LLVMBasicBlockRef bb = LLVMValueAsBasicBlock(worklist_pop(wlist1));
         for(J=LLVMGetFirstInstruction(bb);J!=NULL;J=LLVMGetNextInstruction(J))
         {
           if(LLVMIsALoadInst(J))
           {
             return 0;
           }
         }
       }
}
/*if (addr is a constant and there are no stores to addr in L):
		return true
	if (addr is an AllocaInst and no stores to addr in L and
      AllocaInst is not inside the loop):
		return true
if (there are no stores to any address in L && addr is not defined inside the loop && I dominates L’s exit):
	return true
	else
return false
*/
int canMoveOutOfLoop_load(LLVMLoopRef L, LLVMValueRef I, LLVMValueRef addr)
{
  worklist_t wlist1 = worklist_create();
  worklist_t wlist2 = worklist_create();
  worklist_t wlist_exit = worklist_create();
  LLVMValueRef J;
  wlist1 = LLVMGetBlocksInLoop(L);
   LLVMOpcode opcode=LLVMGetInstructionOpcode(I);
    wlist_exit= LLVMGetExitBlocks(L);
      while(!worklist_empty(wlist_exit))
      {
		  /*check if the load dominates all the exits*/
        LLVMBasicBlockRef be=LLVMValueAsBasicBlock(worklist_pop(wlist_exit));
        if(!LLVMDominates(LLVMGetBasicBlockParent(LLVMGetInstructionParent(I)),LLVMGetInstructionParent(I),be))
        {
         return 0;
        } 
      }
      /*check if the address is defined in the loop*/
       if(LLVMLoopContainsInst(L,addr))
         {
         return 0;
         }
     while(!worklist_empty(wlist1))
       {
         LLVMBasicBlockRef bb = LLVMValueAsBasicBlock(worklist_pop(wlist1));
         for(J=LLVMGetFirstInstruction(bb);J!=NULL;J=LLVMGetNextInstruction(J))
         {
			 /*check if there is a call instruction in the loop*/
            if(LLVMIsACallInst(J))
           {
            
             return 0;
           }
           if(LLVMIsAStoreInst(J))
           {
             LLVMValueRef store_address=LLVMGetOperand(J,1);
			 /*check if there is a store to same address*/
             if(store_address==addr)
             {
               return 0;
             
             }
             
           }
         }  
       } 
	   /*check if address is constant*/
        if(LLVMIsAConstant(addr))
             {
             
               return 1;
             }
			 /*check if the address is an alloca and if it is defined in the loop*/
          if(opcode==LLVMAlloca)
             {
               if(!LLVMLoopContainsInst(L,addr))
               {
                
                 return 1;
               }
             }
			 /*check if there is any store instruction in the loop*/
      while(!worklist_empty(wlist1))
       {
         LLVMBasicBlockRef bb = LLVMValueAsBasicBlock(worklist_pop(wlist1));
         for(J=LLVMGetFirstInstruction(bb);J!=NULL;J=LLVMGetNextInstruction(J))
         {
           if(LLVMIsAStoreInst(J))
           {
             return 0;
           }
         }
       }
}
void LoopInvariantCodeMotion_C(LLVMModuleRef Module)
{
  LLVMValueRef funs;

  Builder = LLVMCreateBuilder();

  list = worklist_create();

  for(funs=LLVMGetFirstFunction(Module);
      funs!=NULL;
      funs=LLVMGetNextFunction(funs))
    { 
     if (LLVMCountBasicBlocks(funs))
     { 
     
      LICM(funs);
      
      
      }
      
    }

  LLVMDisposeBuilder(Builder);
  Builder = NULL;

 
  printf("LICM_Basic      =%d\n",LICM_Basic);
  printf("LICM_NoPreheader=%d\n",LICM_NoPreheader);
  printf("LICM_LoadHoist  =%d\n",LICM_LoadHoist);
  printf("LICM_LoadSink   =%d\n",LICM_LoadSink);
  printf("LICM_StoreSink  =%d\n",LICM_StoreSink);
  printf("LICM_BadCall    =%d\n",LICM_BadCall);
  printf("LICM_BadStore   =%d\n",LICM_BadStore);
}




