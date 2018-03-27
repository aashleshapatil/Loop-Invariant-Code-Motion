 /*
 * File: summary.c
 *
 * Description:
 *   This is where you implement your project 3 support.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* LLVM Header Files */
#include "llvm-c/Core.h"
#include "dominance.h"
#include "valmap.h"

/* Header file global to this project */
#include "summary.h"

typedef struct Stats_def {
  int functions;
  int globals;
  int bbs;

  int insns;
  int insns_nearby_dep;
  
  int allocas;

  int loads;
  int loads_alloca;
  int loads_globals;

  int stores;
  int stores_alloca;
  int stores_globals;
  
  int conditional_branches;
  int calls;

  int gep;
  int gep_load;
  int gep_alloca;
  int gep_globals;
  int gep_gep;

  int loops; //approximated by backedges
  int floats;
} Stats;

void pretty_print_stats(FILE *f, Stats s, int spaces)
{
  char spc[128];
  int i;

  // insert spaces before each line
  for(i=0; i<spaces; i++)
    spc[i] = ' ';
  spc[i] = '\0';
    
  fprintf(f,"%sFunctions.......................%d\n",spc,s.functions);
  fprintf(f,"%sGlobal Vars.....................%d\n",spc,s.globals);
  fprintf(f,"%sBasic Blocks....................%d\n",spc,s.bbs);
  fprintf(f,"%sInstructions....................%d\n",spc,s.insns);
  fprintf(f,"%sInstructions - Nearby Dep.......%d\n",spc,s.insns_nearby_dep);

  fprintf(f,"%sInstructions - Cond. Branches...%d\n",spc,s.conditional_branches);
  fprintf(f,"%sInstructions - Calls............%d\n",spc,s.calls);

  fprintf(f,"%sInstructions - Allocas..........%d\n",spc,s.allocas);
  fprintf(f,"%sInstructions - Loads............%d\n",spc,s.loads);
  fprintf(f,"%sInstructions - Loads (alloca)...%d\n",spc,s.loads_alloca);
  fprintf(f,"%sInstructions - Loads (globals)..%d\n",spc,s.loads_globals);


  fprintf(f,"%sInstructions - Stores...........%d\n",spc,s.stores);
  fprintf(f,"%sInstructions - Stores (alloca)..%d\n",spc,s.stores_alloca);
  fprintf(f,"%sInstructions - Stores (globals).%d\n",spc,s.stores_globals);


  fprintf(f,"%sInstructions - gep..............%d\n",spc,s.gep);
  fprintf(f,"%sInstructions - gep (load).......%d\n",spc,s.gep_load);
  fprintf(f,"%sInstructions - gep (alloca).....%d\n",spc,s.gep_alloca);
  fprintf(f,"%sInstructions - gep (globals)....%d\n",spc,s.gep_globals);
  fprintf(f,"%sInstructions - gep (gep)........%d\n",spc,s.gep_gep);

  fprintf(f,"%sInstructions - Other............%d\n",spc,
	  s.insns-s.conditional_branches-s.loads-s.stores-s.gep-s.calls);
  fprintf(f,"%sLoops...........................%d\n",spc,s.loops);
  fprintf(f,"%sFloats..........................%d\n",spc,s.floats);
}

void print_csv_file(const char *filename, Stats s, const char *id)
{
  FILE *f = fopen(filename,"w");
  fprintf(f,"id,%s\n",id);
  fprintf(f,"functions,%d\n",s.functions);
  fprintf(f,"globals,%d\n",s.globals);
  fprintf(f,"bbs,%d\n",s.bbs);
  fprintf(f,"insns,%d\n",s.insns);
  fprintf(f,"insns_nearby_dep,%d\n",s.insns_nearby_dep);
  fprintf(f,"allocas,%d\n",s.allocas);
  fprintf(f,"branches,%d\n",s.conditional_branches);
  fprintf(f,"calls,%d\n",s.calls);
  fprintf(f,"loads,%d\n",s.loads);
  fprintf(f,"loads_alloca,%d\n",s.loads_alloca);
  fprintf(f,"loads_globals,%d\n",s.loads_globals);
  fprintf(f,"stores,%d\n",s.stores);
  fprintf(f,"stores_alloca,%d\n",s.stores_alloca);
  fprintf(f,"stores_global,%d\n",s.stores_globals);
  fprintf(f,"gep,%d\n",s.gep);
  fprintf(f,"gep_alloca,%d\n",s.gep_load);
  fprintf(f,"gep_alloca,%d\n",s.gep_alloca);
  fprintf(f,"gep_globals,%d\n",s.gep_globals);
  fprintf(f,"gep_gep,%d\n",s.gep_gep);
  fprintf(f,"loops,%d\n",s.loops);
  fprintf(f,"floats,%d\n",s.floats);
  fclose(f);
}

Stats MyStats;

void
Summarize(LLVMModuleRef Module, const char *id, const char* filename)
{
	
	int i=0;
	int count1=0;
	int count2=0;
	valmap_t map_bb= valmap_create();
	LLVMValueRef  global, ref_bb,ref_inst;
	for(global=LLVMGetFirstGlobal(Module); global!=NULL; global=LLVMGetNextGlobal(global))
	{
		LLVMValueRef isini= LLVMGetInitializer(global);
		if(isini!=NULL)
		{	
			MyStats.globals++;
		}
	}
	//stat.allocas=0;
	LLVMValueRef  fn_iter; // iterator 
for (fn_iter = LLVMGetFirstFunction(Module); fn_iter!=NULL; 
    fn_iter = LLVMGetNextFunction(fn_iter))
{

	
	ref_bb=LLVMGetFirstBasicBlock(fn_iter);
	if(ref_bb!=NULL)
	{
		MyStats.functions++;
	}
	// fn_iter points to a function
    LLVMBasicBlockRef bb_iter; /* points to each basic block
                             one at a time */
    for (bb_iter = LLVMGetFirstBasicBlock(fn_iter);
		bb_iter != NULL; bb_iter = LLVMGetNextBasicBlock(bb_iter))
    {
		
		
		LLVMValueRef last_inst=LLVMGetBasicBlockTerminator(bb_iter);
		LLVMOpcode loop=LLVMGetInstructionOpcode(last_inst);
		LLVMBasicBlockRef loop_one_bb,loop_two_bb,loop_one_db_bb;
		if(loop==LLVMBr)
			{
				LLVMValueRef loop_zero=LLVMGetOperand(last_inst,0);
				if(!LLVMValueIsBasicBlock(loop_zero))
				{
					LLVMValueRef loop_one=LLVMGetOperand(last_inst,1);
					
					loop_one_bb= LLVMValueAsBasicBlock(loop_one);	
					
					LLVMValueRef loop_two=LLVMGetOperand(last_inst,2);
					
					loop_two_bb= LLVMValueAsBasicBlock(loop_two);	
					
					
					LLVMBool isdom_one=LLVMDominates(fn_iter,loop_one_bb,bb_iter);
					LLVMBool isdom_two=LLVMDominates(fn_iter,loop_two_bb,bb_iter);
					if(isdom_one)
					{
						LLVMBool loop_check=valmap_check(map_bb,loop_one);
						if(!loop_check)
						{
							valmap_insert(map_bb,loop_one, id);
							MyStats.loops++;
						}
						
					}
					else if(isdom_two)
					{
						LLVMBool loop_check1=valmap_check(map_bb,loop_two);
						if(!loop_check1)
						{
							valmap_insert(map_bb,loop_two, id);
							MyStats.loops++;
						}

					}
					
					
				}
				else
				{
					LLVMValueRef loop_one_db=LLVMGetOperand(last_inst,0);
					if(LLVMValueIsBasicBlock(loop_one_db))
					{
						loop_one_db_bb= LLVMValueAsBasicBlock(loop_one_db);	
					}
				    LLVMBool isdom_one_db=LLVMDominates(fn_iter,loop_one_db_bb,bb_iter);
					if(isdom_one_db)
					{
						LLVMBool loop_check0=valmap_check(map_bb,loop_one_db);
						if(!loop_check0)
						{
							valmap_insert(map_bb,loop_one_db, id);
							MyStats.loops++;
						}
						
					}
				}
				
			}
		MyStats.bbs++;  
		valmap_t map= valmap_create();
       LLVMValueRef inst_iter; /* points to each instruction */
       for(inst_iter = LLVMGetFirstInstruction(bb_iter);
           inst_iter != NULL;inst_iter = LLVMGetNextInstruction(inst_iter)) 
       {
		    MyStats.insns++;
			valmap_insert(map,inst_iter, id);
			
			for(i=0;i<LLVMGetNumOperands (inst_iter);i++)// to find number of floats
			{
				LLVMValueRef float_operand=LLVMGetOperand(inst_iter,i);
				if(	LLVMGetTypeKind (LLVMTypeOf(float_operand))== LLVMHalfTypeKind || LLVMGetTypeKind (LLVMTypeOf(float_operand))==LLVMFloatTypeKind || LLVMGetTypeKind (LLVMTypeOf(float_operand))== LLVMDoubleTypeKind ||LLVMGetTypeKind (LLVMTypeOf(float_operand))== LLVMX86_FP80TypeKind||LLVMGetTypeKind (LLVMTypeOf(float_operand))== LLVMFP128TypeKind || LLVMGetTypeKind (LLVMTypeOf(float_operand))==LLVMPPC_FP128TypeKind )
				{
					MyStats.floats++;
					break;
				}
			}
			for(i=0;i<LLVMGetNumOperands (inst_iter);i++)
			{
				LLVMValueRef dep_operand=LLVMGetOperand(inst_iter,i);
				LLVMBool ins_dep_check=valmap_check(map, dep_operand);
				if(ins_dep_check)
				{
					MyStats.insns_nearby_dep++;
					break;
				}
			}
            // get the basic block of this instruction
            LLVMBasicBlockRef ref =  LLVMGetInstructionParent(inst_iter);
			LLVMOpcode opcode=LLVMGetInstructionOpcode(inst_iter);
			LLVMOpcode op_eg_alloca=LLVMAlloca; 
			LLVMBool global_true = 1;
		//	LLVMDumpValue(global_true);
			if(opcode==op_eg_alloca)
			{
				
				MyStats.allocas++;
			}
			if(opcode==LLVMLoad)
			{
				
				MyStats.loads++;
				LLVMValueRef load_alloca=LLVMGetOperand	(inst_iter,0);
				LLVMOpcode load_op_alloca=LLVMGetInstructionOpcode(load_alloca);
				if(load_op_alloca==LLVMAlloca)
				{
					MyStats.loads_alloca++;
				}
				LLVMValueRef load_globals=LLVMGetOperand(inst_iter,0);
				if(LLVMIsAGlobalVariable(load_globals))
				{
					MyStats.loads_globals++;
				}
			}	
			if(opcode==LLVMStore)
			{
				
				MyStats.stores++;
				LLVMValueRef store_alloca=LLVMGetOperand(inst_iter,1);
				LLVMOpcode store_op_alloca=LLVMGetInstructionOpcode(store_alloca);
				if(store_op_alloca==LLVMAlloca)
				{
					MyStats.stores_alloca++;
				}
				LLVMValueRef store_globals=LLVMGetOperand(inst_iter,1);
				if(LLVMIsAGlobalVariable(store_globals))
				{
					MyStats.stores_globals++;
				}
			}
			if(opcode==LLVMCall)
			{
				
				MyStats.calls++;
			}	
			if(opcode==LLVMGetElementPtr )
			{
				
				MyStats.gep++;
				LLVMValueRef gep_alloca=LLVMGetOperand	(inst_iter,0);
				LLVMOpcode gep_op_alloca=LLVMGetInstructionOpcode(gep_alloca);
				if(gep_op_alloca==LLVMAlloca)
				{
					MyStats.gep_alloca++;
				}
				LLVMValueRef gep_load=LLVMGetOperand(inst_iter,0);
				LLVMOpcode gep_op_load=LLVMGetInstructionOpcode(gep_load);
				if(gep_op_load==LLVMLoad)
				{
					MyStats.gep_load++;
				}
				LLVMValueRef gep_gep=LLVMGetOperand(inst_iter,0);
				LLVMOpcode gep_op_gep=LLVMGetInstructionOpcode(gep_gep);
				if(gep_op_gep==LLVMGetElementPtr)
				{
					MyStats.gep_gep++;
				}
				LLVMValueRef gep_globals=LLVMGetOperand(inst_iter,0);
				if(LLVMIsAGlobalVariable(gep_globals))
				{
					MyStats.gep_globals++;
				}
			}
			if(opcode==LLVMBr)
			{
				LLVMValueRef br_bb=LLVMGetOperand(inst_iter,0);
				if(!LLVMValueIsBasicBlock(br_bb))
				{
					MyStats.conditional_branches++;
				}
				
			}
			
       }
	   valmap_destroy( map);
	   
    }
	
}
  valmap_destroy( map_bb);
  pretty_print_stats(stdout,MyStats,0);
 print_csv_file(filename,MyStats,id);
}

