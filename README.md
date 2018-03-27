# Loop-Invariant-Code-Motion

Objectives
•	Implement an LLVM library for loop invariant code motion.
•	Gain experience with the Loop and LoopInfo API in LLVM.
•	Learn best techniques for modifying the IR  to optimize a program.
•	Examine technical requirements of Loop Invariant Code Motion that stem from a detailed implementation in LLVM.
•	Examine the effectiveness of your implementation of LICM both on its own and in the presence of other optimizations.

Specification
	In this project, you will implement Loop Invariant Code Motion (LICM) using the algorithm described in the lecture notes and then evaluate its effectiveness on wolfbench. 
Your code must do the following:
•	LICM_Basic: move any non-memory instruction that is loop invariant and used within the loop to the preheader.  You must iterate until all such instructions are moved.
•	LICM_LoadHoist: move loop invariant loads that are used within the loop to the pre-header. You must iterate until all such instructions are moved. Note, some non-loads may become invariant, and you must handle them too.
•	LICM_StoreSink: remove loop invariant stores to after the loop. You must iterate until all such instructions are removed. Note, some loads may become invariant after removal, and you must handle them too.
•	LICM_LoadSink: move loop invariant loads that are not used within the loop to the loop exit. You must iterate until all such instructions are removed. Note, some non-loads may become invariant, and you must handle them too.

Your implementation should also count the following: 
1.	LICM_Basic: total number of instructions moved out of the loop to the preheader.
2.	LICM_LoadHoist: total number of loads moved to preheader.
3.	LICM_StoreSink: total number of stores moved after the loop.
4.	LICM_LoadSink: total number of loads moved after the loop.
5.	LICM_NoPreheader: number of loops with no pre-header.
6.	LICM_BadStore: number of times a store prevents optimization of a load. This should be incremented only once per load. 
7.	LICM_BadCalls: (this is a hint!) number of times a call instruction prevents optimization of a load. This should be incremented only once per load. 
a.	In your report be sure to specify what relationship may exist among LICM_BadStores and LICM_BadCalls (i.e. which test you did first).

