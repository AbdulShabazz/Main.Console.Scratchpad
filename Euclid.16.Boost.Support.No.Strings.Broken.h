#pragma once

#include <iostream>
#include <vector>
#include <array>
#include <string>

#include <queue>
#include <chrono>
#include <unordered_map>
#include <mutex>
#include <thread>

#include <boost/multiprecision/cpp_int.hpp>

namespace Euclid_Prover {

    using BigInt512_t = boost::multiprecision::cpp_int;
	using PROOF_STEP = std::vector<std::vector<std::vector<std::string>>>;
	using PROOF_REWRITE = std::vector<std::vector<std::string>>;
	using HASH = std::vector<std::array<BigInt512_t, 2>>;

	//#define IOSTREAM_INCLUDED // Comment out to disable all std::cout messages. //

	#ifdef IOSTREAM_INCLUDED
	std::vector<std::string> TraceCallStackStdStrVec{ "EuclidProver" };
	#endif

	void __stdlog__(const std::initializer_list<std::string>& msg, const bool AddNewlineFlag = true)
	{
		// Check if the iostream library is included.
        #ifdef IOSTREAM_INCLUDED
		auto it = msg.begin();
        const auto& IT = msg.end();
		std::cout << *it;
		++it; // Advance the iterator by 1 position //
		for (it; it != IT; ++it)
		{
			std::cout << *it;
		}
		if (AddNewlineFlag)
			std::cout << std::endl;
        #endif
	};

	void __stdtracein__(const std::string& msg)
	{
		// Check if the iostream library is included.
	    #ifdef IOSTREAM_INCLUDED
		TraceCallStackStdStrVec.emplace_back(msg);
		const BigInt512_t& I = TraceCallStackStdStrVec.size();
		std::cout << TraceCallStackStdStrVec[0];
		for (BigInt512_t i = 1; i < I; ++i)
		{
            std::cout << " >> " << TraceCallStackStdStrVec[std::size_t(i)];
		}
		std::cout << std::endl;
	    #endif
	};

	void __stdtraceout__(const std::string& msg)
	{
		// Check if the iostream library is included.
	#ifdef IOSTREAM_INCLUDED
		TraceCallStackStdStrVec.pop_back();
		const BigInt512_t& I = TraceCallStackStdStrVec.size();
		std::string buff{ TraceCallStackStdStrVec[0] };
		for (BigInt512_t i = 1; i < I; ++i)
		{
			buff.append(" >> " + TraceCallStackStdStrVec[std::size_t(i)]);
		}
		std::cout << buff << " << " << msg << std::endl;
		std::cout << buff << std::endl;
	#endif
	};

	/*

	  AUTHOR
		  Seagat2011 (https://github.com/Seagat2011, https://eternagame.org/web/player/90270/, https://fold.it/port/user/1992490)

	  VERSION
		  Major.Minor.Bugfix.Patch
		  12.0.0.0 // Euclid.16.Boost.Support.No.Strings. h //

	  DESCRIPTION
		Theorem prover written in C++23. Ported from ECMA-262 JavaScript (A grammar reduction term-rewriting system)
		for use in the Unreal Engine 5.2 Core in-game Framework.

		 The following #ifdef EUCLIDPROVERLIBDLL_EXPORTS block is the standard way of creating macros which make exporting
		 from a DLL simpler. All files within this DLL are compiled with the EUCLIDPROVERLIBDLL_EXPORTS
		 symbol defined on the command line. This symbol should NOT be defined on any project
		 that calls this DLL. This way any other project whose source files include this file see
		 API_EXPORT functions as being imported from a DLL, whereas this DLL sees symbols
		 defined with this macro as being exported.

	  C++23 UPDATES
		+ PrintPath Support
		+ Fast-Forwarding (FF) support for proof search
		+ BigInt (boost) support
		+ Prime(k++) ==> Prime([k++])
		+ std::unordered_map ('symbol' == 'SYMBOL') ==> std::unordered_multimap ('symbol' != 'SYMBOL')
		+ Lockless stack manager: RecursionLimiter (Eliminates mutex/semaphore Performance penalty)
		- Multithreaded support (+ Reduced latency, - Reduced scalability)

	  JavaScript UPDATES
		+ Negative proof assertions ~=
		+ _AXIOM_.optimizeCallGraph
		+ Improved ProofComplete search performance
		+ Prove via Auto (PASS)
		+ Axiom._eval => Axiom._reduce
		+ Axiom.{_reduce,_expand} => eventListener(s)
		+ solutionEditor => contentEditable
		+ Prove via Reduce (PASS)
		+ Prove via Expand (PASS)
		+ scoping functionality
		+ LibreOffice math library support
		- Axiom._eval eventListener

	  NOTES:
		Rewrites are performed via the aid of a rewrite compiler (eg. via LEMMA SUBSTITUTION); SEE TEST CASES

		Substitution methods:

			1. AXIOMATIC: 1 + 1 = 2
			2. LEMMA SUBSTITUTION: 1 <==> 1 / 1

		Note: Lemma substitutions are rewrite "helpers" which can be used to rewrite axioms.
		Great care must be taken with them because they can introduce recursion, stack overflows,
		and other performance bugs: For example, consider: "{ PlayerCharacterSideKick } IsIn { StyxBoat }" -
		the "IsIn" operator may or may not link unrelated categories, indefinitely;
		whereas: "{ PlayerCharacterSideKick } IsIn_StyxBoat " is safer and guaranteed to converge.

	  Note: The rewrite engine considerers one or more symbols enclosed within curly braces and or brackets as a scoped variable hint, which can be replaced.

	  Usage example (pseudo code).

		( { a } plus { b } ) raised { 2 } = { { c } raised { 2 } } plus { 2ab }

		{ { a } raised { 2 } } plus { 2ab } plus { b raised { 2 } } <== ( { a } plus { b } ) raised { 2 }
		( { a } plus { b } ) raised { 2 } minus { 2ab } = { c } raised { 2 } <== ( { a } plus { b } ) raised { 2 } = { { c } raised { 2 } } plus { 2ab }
		{ { a } raised { 2 } } plus { 2ab } minus { 2ab } plus { b raised { 2 } } ==> { { a } raised { 2 } } plus { { b } raised { 2 } }

		Prove { { a } raised { 2 } } plus { { b } raised { 2 } } = { c } raised { 2 }

	  Usage Example (pseudo code).

		// Axioms
		{ PlayerCharacterSideKick } IsIn { StyxBoat } = { StyxBoat } IsIn { StyxRiver } // Current Game State
		{ PlayerCharacterSideKick } IsIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand } and { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
		{ PlayerCharacterSideKick } IsIn { EuropaLand } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
		{ PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
		{ PlayerCharacterSideKick } IsNotIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
		.
		. [Other available but non-relevant Game States the framework can choose from ]
		.
		{ PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { QuadUtilityVehicle } and { VehicleDriveDisabled }

		// Lemmas
		{ PlayerCharacterSideKick } IsIn { StyxBoat } <== { StyxBoat } IsNotIn { StyxRiver } // These are connectives, and axiom helpers
		{ PlayerCharacterSideKick } IsOn { Vehicle } <== { VehicleDriveDisabled }
		{ PlayerCharacterSideKick } IsIn { Vehicle { QuadUtilityVehicle } } <== { PlayerCharacterSideKick } IsIn { QuadUtilityVehicle }
		{ PlayerCharacterSideKick } IsNotIn { StyxBoat } ==> { StyxBoat } IsNotIn { StyxRiver }

		// Theorem to prove
		Prove { PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { QuadUtilityVehicle } and { VehicleDriveDisabled }

		// Proof-Steps (Output)
		{ PlayerCharacterSideKick } IsIn { StyxBoat } = { StyxBoat } IsIn { StyxRiver }
		{ PlayerCharacterSideKick } IsIn { StyxBoat } = { StyxBoat } IsNotIn { StyxRiver }
		{ PlayerCharacterSideKick } IsNotIn { StyxBoat } = { StyxBoat } IsNotIn { StyxRiver }
		{ PlayerCharacterSideKick } IsIn { EuropaLand } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
		{ PlayerCharacterSideKick } IsNotIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand }
		{ PlayerCharacterSideKick } IsIn { Vehicle { QuadUtilityVehicle } } = { Vehicle { QuadUtilityVehicle } } IsIn { EuropaLand } and { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
		{ PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { Vehicle { QuadUtilityVehicle { VehicleDriveDisabled } } }
		{ PlayerCharacterSideKick } IsIn { QuadUtilityVehicle } = { QuadUtilityVehicle } and { VehicleDriveDisabled }

		Usage Example C++

		```c++

			std::vector<
				std::vector<
				std::vector<
				std::vector<
				std::string>>>>

				// Instantiate ProofStep_4DStdStrVec[proof][step][lhs/rhs][token]
				ProofStep_4DStdStrVec;

			std::vector<
				std::vector<
				std::string>>

				// Instantiate AxiomCommitLog_StdStrVec[proof][step]
				AxiomCommitLog_StdStrVec;

			// Instantiate Prover (module)
			EuclidProver<BracketType::CurlyBraces> Euclid;

			Euclid.Axioms
			(
				{
					// Axiom_00
					{
						{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "StyxBoat", "}" },  // lhs
						{ "{", "StyxBoat", "}", "IsIn", "{", "StyxRiver", "}" } // rhs
					},

					 // Axiom_01
					{
						{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "Vehicle", "{", "QuadUtilityVehicle", "}", "}"}, // lhs
						{ "{", "Vehicle", "{", "QuadUtilityVehicle", "}", "}", "IsIn", "{", "EuropaLand", "}", "and", "{", "Vehicle", "{", "QuadUtilityVehicle", "{", "VehicleDriveDisabled", "}", "}", "}" } // rhs
					},

					// Axiom_02
					{
						{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "EuropaLand", "}" }, // lhs
						{ "{", "Vehicle", "{", "QuadUtilityVehicle", "}", "}", "IsIn", "{", "EuropaLand", "}" } // rhs
					},

					// Axiom_03
					{
						{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "QuadUtilityVehicle", "}" }, // lhs
						{ "{", "Vehicle", "{", "QuadUtilityVehicle", "{", "VehicleDriveDisabled", "}", "}" } // rhs
					},

					// Axiom_04
					{
						{ "{", "PlayerCharacterSideKick", "}", "IsNotIn", "{", "Vehicle", "{", "QuadUtilityVehicle", "}", "}" }, // lhs
						{ "{", "Vehicle", "{", "QuadUtilityVehicle", "}", "}", "IsIn", "{", "EuropaLand", "}" } // rhs
					},

					// Axiom_05
					{
						{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "QuadUtilityVehicle", "}" }, // lhs
						{ "{", "QuadUtilityVehicle", "}", "and", "{", "VehicleDriveDisabled", "}" } // rhs
					}
				}
			);

			Euclid.Lemmas
			(
				// Lemma_00 (rewrite helper)
				{
					{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "StyxBoat", "}" }, // lhs
					{ "{", "StyxBoat", "}", "IsNotIn", "{", "StyxRiver", "}" } // rhs
				}
			);

			Euclid.Prove
			(
				{
					{ "{", "PlayerCharacterSideKick", "}", "IsIn", "{", "QuadUtilityVehicle", "}", }, // lhs
					{ "{", "QuadUtilityVehicle", "}", "and", "{", "VehicleDriveDisabled", "}" } // rhs
				},

				ProofStep_4DStdStrVec,
				AxiomCommitLog_StdStrVec
			);

			/ *
			if (Euclid.StatusReady())
			{
				if (Euclid.ProofFoundFlag)
				{
					std::cout << "Proof Found." << std::endl;
					ProofStep_4DStdStrVec;
					AxiomCommitLog_StdStrVec;
				} else if (ProofStep_4DStdStrVec.size ()) {
					std::cout << "Partial Proof Found." << std::endl;
					ProofStep_4DStdStrVec;
					AxiomCommitLog_StdStrVec;
				} else {
					std::cout << "No Proof Found." << std::endl;
				}
			} else {
				std::cout << "No Proof Found." << std::endl;
			}
			* /

			while (!Euclid.StatusReadyFlag)
			{
				std::this_thread::yield();
			}

			if (Euclid.ProofFoundFlag)
			{
				std::cout << "Proof Found. (QED)" << std::endl;
				ProofStep4DStdStrVec;
				Euclid.PrintPath(AxiomCommitLogStdStrVec);
			} else if (ProofStep4DStdStrVec.size()) {
				std::cout << "Partial Proof Found." << std::endl;
				ProofStep4DStdStrVec;
				Euclid.PrintPath(AxiomCommitLogStdStrVec);
			} else {
				std::cout << "No Proof Found." << std::endl;
			}

			// Suspend a proof for current (GUID)
			const BigInt128_t guid = Euclid.Suspend();
			std::cout << "Proof suspended for: guid_" << guid << std::endl;

			// Resume a proof for (GUID)
			if(Euclid.Resume(guid))
			{
				std::cout << "Proof resumed for: guid_" << guid << std::endl;
			}

		```

	  TEST CASE 246: nanoseconds elapsed: -

	  REFERENCES
		  OpenAI GPT-4-32k-0314 ( { max_tokens:32000, temperature:1.0, top_p:1.0, N:1,
				stream:false, logprobs:NULL, echo:false, stop:NULL, presence_penalty:0,
				frequency_penalty:0, best_of:1, logit_bias:NULL } )

	  COMPATIBILITY
		  Windows 11+ x86i64 platform with dedicated Coprocessors-, Accelerators-, FPGAs-, and or GPUs

	*/

	std::unordered_multimap<
		std::string, BigInt512_t>
		SymbolToPrime_UInt64MultiMap =
	{
		{"=", 2},
		{"{", 3},
		{"}", 5},
		{"(", 7},
		{")", 11},
		{"[", 13},
		{"]", 17}
	};

	std::size_t PrimeCompositeVecSize_UInt64{ 7 };

	std::vector<BigInt512_t> PrimeComposite_UInt64Vec{ 2, 3, 5, 7, 11, 13, 17 };

	std::vector<
		std::vector<
		std::vector<
		std::string>>> TempProofSteps{};

	/**
	 * Prime() : Return the next prime in the series...
	 * usage: Prime(); // returns 23
	*/
	inline BigInt512_t Prime()
	{
		__stdtracein__("Euclid_Prover::Prime");
		const std::size_t Index_UInt64 = PrimeCompositeVecSize_UInt64++;
		for (BigInt512_t i = PrimeComposite_UInt64Vec.back() + 2; PrimeComposite_UInt64Vec.size() < PrimeCompositeVecSize_UInt64; i += 2)
		{
			bool Add_Flag{ true };

			BigInt512_t j{};

			const BigInt512_t J = i / 4;

			for (const BigInt512_t& val : PrimeComposite_UInt64Vec)
			{

				if (/*(i % 2) == 0 ||*/ ( i % val ) == 0)
				{
					Add_Flag = false;
					break;
				}

				if (++j >= J)
				{
					break;
				}
			}

			if (Add_Flag)
			{
				PrimeComposite_UInt64Vec.emplace_back(i);
			}
		}
		__stdtraceout__("Euclid_Prover::Prime");
		return PrimeComposite_UInt64Vec[Index_UInt64];
	}
	
	inline void PrintPath(const PROOF_STEP& OutProofStep3DStdStrVec)
	{
		__stdtracein__("PrintPath");
	    for (const std::vector<std::vector<std::string>>& x : OutProofStep3DStdStrVec)
	    {
	        std::cout << "{";
    	    for (const std::vector<std::string>& y : x)
    	    {
    	        std::cout << "{";
    	       for (const std::string& z : y)
        	    {
                   std::cout << " " << z << " " ;
        	    } 
    	        std::cout << "} ";
    	    }
            std::cout << "}" << std::endl;
	    }
		__stdtraceout__("PrintPath");
	}

	inline std::string ComputeStringHash(const std::vector<std::string>& Theorem_Src)
	{
		__stdtracein__("ComputeStringHash");

		std::string retbuff{};
		for (const std::string& z : Theorem_Src)
		{
			retbuff += z;
		}

		__stdtraceout__("ComputeStringHash");
		return retbuff;
	}
	
	inline BigInt512_t CreatePrimaryKey(const std::vector<std::string>& Theorem_Src)
	{
		__stdtracein__("ComputeBigIntHash");

		BigInt512_t retbuff{ 1 };
        for (const std::string& z : Theorem_Src)
        {
			if (SymbolToPrime_UInt64MultiMap.find(z) == SymbolToPrime_UInt64MultiMap.end())
			{
				SymbolToPrime_UInt64MultiMap.emplace(z, Prime());
			}

			retbuff *= SymbolToPrime_UInt64MultiMap.find(z)->second;
        }    
	    
		__stdtraceout__("ComputeBigIntHash");
		return retbuff;
	}

	inline bool SubnetFound
	(
		const std::vector<std::string>& Theorem_Src,
		const std::vector<std::string>& Axiom_Src,
		const std::vector<std::string>& Axiom_Dest,
		std::vector<std::string>& Theorem_Dest
	)
	{
		__stdtracein__("SubnetFound");
		const BigInt512_t& th_size = Theorem_Src.size();
		const BigInt512_t& ax_size = Axiom_Src.size();

		bool SubnetFoundFlag{};
		
		if (ax_size <= th_size)
		{
			BigInt512_t i_ax{};

			for (const std::string& th_tok : Theorem_Src)
			{
                const bool MatchFoundFlag = ( !SubnetFoundFlag && ( Axiom_Src[std::size_t(i_ax)] == th_tok ) );
				if (MatchFoundFlag) {
					++i_ax;
					const bool LocalSubnetFoundFlag = ( i_ax == ax_size );
					if (LocalSubnetFoundFlag)
					{
						for (const std::string ax_tok : Axiom_Dest) {
							Theorem_Dest.emplace_back(ax_tok);
						}
                        __stdlog__({"SubnetFound!"});
						SubnetFoundFlag = true;
						i_ax = 0;
						continue;
					}
				} else {
					i_ax = 0;
					Theorem_Dest.emplace_back(th_tok);
				}
			}
		}
		__stdtraceout__("SubnetFound");
		return SubnetFoundFlag;
	};

    auto Prove = [] () -> void
    {
        __stdtracein__("Prove");
        
        bool QED{};

        constexpr int LHS = 0;
        constexpr int RHS = 1;
        constexpr int opcode_field = 2;
        constexpr int opcode = 0;
        constexpr int axiom_label = 1;
		constexpr int guid_UInt64 = 2;
		constexpr int left_hash_UInt64 = 3;
		constexpr int right_hash_UInt64 = 4;

        const std::string axiom_name = "Axiom_";
        const std::string theorem_name = "Theorem_";

        class OPCODESTRUCT {
        public:
            const std::string lhs_reduce = "lhs_reduce ";
            const std::string lhs_expand = "lhs_expand ";
            const std::string rhs_reduce = "rhs_reduce ";
            const std::string rhs_expand = "rhs_expand ";
        };

        OPCODESTRUCT OpcodeStruct;

        // subnets //
        
		PROOF_STEP InProofLibrary3DStdStrVec = {
            // {{lhs},{rhs}} // 
            /*
            {{1, 10001, 1, 10001, 1, 10001, 1},{4}},
            {{1, 10001, 1},{2}},
            {{2, 10001, 2},{4}}
            */
			 {
				 {
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+", "1", "+",
		 "1", "+", "1", "+", "1"
	 }, // lhs
	 {
		 "246"
	 } }, // rhs
{ { "1", "+", "1" }, { "2" } },
{ { "1", "+", "2" }, { "3" } },
{ { "2", "+", "2" }, { "4" } },
{ { "1", "+", "4" }, { "5" } },
{ { "3", "+", "3" }, { "6" } },
{ { "1", "+", "6" }, { "7" } },
{ { "4", "+", "4" }, { "8" } },
{ { "1", "+", "8" }, { "9" } },
{ { "5", "+", "5" }, { "10" } },
{ { "1", "+", "10" }, { "11" } },
{ { "6", "+", "6" }, { "12" } },
{ { "1", "+", "12" }, { "13" } },
{ { "7", "+", "7" }, { "14" } },
{ { "1", "+", "14" }, { "15" } },
{ { "8", "+", "8" }, { "16" } },
{ { "1", "+", "16" }, { "17" } },
{ { "9", "+", "9" }, { "18" } },
{ { "1", "+", "18" }, { "19" } },
{ { "10", "+", "10" }, { "20" } },
{ { "1", "+", "20" }, { "21" } },
{ { "11", "+", "11" }, { "22" } },
{ { "1", "+", "22" }, { "23" } },
{ { "12", "+", "12" }, { "24" } },
{ { "1", "+", "24" }, { "25" } },
{ { "13", "+", "13" }, { "26" } },
{ { "1", "+", "26" }, { "27" } },
{ { "14", "+", "14" }, { "28" } },
{ { "1", "+", "28" }, { "29" } },
{ { "15", "+", "15" }, { "30" } },
{ { "1", "+", "30" }, { "31" } },
{ { "16", "+", "16" }, { "32" } },
{ { "1", "+", "32" }, { "33" } },
{ { "17", "+", "17" }, { "34" } },
{ { "1", "+", "34" }, { "35" } },
{ { "18", "+", "18" }, { "36" } },
{ { "1", "+", "36" }, { "37" } },
{ { "19", "+", "19" }, { "38" } },
{ { "1", "+", "38" }, { "39" } },
{ { "20", "+", "20" }, { "40" } },
{ { "1", "+", "40" }, { "41" } },
{ { "21", "+", "21" }, { "42" } },
{ { "1", "+", "42" }, { "43" } },
{ { "22", "+", "22" }, { "44" } },
{ { "1", "+", "44" }, { "45" } },
{ { "23", "+", "23" }, { "46" } },
{ { "1", "+", "46" }, { "47" } },
{ { "24", "+", "24" }, { "48" } },
{ { "1", "+", "48" }, { "49" } },
{ { "25", "+", "25" }, { "50" } },
{ { "1", "+", "50" }, { "51" } },
{ { "26", "+", "26" }, { "52" } },
{ { "1", "+", "52" }, { "53" } },
{ { "27", "+", "27" }, { "54" } },
{ { "1", "+", "54" }, { "55" } },
{ { "28", "+", "28" }, { "56" } },
{ { "1", "+", "56" }, { "57" } },
{ { "29", "+", "29" }, { "58" } },
{ { "1", "+", "58" }, { "59" } },
{ { "30", "+", "30" }, { "60" } },
{ { "1", "+", "60" }, { "61" } },
{ { "31", "+", "31" }, { "62" } },
{ { "1", "+", "62" }, { "63" } },
{ { "32", "+", "32" }, { "64" } },
{ { "1", "+", "64" }, { "65" } },
{ { "33", "+", "33" }, { "66" } },
{ { "1", "+", "66" }, { "67" } },
{ { "34", "+", "34" }, { "68" } },
{ { "1", "+", "68" }, { "69" } },
{ { "35", "+", "35" }, { "70" } },
{ { "1", "+", "70" }, { "71" } },
{ { "36", "+", "36" }, { "72" } },
{ { "1", "+", "72" }, { "73" } },
{ { "37", "+", "37" }, { "74" } },
{ { "1", "+", "74" }, { "75" } },
{ { "38", "+", "38" }, { "76" } },
{ { "1", "+", "76" }, { "77" } },
{ { "39", "+", "39" }, { "78" } },
{ { "1", "+", "78" }, { "79" } },
{ { "40", "+", "40" }, { "80" } },
{ { "1", "+", "80" }, { "81" } },
{ { "41", "+", "41" }, { "82" } },
{ { "1", "+", "82" }, { "83" } },
{ { "42", "+", "42" }, { "84" } },
{ { "1", "+", "84" }, { "85" } },
{ { "43", "+", "43" }, { "86" } },
{ { "1", "+", "86" }, { "87" } },
{ { "44", "+", "44" }, { "88" } },
{ { "1", "+", "88" }, { "89" } },
{ { "45", "+", "45" }, { "90" } },
{ { "1", "+", "90" }, { "91" } },
{ { "46", "+", "46" }, { "92" } },
{ { "1", "+", "92" }, { "93" } },
{ { "47", "+", "47" }, { "94" } },
{ { "1", "+", "94" }, { "95" } },
{ { "48", "+", "48" }, { "96" } },
{ { "1", "+", "96" }, { "97" } },
{ { "49", "+", "49" }, { "98" } },
{ { "1", "+", "98" }, { "99" } },
{ { "50", "+", "50" }, { "100" } },
{ { "1", "+", "100" }, { "101" } },
{ { "51", "+", "51" }, { "102" } },
{ { "1", "+", "102" }, { "103" } },
{ { "52", "+", "52" }, { "104" } },
{ { "1", "+", "104" }, { "105" } },
{ { "53", "+", "53" }, { "106" } },
{ { "1", "+", "106" }, { "107" } },
{ { "54", "+", "54" }, { "108" } },
{ { "1", "+", "108" }, { "109" } },
{ { "55", "+", "55" }, { "110" } },
{ { "1", "+", "110" }, { "111" } },
{ { "56", "+", "56" }, { "112" } },
{ { "1", "+", "112" }, { "113" } },
{ { "57", "+", "57" }, { "114" } },
{ { "1", "+", "114" }, { "115" } },
{ { "58", "+", "58" }, { "116" } },
{ { "1", "+", "116" }, { "117" } },
{ { "59", "+", "59" }, { "118" } },
{ { "1", "+", "118" }, { "119" } },
{ { "60", "+", "60" }, { "120" } },
{ { "1", "+", "120" }, { "121" } },
{ { "61", "+", "61" }, { "122" } },
{ { "1", "+", "122" }, { "123" } },
{ { "62", "+", "62" }, { "124" } },
{ { "1", "+", "124" }, { "125" } },
{ { "63", "+", "63" }, { "126" } },
{ { "1", "+", "126" }, { "127" } },
{ { "64", "+", "64" }, { "128" } },
{ { "1", "+", "128" }, { "129" } },
{ { "65", "+", "65" }, { "130" } },
{ { "1", "+", "130" }, { "131" } },
{ { "66", "+", "66" }, { "132" } },
{ { "1", "+", "132" }, { "133" } },
{ { "67", "+", "67" }, { "134" } },
{ { "1", "+", "134" }, { "135" } },
{ { "68", "+", "68" }, { "136" } },
{ { "1", "+", "136" }, { "137" } },
{ { "69", "+", "69" }, { "138" } },
{ { "1", "+", "138" }, { "139" } },
{ { "70", "+", "70" }, { "140" } },
{ { "1", "+", "140" }, { "141" } },
{ { "71", "+", "71" }, { "142" } },
{ { "1", "+", "142" }, { "143" } },
{ { "72", "+", "72" }, { "144" } },
{ { "1", "+", "144" }, { "145" } },
{ { "73", "+", "73" }, { "146" } },
{ { "1", "+", "146" }, { "147" } },
{ { "74", "+", "74" }, { "148" } },
{ { "1", "+", "148" }, { "149" } },
{ { "75", "+", "75" }, { "150" } },
{ { "1", "+", "150" }, { "151" } },
{ { "76", "+", "76" }, { "152" } },
{ { "1", "+", "152" }, { "153" } },
{ { "77", "+", "77" }, { "154" } },
{ { "1", "+", "154" }, { "155" } },
{ { "78", "+", "78" }, { "156" } },
{ { "1", "+", "156" }, { "157" } },
{ { "79", "+", "79" }, { "158" } },
{ { "1", "+", "158" }, { "159" } },
{ { "80", "+", "80" }, { "160" } },
{ { "1", "+", "160" }, { "161" } },
{ { "81", "+", "81" }, { "162" } },
{ { "1", "+", "162" }, { "163" } },
{ { "82", "+", "82" }, { "164" } },
{ { "1", "+", "164" }, { "165" } },
{ { "83", "+", "83" }, { "166" } },
{ { "1", "+", "166" }, { "167" } },
{ { "84", "+", "84" }, { "168" } },
{ { "1", "+", "168" }, { "169" } },
{ { "85", "+", "85" }, { "170" } },
{ { "1", "+", "170" }, { "171" } },
{ { "86", "+", "86" }, { "172" } },
{ { "1", "+", "172" }, { "173" } },
{ { "87", "+", "87" }, { "174" } },
{ { "1", "+", "174" }, { "175" } },
{ { "88", "+", "88" }, { "176" } },
{ { "1", "+", "176" }, { "177" } },
{ { "89", "+", "89" }, { "178" } },
{ { "1", "+", "178" }, { "179" } },
{ { "90", "+", "90" }, { "180" } },
{ { "1", "+", "180" }, { "181" } },
{ { "91", "+", "91" }, { "182" } },
{ { "1", "+", "182" }, { "183" } },
{ { "92", "+", "92" }, { "184" } },
{ { "1", "+", "184" }, { "185" } },
{ { "93", "+", "93" }, { "186" } },
{ { "1", "+", "186" }, { "187" } },
{ { "94", "+", "94" }, { "188" } },
{ { "1", "+", "188" }, { "189" } },
{ { "95", "+", "95" }, { "190" } },
{ { "1", "+", "190" }, { "191" } },
{ { "96", "+", "96" }, { "192" } },
{ { "1", "+", "192" }, { "193" } },
{ { "97", "+", "97" }, { "194" } },
{ { "1", "+", "194" }, { "195" } },
{ { "98", "+", "98" }, { "196" } },
{ { "1", "+", "196" }, { "197" } },
{ { "99", "+", "99" }, { "198" } },
{ { "1", "+", "198" }, { "199" } },
{ { "100", "+", "100" }, { "200" } },
{ { "1", "+", "200" }, { "201" } },
{ { "101", "+", "101" }, { "202" } },
{ { "1", "+", "202" }, { "203" } },
{ { "102", "+", "102" }, { "204" } },
{ { "1", "+", "204" }, { "205" } },
{ { "103", "+", "103" }, { "206" } },
{ { "1", "+", "206" }, { "207" } },
{ { "104", "+", "104" }, { "208" } },
{ { "1", "+", "208" }, { "209" } },
{ { "105", "+", "105" }, { "210" } },
{ { "1", "+", "210" }, { "211" } },
{ { "106", "+", "106" }, { "212" } },
{ { "1", "+", "212" }, { "213" } },
{ { "107", "+", "107" }, { "214" } },
{ { "1", "+", "214" }, { "215" } },
{ { "108", "+", "108" }, { "216" } },
{ { "1", "+", "216" }, { "217" } },
{ { "109", "+", "109" }, { "218" } },
{ { "1", "+", "218" }, { "219" } },
{ { "110", "+", "110" }, { "220" } },
{ { "1", "+", "220" }, { "221" } },
{ { "111", "+", "111" }, { "222" } },
{ { "1", "+", "222" }, { "223" } },
{ { "112", "+", "112" }, { "224" } },
{ { "1", "+", "224" }, { "225" } },
{ { "113", "+", "113" }, { "226" } },
{ { "1", "+", "226" }, { "227" } },
{ { "114", "+", "114" }, { "228" } },
{ { "1", "+", "228" }, { "229" } },
{ { "115", "+", "115" }, { "230" } },
{ { "1", "+", "230" }, { "231" } },
{ { "116", "+", "116" }, { "232" } },
{ { "1", "+", "232" }, { "233" } },
{ { "117", "+", "117" }, { "234" } },
{ { "1", "+", "234" }, { "235" } },
{ { "118", "+", "118" }, { "236" } },
{ { "1", "+", "236" }, { "237" } },
{ { "119", "+", "119" }, { "238" } },
{ { "1", "+", "238" }, { "239" } },
{ { "120", "+", "120" }, { "240" } },
{ { "1", "+", "240" }, { "241" } },
{ { "121", "+", "121" }, { "242" } },
{ { "1", "+", "242" }, { "243" } },
{ { "122", "+", "122" }, { "244" } },
{ { "1", "+", "244" }, { "245" } },
{ { "123", "+", "123" }, { "246" } }

}; // PrintPath(InProofLibrary3DStdStrVec);
        
        PROOF_STEP OutProofStep3DStdStrVec;

        OutProofStep3DStdStrVec.push_back(InProofLibrary3DStdStrVec[0]);
		OutProofStep3DStdStrVec[0].push_back({ "root", "Theorem_", "0" });
        
        //PrintPath(OutProofStep3DStdStrVec);

		auto PopulateLocalHashLibraryUInt64Vec = [&] (const PROOF_STEP& InLocalProofStep3DStdStrVec) -> HASH
		{
			__stdtracein__("PopulateProofStepLibrary3DUInt64Vec");
			HASH Hash3DUInt64Vec{};
			for (const PROOF_REWRITE& Axiom_i : InLocalProofStep3DStdStrVec)
			{
				const BigInt512_t LHSPrimaryKeyUInt64 = CreatePrimaryKey(Axiom_i[LHS]);
				const BigInt512_t RHSPrimaryKeyUInt64 = CreatePrimaryKey(Axiom_i[RHS]);
				Hash3DUInt64Vec.emplace_back(std::array<BigInt512_t,2>{ LHSPrimaryKeyUInt64, RHSPrimaryKeyUInt64 });
			}
			__stdtraceout__("PopulateProofStepLibrary3DUInt64Vec");
			return Hash3DUInt64Vec;
		};

		const HASH PrimaryKeyLibrary3DUInt64Vec = 
			PopulateLocalHashLibraryUInt64Vec(InProofLibrary3DStdStrVec);

        /*
            // internal representation //
            std::vector<
            std::vector<
            std::vector<std::string>>> OutProofStep3DStdStrVec =
            {
                // {{lhs},{rhs},{opcode}} //
                {{1,10001,1,10001,1,10001,1},{4},{0,10002,0}} // {{1,+,1,+,1,+,1},{4},{root,Theorem_,0}}
            };
        */
		std::unordered_map< BigInt512_t, std::unordered_map<BigInt512_t, bool>> CallGraphMap{};

		auto BuildCallGraph = [&] ()
		{
			const BigInt512_t SIZE = PrimaryKeyLibrary3DUInt64Vec.size();
			for (BigInt512_t i = 0; i < SIZE; ++i)
			{
				for (BigInt512_t j = 0; j < SIZE; ++j)
				{
					const std::size_t ii{ i };
					const std::size_t jj{ i };
					if
					(
						ii != jj && (
						PrimaryKeyLibrary3DUInt64Vec[ii][LHS] % PrimaryKeyLibrary3DUInt64Vec[jj][LHS] ||
						PrimaryKeyLibrary3DUInt64Vec[ii][LHS] % PrimaryKeyLibrary3DUInt64Vec[jj][RHS] ||
						PrimaryKeyLibrary3DUInt64Vec[ii][RHS] % PrimaryKeyLibrary3DUInt64Vec[jj][LHS] ||
						PrimaryKeyLibrary3DUInt64Vec[ii][RHS] % PrimaryKeyLibrary3DUInt64Vec[jj][RHS] )
					)
					{
						CallGraphMap.emplace(ii, std::unordered_map<BigInt512_t, bool>{{jj, true}});
					}
				}
			}
		};

		BuildCallGraph();

		bool bFastForwardFlag{};

		struct PROOF_STRUCT
		{
			PROOF_STEP _;
			BigInt512_t LHSPrimaryKeyUInt64{1};
			BigInt512_t RHSPrimaryKeyUInt64{1};
			BigInt512_t last_guid{};
		};
        
        std::priority_queue<PROOF_STRUCT> Tasks_Thread, FastForwardTask_Thread;

		PROOF_STRUCT Proof;
		Proof._ = OutProofStep3DStdStrVec;
		Proof.LHSPrimaryKeyUInt64 = PrimaryKeyLibrary3DUInt64Vec[0][LHS];
		Proof.RHSPrimaryKeyUInt64 = PrimaryKeyLibrary3DUInt64Vec[0][RHS];

		std::unordered_map<std::string, PROOF_STRUCT>
			LHSRouteHistoryMap, RHSRouteHistoryMap;

        Tasks_Thread.push(Proof);

        // *** Core Proof Engine (Loop) *** //
        while (!Tasks_Thread.empty() && !QED)
        {
			PROOF_STRUCT TempProofStruct { !bFastForwardFlag ? Tasks_Thread.top() : FastForwardTask_Thread.top() };

			PROOF_STEP TempProofStep3DStdStrVec = TempProofStruct._;

			const BigInt512_t last_GUID = TempProofStruct.last_guid;
			const BigInt512_t LHSPrimaryKeyUInt64 = TempProofStruct.LHSPrimaryKeyUInt64;
			const BigInt512_t RHSPrimaryKeyUInt64 = TempProofStruct.RHSPrimaryKeyUInt64;
            
            !bFastForwardFlag ? Tasks_Thread.pop() : FastForwardTask_Thread.pop() ;
            
		    bFastForwardFlag = false;
            
            const PROOF_REWRITE& Theorem{ TempProofStep3DStdStrVec.back() };

			QED = ( LHSPrimaryKeyUInt64 == RHSPrimaryKeyUInt64 ); // Theorem[LHS] == Theorem[RHS]; //

			if (QED)
			{
				OutProofStep3DStdStrVec = TempProofStep3DStdStrVec;
				PrintPath(OutProofStep3DStdStrVec);
				break;
			}
            
            const BigInt512_t I = InProofLibrary3DStdStrVec.size();

            for(BigInt512_t i = 1; i < I; ++i)
            {
				const std::size_t ii {i};

                const
				PROOF_REWRITE& Axiom = InProofLibrary3DStdStrVec[ii];

				const BigInt512_t LHSAxiomPrimaryKeyUInt64 = PrimaryKeyLibrary3DUInt64Vec[ii][LHS];
				const BigInt512_t RHSAxiomPrimaryKeyUInt64 = PrimaryKeyLibrary3DUInt64Vec[ii][RHS];
                
                PROOF_REWRITE
                Theorem_0000{Theorem},
                Theorem_0001{Theorem},
                Theorem_0002{Theorem},
                Theorem_0003{Theorem},
                Theorem_0004{Theorem},
                Theorem_0005{Theorem},
                Theorem_0006{Theorem},
                Theorem_0007{Theorem};
                
                Theorem_0000[LHS].clear();
                Theorem_0001[LHS].clear();
                
                Theorem_0002[RHS].clear();
                Theorem_0003[RHS].clear();

				const bool LHSPrimaryKeyFoundFlag = ( CallGraphMap[last_GUID][ii] || ( ( LHSPrimaryKeyUInt64 % LHSAxiomPrimaryKeyUInt64 ) == 0 ) );
				const bool RHSPrimaryKeyFoundFlag = ( CallGraphMap[last_GUID][ii] || ( ( RHSPrimaryKeyUInt64 % RHSAxiomPrimaryKeyUInt64 ) == 0 ) );

				const bool lhs_reduce_flag = LHSPrimaryKeyFoundFlag && SubnetFound(Theorem[LHS], Axiom[LHS], Axiom[RHS], Theorem_0000[LHS]);
				const bool lhs_expand_flag = LHSPrimaryKeyFoundFlag && SubnetFound(Theorem[LHS], Axiom[RHS], Axiom[LHS], Theorem_0001[LHS]);
				const bool rhs_reduce_flag = RHSPrimaryKeyFoundFlag && SubnetFound(Theorem[RHS], Axiom[LHS], Axiom[RHS], Theorem_0002[RHS]);
				const bool rhs_expand_flag = RHSPrimaryKeyFoundFlag && SubnetFound(Theorem[RHS], Axiom[RHS], Axiom[LHS], Theorem_0003[RHS]);

				auto LHSReduceFastForward = [&] () -> bool {
					//__stdlog__({"lhs_reduce_ via ",axiom_name, i});
					Theorem_0000[opcode_field][opcode] = OpcodeStruct.lhs_reduce;
					Theorem_0000[opcode_field][axiom_label] = axiom_name;
					Theorem_0000[opcode_field][guid_UInt64] = ii;

					PROOF_STEP TempProofStep3DStdStrVec_0000{ TempProofStep3DStdStrVec };
					TempProofStep3DStdStrVec_0000.emplace_back(Theorem_0000);

					// Commit for later fast-forward //
					const std::string HashKeyString = ComputeStringHash(Theorem_0000[LHS]);
					if (LHSRouteHistoryMap.find(HashKeyString) == LHSRouteHistoryMap.end())
						LHSRouteHistoryMap.emplace(HashKeyString, TempProofStep3DStdStrVec_0000);

					const BigInt512_t UpdateLHSPrimaryKeyUInt64 = LHSPrimaryKeyUInt64 / LHSAxiomPrimaryKeyUInt64 * RHSAxiomPrimaryKeyUInt64;

					PROOF_STRUCT TempProofStruct_0000;
					TempProofStruct_0000.LHSPrimaryKeyUInt64 = UpdateLHSPrimaryKeyUInt64;
					TempProofStruct_0000.last_guid = ii;

					// Attempt fast-forward //
					if(RHSRouteHistoryMap.find(HashKeyString) != RHSRouteHistoryMap.end())
					{
						std::cout << "Proof found in Module_0000 via Fast-Forward (FF)" << std::endl;
						__stdlog__({ "Proof found in Module_0000 via Fast-Forward (FF)" });
						const auto it = LHSRouteHistoryMap[HashKeyString];
						auto iProofStep2DStdStrVec = it._.begin();
						const auto iProofStepEND = it._.end();
						const auto& LHS_SOLU = Theorem_0000[LHS];
						// Skip the root element //
						for (++iProofStep2DStdStrVec; iProofStep2DStdStrVec != iProofStepEND; ++iProofStep2DStdStrVec) {
							( *iProofStep2DStdStrVec )[LHS] = LHS_SOLU;
							TempProofStep3DStdStrVec_0000.emplace_back(*iProofStep2DStdStrVec);
						}
						TempProofStruct_0000._ = TempProofStep3DStdStrVec_0000;
						TempProofStruct_0000.RHSPrimaryKeyUInt64 = UpdateLHSPrimaryKeyUInt64;
						FastForwardTask_Thread.push(TempProofStruct_0000);
						return true;
					}

					TempProofStruct_0000._ = TempProofStep3DStdStrVec_0000;
					TempProofStruct_0000.RHSPrimaryKeyUInt64 = TempProofStruct.RHSPrimaryKeyUInt64;
					Tasks_Thread.push(TempProofStruct_0000);

					return false;
				};

				auto LHSExpandFastForward = [&] () -> bool {
					//__stdlog__({"lhs_reduce_ via ",axiom_name, i});
					Theorem_0001[opcode_field][opcode] = OpcodeStruct.lhs_expand;
					Theorem_0001[opcode_field][axiom_label] = axiom_name;
					Theorem_0001[opcode_field][guid_UInt64] = ii;

					PROOF_STEP TempProofStep3DStdStrVec_0001{ TempProofStep3DStdStrVec };
					TempProofStep3DStdStrVec_0001.emplace_back(Theorem_0001);

					// Commit for later fast-forward //
					const std::string HashKeyString = ComputeStringHash(Theorem_0001[LHS]);
					if (LHSRouteHistoryMap.find(HashKeyString) == LHSRouteHistoryMap.end())
						LHSRouteHistoryMap.emplace(HashKeyString, TempProofStep3DStdStrVec_0001);

					const BigInt512_t UpdateLHSPrimaryKeyUInt64 = LHSPrimaryKeyUInt64 / RHSAxiomPrimaryKeyUInt64 * LHSAxiomPrimaryKeyUInt64;

					PROOF_STRUCT TempProofStruct_0001;
					TempProofStruct_0001.LHSPrimaryKeyUInt64 = UpdateLHSPrimaryKeyUInt64;
					TempProofStruct_0001.last_guid = ii;

					// Attempt fast-forward //
					if (RHSRouteHistoryMap.find(HashKeyString) != RHSRouteHistoryMap.end())
					{
						std::cout << "Proof found in Module_0001 via Fast-Forward (FF)" << std::endl;
						__stdlog__({ "Proof found in Module_0001 via Fast-Forward (FF)" });
						const auto it = LHSRouteHistoryMap[HashKeyString];
						auto iProofStep2DStdStrVec = it._.begin();
						const auto iProofStepEND = it._.end();
						const auto& LHS_SOLU = Theorem_0001[LHS];
						// Skip the root element //
						for (++iProofStep2DStdStrVec; iProofStep2DStdStrVec != iProofStepEND; ++iProofStep2DStdStrVec) {
							( *iProofStep2DStdStrVec )[LHS] = LHS_SOLU;
							TempProofStep3DStdStrVec_0001.emplace_back(*iProofStep2DStdStrVec);
						}
						TempProofStruct_0001._ = TempProofStep3DStdStrVec_0001;
						TempProofStruct_0001.RHSPrimaryKeyUInt64 = UpdateLHSPrimaryKeyUInt64;
						FastForwardTask_Thread.push(TempProofStruct_0001);
						return true;
					} 

					TempProofStruct_0001._ = TempProofStep3DStdStrVec_0001;
					TempProofStruct_0001.RHSPrimaryKeyUInt64 = TempProofStruct.RHSPrimaryKeyUInt64;
					Tasks_Thread.push(TempProofStruct_0001);

					return false;
				};

				auto RHSReduceFastForward = [&] () -> bool {
					//__stdlog__({"lhs_reduce_ via ",axiom_name, i});
					Theorem_0002[opcode_field][opcode] = OpcodeStruct.lhs_expand;
					Theorem_0002[opcode_field][axiom_label] = axiom_name;
					Theorem_0002[opcode_field][guid_UInt64] = ii;

					PROOF_STEP TempProofStep3DStdStrVec_0002{ TempProofStep3DStdStrVec };
					TempProofStep3DStdStrVec_0002.emplace_back(Theorem_0002);

					const std::string HashKeyString = ComputeStringHash(Theorem_0002[RHS]);

					const BigInt512_t UpdateRHSPrimaryKeyUInt64 = RHSPrimaryKeyUInt64 / LHSAxiomPrimaryKeyUInt64 * RHSAxiomPrimaryKeyUInt64;

					PROOF_STRUCT TempProofStruct_0002;

					TempProofStruct_0002.last_guid = ii;
					TempProofStruct_0002._ = TempProofStep3DStdStrVec_0002;
					TempProofStruct_0002.LHSPrimaryKeyUInt64 = TempProofStruct.LHSPrimaryKeyUInt64;
					TempProofStruct_0002.RHSPrimaryKeyUInt64 = UpdateRHSPrimaryKeyUInt64;

					// Commit for later fast-forward //
					if (RHSRouteHistoryMap.find(HashKeyString) == RHSRouteHistoryMap.end())
						RHSRouteHistoryMap.emplace(HashKeyString, TempProofStruct_0002);

					// Attempt fast-forward //
					if (LHSRouteHistoryMap.find(HashKeyString) != LHSRouteHistoryMap.end())
					{
						std::cout << "Proof found in Module_0002 via Fast-Forward (FF)" << std::endl;
						__stdlog__({ "Proof found in Module_0002 via Fast-Forward (FF)" });
						const auto it = LHSRouteHistoryMap[HashKeyString];
						auto iProofStep2DStdStrVec = it._.begin();
						const auto iProofStepEND = it._.end();
						const auto RHS_SOLU = Theorem_0002[RHS];
						// Skip the root element //
						for (++iProofStep2DStdStrVec; iProofStep2DStdStrVec != iProofStepEND; ++iProofStep2DStdStrVec) {
							( *iProofStep2DStdStrVec )[RHS] = RHS_SOLU;
							TempProofStep3DStdStrVec_0002.emplace_back(*iProofStep2DStdStrVec);
						}
						TempProofStruct_0002._ = TempProofStep3DStdStrVec_0002;
						TempProofStruct_0002.RHSPrimaryKeyUInt64 = UpdateRHSPrimaryKeyUInt64;
						FastForwardTask_Thread.push(TempProofStruct_0002);
						return true;
					}

					Tasks_Thread.push(TempProofStruct_0002);

					return false;
				};
				
				auto FastForwardFound = [] (bool flag, std::function<bool()> FFFunc) -> bool
				{
					if (flag && FFFunc())
					{
						return true;
					}
					return false;
				};

				if
				(
					FastForwardFound(lhs_reduce_flag, LHSReduceFastForward) ||
					FastForwardFound(lhs_expand_flag, LHSExpandFastForward) ||
					FastForwardFound(rhs_reduce_flag, RHSReduceFastForward) ||
					FastForwardFound(rhs_expand_flag, RHSExpandFastForward)
				)
				{
					bFastForwardFlag = true;
					break;
				}
                
                if (lhs_expand_flag = SubnetFound(Theorem[LHS], Axiom[RHS], Axiom[LHS], Theorem_0001[LHS]))
                {
                    //__stdlog__({"lhs_expand_ via ",axiom_name, i});
                    Theorem_0001[opcode_field][opcode] = OpcodeStruct.lhs_expand;;
                    Theorem_0001[opcode_field][axiom_label] = axiom_name;
                    Theorem_0001[opcode_field][guid_UInt64] = i;
                    
                    PROOF_STEP TempProofStep3DStdStrVec_0001 { TempProofStep3DStdStrVec };
                    TempProofStep3DStdStrVec_0001.emplace_back(Theorem_0001);

					// Commit for later fast-forward //
					const std::string HashKeyStdStr = ComputeHash(Theorem_0001[LHS]);
					if (LHSRouteHistoryMap.find(HashKeyStdStr) == LHSRouteHistoryMap.end())
						LHSRouteHistoryMap.emplace(HashKeyStdStr, TempProofStep3DStdStrVec_0001);

					// Attempt fast-forward //
					if (RHSRouteHistoryMap.find(HashKeyStdStr) != RHSRouteHistoryMap.end()) {
                        std::cout << "Proof found in Module_0001 via Fast-Forward (FF)" << std::endl;
						__stdlog__({ "Proof found in Module_0001 via Fast-Forward (FF)" });
						auto iProofStep2DStdStrVec = RHSRouteHistoryMap[HashKeyStdStr].begin();
						const auto iProofStepEND = RHSRouteHistoryMap[HashKeyStdStr].end();
						const auto& LHS_SOLU = Theorem_0001[LHS];
						// Skip root datum //
						for (++iProofStep2DStdStrVec; iProofStep2DStdStrVec != iProofStepEND; ++iProofStep2DStdStrVec){
						    (*iProofStep2DStdStrVec)[LHS] = LHS_SOLU;
							TempProofStep3DStdStrVec_0001.emplace_back(*iProofStep2DStdStrVec);
						}

						// Is the FF queue still empty? //
						if (FastForwardTask_Thread.empty()) {
							bFastForwardFlag = true;
							FastForwardTask_Thread.push(TempProofStep3DStdStrVec_0001);
							QED = true;
							break;
						}
					}
                    
                    Tasks_Thread.push(TempProofStep3DStdStrVec_0001);
                }
                
                if (rhs_reduce_flag = SubnetFound(Theorem[RHS], Axiom[LHS], Axiom[RHS], Theorem_0002[RHS]))
                {
                    //__stdlog__({"rhs_reduce_ via ",axiom_name, i});
                    Theorem_0002[opcode_field][opcode] = OpcodeStruct.rhs_reduce;;
                    Theorem_0002[opcode_field][axiom_label] = axiom_name;
                    Theorem_0002[opcode_field][guid_UInt64] = i;
                    
                    PROOF_STEP TempProofStep3DStdStrVec_0002 { TempProofStep3DStdStrVec };
                    TempProofStep3DStdStrVec_0002.emplace_back(Theorem_0002);

					// Commit for later fast-forward //
					const std::string HashKeyStdStr = ComputeHash(Theorem_0002[RHS]);
					if (RHSRouteHistoryMap.find(HashKeyStdStr) == RHSRouteHistoryMap.end())
						RHSRouteHistoryMap.emplace(HashKeyStdStr, TempProofStep3DStdStrVec_0002);

					// Attempt fast-forward //
					if (LHSRouteHistoryMap.find(HashKeyStdStr) != LHSRouteHistoryMap.end()) {
                        std::cout << "Proof found in Module_0002 via Fast-Forward (FF)" << std::endl;
						__stdlog__({ "Proof found in Module_0002 via Fast-Forward (FF)" });
						auto iProofStep2DStdStrVec = LHSRouteHistoryMap[HashKeyStdStr].begin();
						const auto iProofStepEND = LHSRouteHistoryMap[HashKeyStdStr].end();
						const auto& RHS_SOLU = Theorem_0002[RHS];
						// Skip root datum //
						for (++iProofStep2DStdStrVec; iProofStep2DStdStrVec != iProofStepEND; ++iProofStep2DStdStrVec){
						    (*iProofStep2DStdStrVec)[RHS] = RHS_SOLU;
							TempProofStep3DStdStrVec_0002.emplace_back(*iProofStep2DStdStrVec);
						}
						
						// Is the FF queue still empty? //
						if (FastForwardTask_Thread.empty()) {
							bFastForwardFlag = true;
							FastForwardTask_Thread.push(TempProofStep3DStdStrVec_0002);
							QED = true;
							break;
						}
					}
					
                    Tasks_Thread.push(TempProofStep3DStdStrVec_0002);
                }
                
                if (rhs_expand_flag = SubnetFound(Theorem[RHS], Axiom[RHS], Axiom[LHS], Theorem_0003[RHS]))
                {
                    //__stdlog__({ "rhs_expand_ via ",axiom_name, i });
                    Theorem_0003[opcode_field][opcode] = OpcodeStruct.rhs_expand;;
                    Theorem_0003[opcode_field][axiom_label] = axiom_name;
                    Theorem_0003[opcode_field][guid_UInt64] = i;
                    
                    PROOF_STEP TempProofStep3DStdStrVec_0003 { TempProofStep3DStdStrVec };
                    TempProofStep3DStdStrVec_0003.emplace_back(Theorem_0003);

					// Commit for later fast-forward //
					const std::string HashKeyStdStr = ComputeHash(Theorem_0003[RHS]);
					if (RHSRouteHistoryMap.find(HashKeyStdStr) == RHSRouteHistoryMap.end())
						RHSRouteHistoryMap.emplace(HashKeyStdStr, TempProofStep3DStdStrVec_0003);

					// Attempt fast-forward //
					if (LHSRouteHistoryMap.find(HashKeyStdStr) != LHSRouteHistoryMap.end()) {
                        std::cout << "Proof found in Module_0003 via Fast-Forward (FF)" << std::endl;
						__stdlog__({ "Proof found in Module_0003 via Fast-Forward (FF)" });
						auto iProofStep2DStdStrVec = LHSRouteHistoryMap[HashKeyStdStr].begin();
						const auto iProofStepEND = LHSRouteHistoryMap[HashKeyStdStr].end();
						const auto& RHS_SOLU = Theorem_0003[RHS];
						// Skip root datum //
						for (++iProofStep2DStdStrVec; iProofStep2DStdStrVec != iProofStepEND; ++iProofStep2DStdStrVec){
						    (*iProofStep2DStdStrVec)[RHS] = RHS_SOLU;
							TempProofStep3DStdStrVec_0003.emplace_back(*iProofStep2DStdStrVec);
						}

						// Is the FF queue still empty? //
						if (FastForwardTask_Thread.empty()) {
							bFastForwardFlag = true;
							FastForwardTask_Thread.push(TempProofStep3DStdStrVec_0003);
							QED = true;
							break;
						}
					}
					
                    Tasks_Thread.push(TempProofStep3DStdStrVec_0003);
                }
                
                // Advanced Rewrites //
                
                if (lhs_reduce_flag && rhs_reduce_flag)
                {
                   // __stdlog__({ "lhs_reduce + rhs_reduce_ via ",axiom_name, i });
                    Theorem_0004[opcode_field][opcode] = OpcodeStruct.lhs_reduce +  OpcodeStruct.rhs_reduce;;
                    Theorem_0004[opcode_field][axiom_label] = axiom_name;
                    Theorem_0004[opcode_field][guid_UInt64] = i;
                    
                    Theorem_0004[LHS] = Theorem_0000[LHS];
                    Theorem_0004[RHS] = Theorem_0002[RHS];
                    
                    PROOF_STEP TempProofStep3DStdStrVec_0004 { TempProofStep3DStdStrVec };
                    TempProofStep3DStdStrVec_0004.emplace_back(Theorem_0004);
                    
                    Tasks_Thread.push(TempProofStep3DStdStrVec_0004);
                }
                
                if (lhs_reduce_flag && rhs_expand_flag)
                {
                   // __stdlog__({ "lhs_expand_ + rhs_expand_ via ",axiom_name, i });
                    Theorem_0005[opcode_field][opcode] = OpcodeStruct.lhs_reduce +  OpcodeStruct.rhs_expand;;
                    Theorem_0005[opcode_field][axiom_label] = axiom_name;
                    Theorem_0005[opcode_field][guid_UInt64] = i;
                    
                    Theorem_0005[LHS] = Theorem_0000[LHS];
                    Theorem_0005[RHS] = Theorem_0003[RHS];
                    
                    PROOF_STEP TempProofStep3DStdStrVec_0005 { TempProofStep3DStdStrVec };
                    TempProofStep3DStdStrVec_0005.emplace_back(Theorem_0005);
                    
                    Tasks_Thread.push(TempProofStep3DStdStrVec_0005);
                }
                
                if (lhs_expand_flag && rhs_reduce_flag)
                {
                   // __stdlog__({ "lhs_expand_ + rhs_reduce_ via ",axiom_name, i });
                    Theorem_0006[opcode_field][opcode] = OpcodeStruct.lhs_expand +  OpcodeStruct.rhs_reduce;;
                    Theorem_0006[opcode_field][axiom_label] = axiom_name;
                    Theorem_0006[opcode_field][guid_UInt64] = i;
                    
                    Theorem_0006[LHS] = Theorem_0001[LHS];
                    Theorem_0006[RHS] = Theorem_0002[RHS];
                    
                    PROOF_STEP TempProofStep3DStdStrVec_0006 { TempProofStep3DStdStrVec };
                    TempProofStep3DStdStrVec_0006.emplace_back(Theorem_0006);
                    
                    Tasks_Thread.push(TempProofStep3DStdStrVec_0006);
                }
                
                if (lhs_expand_flag && rhs_expand_flag)
                {
                    //__stdlog__({ "lhs_expand_ + rhs_expand_ via ",axiom_name, i });
                    Theorem_0007[opcode_field][opcode] = OpcodeStruct.lhs_expand +  OpcodeStruct.rhs_expand;;
                    Theorem_0007[opcode_field][axiom_label] = axiom_name;
                    Theorem_0007[opcode_field][guid_UInt64] = i;
                    
                    Theorem_0007[LHS] = Theorem_0001[LHS];
                    Theorem_0007[RHS] = Theorem_0003[RHS];
                    
                    PROOF_STEP TempProofStep3DStdStrVec_0007 { TempProofStep3DStdStrVec };
                    TempProofStep3DStdStrVec_0007.emplace_back(Theorem_0007);
                    
                    Tasks_Thread.push(TempProofStep3DStdStrVec_0007);
                }
                
            } // end for(...InProofLibrary3DStdStrVec)
            
        } // end while  (!Tasks_Thread.empty() && !QED)
        // *** End Core Proof Engine (Loop) *** //

        if (QED)
            std::cout << "\n\nQ.E.D.\n";
        else
            std::cout << "Proof not found";

        __stdtraceout__("Prove");
    }; // end Prove(...)
	
} // end namespace Proof

#include <string>
#include <chrono>
//#include <Euclid.h>
/*
int main()
{
    Euclid_Prover::__stdtracein__("Main");

    const auto start_time_chrono = std::chrono::high_resolution_clock::now();

    Euclid_Prover::Prove();

    std::cout << std::endl;
    const auto end_time_chrono = std::chrono::high_resolution_clock::now();
    const auto duration_chrono = std::chrono::duration_cast<std::chrono::nanoseconds>( end_time_chrono - start_time_chrono ).count();
    std::cout << "Total Duration (nanoseconds): " << duration_chrono << std::endl;

    Euclid_Prover::__stdtraceout__("Main");

    //std::string Hold_for_user_input{};
    //std::cin >> Hold_for_user_input;

    return EXIT_SUCCESS;
}
*/