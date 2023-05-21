#pragma once

#include <iostream>
#include <vector>
#include <string>

#include <queue>
#include <chrono>
#include <unordered_map>
#include <mutex>
#include <thread>

namespace Euclid_Prover {

	//#define IOSTREAM_INCLUDED // Comment out to disable all std::cout messages. //

	#ifdef IOSTREAM_INCLUDED
	std::vector<std::string> TraceCallStackStdStrVec{ "EuclidProver" };
	#endif

	void __stdlog__(const std::initializer_list<std::string>& msg, const bool AddNewlineFlag = true)
	{
		// Check if the iostream library is included.
        #ifdef IOSTREAM_INCLUDED
		auto it = msg.begin();
		auto IT = msg.end();
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
		const std::size_t I = TraceCallStackStdStrVec.size();
		std::cout << TraceCallStackStdStrVec[0];
		for (std::size_t i = 1; i < I; ++i)
		{
			std::cout << " >> " << TraceCallStackStdStrVec[i];
		}
		std::cout << std::endl;
	    #endif
	};

	void __stdtraceout__(const std::string& msg)
	{
		// Check if the iostream library is included.
	#ifdef IOSTREAM_INCLUDED
		TraceCallStackStdStrVec.pop_back();
		const std::size_t I = TraceCallStackStdStrVec.size();
		std::string buff{ TraceCallStackStdStrVec[0] };
		for (std::size_t i = 1; i < I; ++i)
		{
			buff.append(" >> " + TraceCallStackStdStrVec[i]);
		}
		std::cout << buff << " << " << msg << std::endl;
		std::cout << buff << std::endl;
	#endif
	};

	/**
		AUTHOR:
			Seagat2011 (https://github.com/Seagat2011 )

		TITLE:
			EuclidProver.h

		DESCRIPTION:
			Term rewrite engine.

		TEST CASE 246:
			nanoseconds elapsed: +5 min

		REFERENCES
			OpenAI GPT-4-32k-0314 ( { max_tokens:32000, temperature:1.0, top_p:1.0, N:1,
				stream:false, logprobs:NULL, echo:false, stop:NULL, presence_penalty:0,
				frequency_penalty:0, best_of:1, logit_bias:NULL } )

		COMPATIBILITY
			Windows 11+ x86i64
	*/
	
	void PrintPath(const std::vector<std::vector<std::vector<std::size_t>>>& OutProofStep3DStdStrVec)
	{
		__stdtracein__("PrintPath");
	    for (const std::vector<std::vector<std::size_t>>& x : OutProofStep3DStdStrVec)
	    {
	        __stdlog__({ "{" }, false);
    	    for (const std::vector<std::size_t>& y : x)
    	    {
    	        __stdlog__({ "{" }, false);
    	       for (const std::size_t& z : y)
        	    {
        	        __stdlog__({ " ", std::to_string(z), " " }, false);
        	    } 
    	        __stdlog__({ "}, " }, false);
    	    }
	        __stdlog__({ "}" });
	    }
		__stdtraceout__("PrintPath");
	}
	
	std::string ComputeHash(const std::vector<std::size_t>& Theorem_Src)
	{
		__stdtracein__("ComputeHash");
		std::string retbuff {"{"};
		
	       for (const std::size_t& z : Theorem_Src)
    	    {
    	        retbuff += std::to_string(z);
    	    }
            
        retbuff += "}";
	    
		__stdtraceout__("ComputeHash");
		return retbuff;
	}

	bool SubnetFound
	(
		const std::vector<std::size_t>& Theorem_Src,
		const std::vector<std::size_t>& Axiom_Src,
		const std::vector<std::size_t>& Axiom_Dest,
		std::vector<std::size_t>& Theorem_Dest
	)
	{
		__stdtracein__("SubnetFound");
		const std::size_t& th_size = Theorem_Src.size();
		const std::size_t& ax_size = Axiom_Src.size();

		bool SubnetFoundFlag{};
		
		if (ax_size <= th_size)
		{
			std::size_t i_ax{};

			for (const std::size_t& th_tok : Theorem_Src)
			{
			    const bool MatchFoundFlag = (!SubnetFoundFlag && (Axiom_Src[i_ax] == th_tok));
				if (MatchFoundFlag) {
					++i_ax;
					const bool LocalSubnetFoundFlag = ( i_ax == ax_size );
					if (LocalSubnetFoundFlag)
					{
						for (const std::size_t ax_tok : Axiom_Dest) {
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

        const std::size_t axiom_name = 10003;//"Axiom_";
        const std::size_t theorem_name = 10002;//"Theorem_";

        class OPCODESTRUCT {
        public:
            const std::size_t lhs_reduce = 10004;//"lhs_reduce ";
            const std::size_t lhs_expand = 10005;//"lhs_expand ";
            const std::size_t rhs_reduce = 10006;//"rhs_reduce ";
            const std::size_t rhs_expand = 10007;//"rhs_expand ";
        };

        OPCODESTRUCT OpcodeStruct;

        using PROOF_STEP = std::vector<std::vector<std::vector<std::size_t>>>;
        using PROOF_REWRITE = std::vector<std::vector<std::size_t>>;

        // input //
        
        std::vector<std::vector<std::vector<std::size_t>>> InProofLibrary3DStdStrVec =
        
        {
            // {{lhs},{rhs}} // 
            /*
            {{"1", "+", "1", "+", "1", "+", "1"},{"4"}},
            {{"1", "+", "1"},{"2"}},
            {{"2", "+", "2"},{"4"}}
            */
             {
                 {
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001, 1, 10001,
         1, 10001, 1, 10001, 1
     }, // lhs
     {
         246
     } }, // rhs
{ { 1, 10001, 1 }, { 2 } },
{ { 1, 10001, 2 }, { 3 } },
{ { 2, 10001, 2 }, { 4 } },
{ { 1, 10001, 4 }, { 5 } },
{ { 3, 10001, 3 }, { 6 } },
{ { 1, 10001, 6 }, { 7 } },
{ { 4, 10001, 4 }, { 8 } },
{ { 1, 10001, 8 }, { 9 } },
{ { 5, 10001, 5 }, { 10 } },
{ { 1, 10001, 10 }, { 11 } },
{ { 6, 10001, 6 }, { 12 } },
{ { 1, 10001, 12 }, { 13 } },
{ { 7, 10001, 7 }, { 14 } },
{ { 1, 10001, 14 }, { 15 } },
{ { 8, 10001, 8 }, { 16 } },
{ { 1, 10001, 16 }, { 17 } },
{ { 9, 10001, 9 }, { 18 } },
{ { 1, 10001, 18 }, { 19 } },
{ { 10, 10001, 10 }, { 20 } },
{ { 1, 10001, 20 }, { 21 } },
{ { 11, 10001, 11 }, { 22 } },
{ { 1, 10001, 22 }, { 23 } },
{ { 12, 10001, 12 }, { 24 } },
{ { 1, 10001, 24 }, { 25 } },
{ { 13, 10001, 13 }, { 26 } },
{ { 1, 10001, 26 }, { 27 } },
{ { 14, 10001, 14 }, { 28 } },
{ { 1, 10001, 28 }, { 29 } },
{ { 15, 10001, 15 }, { 30 } },
{ { 1, 10001, 30 }, { 31 } },
{ { 16, 10001, 16 }, { 32 } },
{ { 1, 10001, 32 }, { 33 } },
{ { 17, 10001, 17 }, { 34 } },
{ { 1, 10001, 34 }, { 35 } },
{ { 18, 10001, 18 }, { 36 } },
{ { 1, 10001, 36 }, { 37 } },
{ { 19, 10001, 19 }, { 38 } },
{ { 1, 10001, 38 }, { 39 } },
{ { 20, 10001, 20 }, { 40 } },
{ { 1, 10001, 40 }, { 41 } },
{ { 21, 10001, 21 }, { 42 } },
{ { 1, 10001, 42 }, { 43 } },
{ { 22, 10001, 22 }, { 44 } },
{ { 1, 10001, 44 }, { 45 } },
{ { 23, 10001, 23 }, { 46 } },
{ { 1, 10001, 46 }, { 47 } },
{ { 24, 10001, 24 }, { 48 } },
{ { 1, 10001, 48 }, { 49 } },
{ { 25, 10001, 25 }, { 50 } },
{ { 1, 10001, 50 }, { 51 } },
{ { 26, 10001, 26 }, { 52 } },
{ { 1, 10001, 52 }, { 53 } },
{ { 27, 10001, 27 }, { 54 } },
{ { 1, 10001, 54 }, { 55 } },
{ { 28, 10001, 28 }, { 56 } },
{ { 1, 10001, 56 }, { 57 } },
{ { 29, 10001, 29 }, { 58 } },
{ { 1, 10001, 58 }, { 59 } },
{ { 30, 10001, 30 }, { 60 } },
{ { 1, 10001, 60 }, { 61 } },
{ { 31, 10001, 31 }, { 62 } },
{ { 1, 10001, 62 }, { 63 } },
{ { 32, 10001, 32 }, { 64 } },
{ { 1, 10001, 64 }, { 65 } },
{ { 33, 10001, 33 }, { 66 } },
{ { 1, 10001, 66 }, { 67 } },
{ { 34, 10001, 34 }, { 68 } },
{ { 1, 10001, 68 }, { 69 } },
{ { 35, 10001, 35 }, { 70 } },
{ { 1, 10001, 70 }, { 71 } },
{ { 36, 10001, 36 }, { 72 } },
{ { 1, 10001, 72 }, { 73 } },
{ { 37, 10001, 37 }, { 74 } },
{ { 1, 10001, 74 }, { 75 } },
{ { 38, 10001, 38 }, { 76 } },
{ { 1, 10001, 76 }, { 77 } },
{ { 39, 10001, 39 }, { 78 } },
{ { 1, 10001, 78 }, { 79 } },
{ { 40, 10001, 40 }, { 80 } },
{ { 1, 10001, 80 }, { 81 } },
{ { 41, 10001, 41 }, { 82 } },
{ { 1, 10001, 82 }, { 83 } },
{ { 42, 10001, 42 }, { 84 } },
{ { 1, 10001, 84 }, { 85 } },
{ { 43, 10001, 43 }, { 86 } },
{ { 1, 10001, 86 }, { 87 } },
{ { 44, 10001, 44 }, { 88 } },
{ { 1, 10001, 88 }, { 89 } },
{ { 45, 10001, 45 }, { 90 } },
{ { 1, 10001, 90 }, { 91 } },
{ { 46, 10001, 46 }, { 92 } },
{ { 1, 10001, 92 }, { 93 } },
{ { 47, 10001, 47 }, { 94 } },
{ { 1, 10001, 94 }, { 95 } },
{ { 48, 10001, 48 }, { 96 } },
{ { 1, 10001, 96 }, { 97 } },
{ { 49, 10001, 49 }, { 98 } },
{ { 1, 10001, 98 }, { 99 } },
{ { 50, 10001, 50 }, { 100 } },
{ { 1, 10001, 100 }, { 101 } },
{ { 51, 10001, 51 }, { 102 } },
{ { 1, 10001, 102 }, { 103 } },
{ { 52, 10001, 52 }, { 104 } },
{ { 1, 10001, 104 }, { 105 } },
{ { 53, 10001, 53 }, { 106 } },
{ { 1, 10001, 106 }, { 107 } },
{ { 54, 10001, 54 }, { 108 } },
{ { 1, 10001, 108 }, { 109 } },
{ { 55, 10001, 55 }, { 110 } },
{ { 1, 10001, 110 }, { 111 } },
{ { 56, 10001, 56 }, { 112 } },
{ { 1, 10001, 112 }, { 113 } },
{ { 57, 10001, 57 }, { 114 } },
{ { 1, 10001, 114 }, { 115 } },
{ { 58, 10001, 58 }, { 116 } },
{ { 1, 10001, 116 }, { 117 } },
{ { 59, 10001, 59 }, { 118 } },
{ { 1, 10001, 118 }, { 119 } },
{ { 60, 10001, 60 }, { 120 } },
{ { 1, 10001, 120 }, { 121 } },
{ { 61, 10001, 61 }, { 122 } },
{ { 1, 10001, 122 }, { 123 } },
{ { 62, 10001, 62 }, { 124 } },
{ { 1, 10001, 124 }, { 125 } },
{ { 63, 10001, 63 }, { 126 } },
{ { 1, 10001, 126 }, { 127 } },
{ { 64, 10001, 64 }, { 128 } },
{ { 1, 10001, 128 }, { 129 } },
{ { 65, 10001, 65 }, { 130 } },
{ { 1, 10001, 130 }, { 131 } },
{ { 66, 10001, 66 }, { 132 } },
{ { 1, 10001, 132 }, { 133 } },
{ { 67, 10001, 67 }, { 134 } },
{ { 1, 10001, 134 }, { 135 } },
{ { 68, 10001, 68 }, { 136 } },
{ { 1, 10001, 136 }, { 137 } },
{ { 69, 10001, 69 }, { 138 } },
{ { 1, 10001, 138 }, { 139 } },
{ { 70, 10001, 70 }, { 140 } },
{ { 1, 10001, 140 }, { 141 } },
{ { 71, 10001, 71 }, { 142 } },
{ { 1, 10001, 142 }, { 143 } },
{ { 72, 10001, 72 }, { 144 } },
{ { 1, 10001, 144 }, { 145 } },
{ { 73, 10001, 73 }, { 146 } },
{ { 1, 10001, 146 }, { 147 } },
{ { 74, 10001, 74 }, { 148 } },
{ { 1, 10001, 148 }, { 149 } },
{ { 75, 10001, 75 }, { 150 } },
{ { 1, 10001, 150 }, { 151 } },
{ { 76, 10001, 76 }, { 152 } },
{ { 1, 10001, 152 }, { 153 } },
{ { 77, 10001, 77 }, { 154 } },
{ { 1, 10001, 154 }, { 155 } },
{ { 78, 10001, 78 }, { 156 } },
{ { 1, 10001, 156 }, { 157 } },
{ { 79, 10001, 79 }, { 158 } },
{ { 1, 10001, 158 }, { 159 } },
{ { 80, 10001, 80 }, { 160 } },
{ { 1, 10001, 160 }, { 161 } },
{ { 81, 10001, 81 }, { 162 } },
{ { 1, 10001, 162 }, { 163 } },
{ { 82, 10001, 82 }, { 164 } },
{ { 1, 10001, 164 }, { 165 } },
{ { 83, 10001, 83 }, { 166 } },
{ { 1, 10001, 166 }, { 167 } },
{ { 84, 10001, 84 }, { 168 } },
{ { 1, 10001, 168 }, { 169 } },
{ { 85, 10001, 85 }, { 170 } },
{ { 1, 10001, 170 }, { 171 } },
{ { 86, 10001, 86 }, { 172 } },
{ { 1, 10001, 172 }, { 173 } },
{ { 87, 10001, 87 }, { 174 } },
{ { 1, 10001, 174 }, { 175 } },
{ { 88, 10001, 88 }, { 176 } },
{ { 1, 10001, 176 }, { 177 } },
{ { 89, 10001, 89 }, { 178 } },
{ { 1, 10001, 178 }, { 179 } },
{ { 90, 10001, 90 }, { 180 } },
{ { 1, 10001, 180 }, { 181 } },
{ { 91, 10001, 91 }, { 182 } },
{ { 1, 10001, 182 }, { 183 } },
{ { 92, 10001, 92 }, { 184 } },
{ { 1, 10001, 184 }, { 185 } },
{ { 93, 10001, 93 }, { 186 } },
{ { 1, 10001, 186 }, { 187 } },
{ { 94, 10001, 94 }, { 188 } },
{ { 1, 10001, 188 }, { 189 } },
{ { 95, 10001, 95 }, { 190 } },
{ { 1, 10001, 190 }, { 191 } },
{ { 96, 10001, 96 }, { 192 } },
{ { 1, 10001, 192 }, { 193 } },
{ { 97, 10001, 97 }, { 194 } },
{ { 1, 10001, 194 }, { 195 } },
{ { 98, 10001, 98 }, { 196 } },
{ { 1, 10001, 196 }, { 197 } },
{ { 99, 10001, 99 }, { 198 } },
{ { 1, 10001, 198 }, { 199 } },
{ { 100, 10001, 100 }, { 200 } },
{ { 1, 10001, 200 }, { 201 } },
{ { 101, 10001, 101 }, { 202 } },
{ { 1, 10001, 202 }, { 203 } },
{ { 102, 10001, 102 }, { 204 } },
{ { 1, 10001, 204 }, { 205 } },
{ { 103, 10001, 103 }, { 206 } },
{ { 1, 10001, 206 }, { 207 } },
{ { 104, 10001, 104 }, { 208 } },
{ { 1, 10001, 208 }, { 209 } },
{ { 105, 10001, 105 }, { 210 } },
{ { 1, 10001, 210 }, { 211 } },
{ { 106, 10001, 106 }, { 212 } },
{ { 1, 10001, 212 }, { 213 } },
{ { 107, 10001, 107 }, { 214 } },
{ { 1, 10001, 214 }, { 215 } },
{ { 108, 10001, 108 }, { 216 } },
{ { 1, 10001, 216 }, { 217 } },
{ { 109, 10001, 109 }, { 218 } },
{ { 1, 10001, 218 }, { 219 } },
{ { 110, 10001, 110 }, { 220 } },
{ { 1, 10001, 220 }, { 221 } },
{ { 111, 10001, 111 }, { 222 } },
{ { 1, 10001, 222 }, { 223 } },
{ { 112, 10001, 112 }, { 224 } },
{ { 1, 10001, 224 }, { 225 } },
{ { 113, 10001, 113 }, { 226 } },
{ { 1, 10001, 226 }, { 227 } },
{ { 114, 10001, 114 }, { 228 } },
{ { 1, 10001, 228 }, { 229 } },
{ { 115, 10001, 115 }, { 230 } },
{ { 1, 10001, 230 }, { 231 } },
{ { 116, 10001, 116 }, { 232 } },
{ { 1, 10001, 232 }, { 233 } },
{ { 117, 10001, 117 }, { 234 } },
{ { 1, 10001, 234 }, { 235 } },
{ { 118, 10001, 118 }, { 236 } },
{ { 1, 10001, 236 }, { 237 } },
{ { 119, 10001, 119 }, { 238 } },
{ { 1, 10001, 238 }, { 239 } },
{ { 120, 10001, 120 }, { 240 } },
{ { 1, 10001, 240 }, { 241 } },
{ { 121, 10001, 121 }, { 242 } },
{ { 1, 10001, 242 }, { 243 } },
{ { 122, 10001, 122 }, { 244 } },
{ { 1, 10001, 244 }, { 245 } },
{ { 123, 10001, 123 }, { 246 } }
        };
        
        PROOF_STEP OutProofStep3DStdStrVec;

        OutProofStep3DStdStrVec.emplace_back(InProofLibrary3DStdStrVec[0]);
        OutProofStep3DStdStrVec[0].push_back ({ 0, theorem_name, 0 });
        
        PrintPath(OutProofStep3DStdStrVec);

        /*
            // internal representation //
            std::vector<
            std::vector<
            std::vector<std::string>>> OutProofStep3DStdStrVec =
            {
                // {{opcode},{lhs},{rhs}} //
                {{"1","+","1","+","1","+","1"},{"4"},{"root","Theorem_","0"}}
            };
        */

		bool bFastForwardFlag{};
		
        std::unordered_map<std::string, PROOF_STEP>
        LHSRouteHistoryMap, RHSRouteHistoryMap;
        
        std::priority_queue<PROOF_STEP> Tasks_Thread, FastForwardTask_Thread;

        Tasks_Thread.push(OutProofStep3DStdStrVec);

        // *** Core Proof Engine (Loop) *** //
        while (!Tasks_Thread.empty() && !QED)
        {
            PROOF_STEP TempProofStep3DStdStrVec { !bFastForwardFlag ? Tasks_Thread.top() : FastForwardTask_Thread.top() };
            
            !bFastForwardFlag ? Tasks_Thread.pop() : FastForwardTask_Thread.pop() ;
            
		    bFastForwardFlag = false;
            
            const PROOF_REWRITE& Theorem{ TempProofStep3DStdStrVec.back() };
            
            const std::size_t I = InProofLibrary3DStdStrVec.size();
            for(std::size_t i = 1; i < I; ++i)
            {
                const
                std::vector<
                std::vector<std::size_t>>& Axiom = InProofLibrary3DStdStrVec[i];
                
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
                
                bool lhs_reduce_flag;
                bool lhs_expand_flag;
                bool rhs_reduce_flag;
                bool rhs_expand_flag;
    
                if (lhs_reduce_flag = SubnetFound(Theorem[LHS], Axiom[LHS], Axiom[RHS], Theorem_0000[LHS]))
                {
                    //__stdlog__({"lhs_reduce_ via ",axiom_name, i});
                    Theorem_0000[opcode_field][opcode] = OpcodeStruct.lhs_reduce;;
                    Theorem_0000[opcode_field][axiom_label] = axiom_name;
                    Theorem_0000[opcode_field][guid_UInt64] = i;
                    
                    PROOF_STEP TempProofStep3DStdStrVec_0000 { TempProofStep3DStdStrVec };
                    TempProofStep3DStdStrVec_0000.emplace_back(Theorem_0000);

					// Commit for later fast-forward //
					const std::string HashKeyStdStr = ComputeHash(Theorem_0000[LHS]);
					if (LHSRouteHistoryMap.find(HashKeyStdStr) == LHSRouteHistoryMap.end())
						LHSRouteHistoryMap.emplace(HashKeyStdStr, TempProofStep3DStdStrVec_0000);

					// Attempt fast-forward //
					if (RHSRouteHistoryMap.find(HashKeyStdStr) != RHSRouteHistoryMap.end()) {
						//std::cout << "Proof found in Module_0000 via Fast-Forward (FF)" << " {" << Theorem_0000[LHS].str() << ", " << Theorem_0000[LHS].str() << "}" << std::endl;
						__stdlog__({ "Proof found in Module_0000 via Fast-Forward (FF)" });
						auto iProofStep2DStdStrVec = RHSRouteHistoryMap[HashKeyStdStr].begin();
						const auto iProofStepEND = RHSRouteHistoryMap[HashKeyStdStr].end();
						const auto& LHS_SOLU = Theorem_0000[LHS];
						// Skip root datum //
						for (++iProofStep2DStdStrVec; iProofStep2DStdStrVec != iProofStepEND; ++iProofStep2DStdStrVec){
						    (*iProofStep2DStdStrVec)[LHS] = LHS_SOLU;
							TempProofStep3DStdStrVec_0000.emplace_back(*iProofStep2DStdStrVec);
						}

						// Is the FF queue still empty? //
						if (FastForwardTask_Thread.empty()) {
							bFastForwardFlag = true;
							FastForwardTask_Thread.push(TempProofStep3DStdStrVec_0000);
							QED = true;
							break;
						}
					}
                    
                    Tasks_Thread.push(TempProofStep3DStdStrVec_0000);
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
						//std::cout << "Proof found in Module_0001 via Fast-Forward (FF)" << " {" << Theorem_0000[LHS].str() << ", " << Theorem_0000[LHS].str() << "}" << std::endl;
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
						//std::cout << "Proof found in Module_0002 via Fast-Forward (FF)" << " {" << Theorem_0000[LHS].str() << ", " << Theorem_0000[LHS].str() << "}" << std::endl;
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
						//std::cout << "Proof found in Module_0003 via Fast-Forward (FF)" << " {" << Theorem_0000[LHS].str() << ", " << Theorem_0000[LHS].str() << "}" << std::endl;
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
        {
            OutProofStep3DStdStrVec = bFastForwardFlag ? FastForwardTask_Thread.top() : Tasks_Thread.top() ;
            PrintPath(OutProofStep3DStdStrVec);
            std::cout << "\n\nQ.E.D.\n";
        } else {
            std::cout << "Proof not found";
        }
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