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
            std::cout << " > " << TraceCallStackStdStrVec[i];
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
            buff.append(" > " + TraceCallStackStdStrVec[i]);
        }
        std::cout << buff << " < " << msg << std::endl;
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
            nanoseconds elapsed: 147524900

        REFERENCES
            OpenAI GPT-4-32k-0314 ( { max_tokens:32000, temperature:1.0, top_p:1.0, N:1,
                stream:false, logprobs:NULL, echo:false, stop:NULL, presence_penalty:0,
                frequency_penalty:0, best_of:1, logit_bias:NULL } )

        COMPATIBILITY
            Windows 11+ x86i64
    */

    bool SubnetFound
    (
        const std::vector<std::string>& Theorem_Src,
        const std::vector<std::string>& Axiom_Src,
        const std::vector<std::string>& Axiom_Dest,
        std::vector<std::string>& Theorem_Dest
    )
    {
        __stdtracein__("SubnetFound");
        const std::size_t& th_size = Theorem_Src.size();
        const std::size_t& ax_size = Axiom_Src.size();

        bool SubnetFoundFlag{};

        if (ax_size <= th_size)
        {
            bool LocalSubnetFoundFlag{};

            std::size_t i_ax{};

            for (const std::string& th_tok : Theorem_Src)
            {
                if (Axiom_Src[i_ax] == th_tok && !LocalSubnetFoundFlag) {
                    ++i_ax;
                    LocalSubnetFoundFlag = ( i_ax == ax_size );
                    if (LocalSubnetFoundFlag)
                    {
                        for (const std::string ax_tok : Axiom_Dest) {
                            Theorem_Dest.emplace_back(ax_tok);
                        }
                        SubnetFoundFlag = true;
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

        using PROOF_STEP = std::vector<std::vector<std::vector<std::string>>>;

        // input //
        std::vector<std::vector<std::vector<std::string>>> InProofLibrary3DStdStrVec =
        {
            // {{lhs},{rhs}} //
            {{"1","+","1","+","1","+","1"},{"4"}}, // Theorem_0 //	
            {{"1","+","1"},{"2"}},	// Axiom_1 //	
            {{"2","+","2"},{"4"}}	// Axiom_2 //
        };

        PROOF_STEP OutProofStep3DStdStrVec;

        OutProofStep3DStdStrVec.emplace_back(InProofLibrary3DStdStrVec[0]);
        OutProofStep3DStdStrVec[0].push_back({ "root", theorem_name, "0" });

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

        std::priority_queue<PROOF_STEP> Tasks_Thread;

        Tasks_Thread.push(OutProofStep3DStdStrVec);

        // *** Core Proof Engine (Loop) *** //
        while (!Tasks_Thread.empty() && !QED)
        {
            PROOF_STEP TempProofStep3DStdStrVec{ Tasks_Thread.top() };

            Tasks_Thread.pop();

            const
                std::vector<
                std::vector<std::string>>&Theorem{ TempProofStep3DStdStrVec.back() };

            if (Theorem[LHS] == Theorem[RHS])
            {
                __stdlog__({ " Proof found " });
                QED = true;
            } else {
                const std::size_t I = InProofLibrary3DStdStrVec.size();
                for (std::size_t i = 1; i < I; ++i)
                {
                    const
                        std::vector<
                        std::vector<std::string>>&Axiom = InProofLibrary3DStdStrVec[i];

                    std::vector<
                        std::vector<std::string>>
                        Theorem_0000{ Theorem },
                        Theorem_0001{ Theorem },
                        Theorem_0002{ Theorem },
                        Theorem_0003{ Theorem },
                        Theorem_0004{ Theorem };

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
                        Theorem_0000[opcode_field][opcode] = OpcodeStruct.lhs_reduce;
                        Theorem_0000[opcode_field][axiom_label] = axiom_name;
                        Theorem_0000[opcode_field][guid_UInt64] = std::to_string(i);

                        PROOF_STEP TempProofStep3DStdStrVec_0000{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0000.emplace_back(Theorem_0000);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0000);
                    }

                    if (lhs_expand_flag = SubnetFound(Theorem[LHS], Axiom[RHS], Axiom[LHS], Theorem_0001[LHS]))
                    {
                        Theorem_0001[opcode_field][opcode] = OpcodeStruct.lhs_expand;
                        Theorem_0001[opcode_field][axiom_label] = axiom_name;
                        Theorem_0001[opcode_field][guid_UInt64] = std::to_string(i);

                        PROOF_STEP TempProofStep3DStdStrVec_0001{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0001.emplace_back(Theorem_0001);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0001);
                    }

                    if (rhs_reduce_flag = SubnetFound(Theorem[RHS], Axiom[LHS], Axiom[RHS], Theorem_0002[RHS]))
                    {
                        Theorem_0002[opcode_field][opcode] = OpcodeStruct.rhs_reduce;
                        Theorem_0002[opcode_field][axiom_label] = axiom_name;
                        Theorem_0002[opcode_field][guid_UInt64] = std::to_string(i);

                        PROOF_STEP TempProofStep3DStdStrVec_0002{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0002.emplace_back(Theorem_0002);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0002);
                    }

                    if (rhs_expand_flag = SubnetFound(Theorem[RHS], Axiom[RHS], Axiom[LHS], Theorem_0003[RHS]))
                    {
                        Theorem_0003[opcode_field][opcode] = OpcodeStruct.rhs_expand;
                        Theorem_0003[opcode_field][axiom_label] = axiom_name;
                        Theorem_0003[opcode_field][guid_UInt64] = std::to_string(i);

                        PROOF_STEP TempProofStep3DStdStrVec_0003{ TempProofStep3DStdStrVec };
                        TempProofStep3DStdStrVec_0003.emplace_back(Theorem_0003);

                        Tasks_Thread.push(TempProofStep3DStdStrVec_0003);
                    }

                } // end for(...InProofLibrary3DStdStrVec)

            } // end if (Theorem[LHS] == Theorem[RHS])

        } // end while  (!Tasks_Thread.empty() && !QED)
        // *** End Core Proof Engine (Loop) *** //

        __stdlog__({ ( QED ? "" : "\n\nQ.E.D\n" ) });
        __stdtraceout__("Prove");
    }; // end Prove(...)

} // end namespace Proof
