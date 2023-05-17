#pragma once

#include <iostream>
#include <vector>
#include <string>

#define IOSTREAM_INCLUDED // Comment out to disable all std::cout messages. //

#ifdef IOSTREAM_INCLUDED
std::vector<std::string> TraceCallStackStdStrVec{ "EuclidProver" };
#endif

void __stdlog__(const std::initializer_list<std::string>& msg, const bool AddNewlineFlag = true)
{
    // Check if the iostream library is included.
    auto it = msg.begin();
    auto IT = msg.end();
    std::cout << *it;
    ++it; // Advance the iterator by 1 position //
    for (it; it != IT; ++it)
    {
        std::cout << " " << *it;
    }
    if (AddNewlineFlag)
        std::cout << std::endl;
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

#include <cstdlib>
#include <queue>
#include <chrono>
#include <unordered_map>
#include <mutex>
#include <thread>

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
    const std::vector<std::string>& Theorem,
    const std::vector<std::string>& Axiom_Src,
    const std::vector<std::string>& Axiom_Dest,
    std::vector<std::string>& Theorem_0000
)
{
    __stdtracein__("SubnetFound");
    const std::size_t ax_size = Axiom_Src.size();

    bool SubnetFoundFlag{};

    if (ax_size <= Theorem_0000.size())
    {
        bool LocalSubnetFoundFlag{};

        std::size_t i_ax{};

        for (const std::string th_tok : Theorem)
        {
            if (Axiom_Src[i_ax] == th_tok && !LocalSubnetFoundFlag) {
                ++i_ax;
                LocalSubnetFoundFlag = ( i_ax == ax_size );
                if (LocalSubnetFoundFlag)
                {
                    for (const std::string ax_tok : Axiom_Dest) {
                        Theorem_0000.emplace_back(ax_tok);
                        __stdlog__({ ax_tok + " " }, false);
                    }
                    SubnetFoundFlag = true;
                    __stdlog__({ "" });
                }
            } else {
                i_ax = 0;
                Theorem_0000.emplace_back(th_tok);
            }
        }
    }
    __stdtraceout__("SubnetFound");
    return SubnetFoundFlag;
};

int main()
{
    __stdtracein__("Main");
    auto Prove = [&] () -> void // Total Duration (nanoseconds): 130731 //
    {
        __stdtracein__("Prove");
        bool QED{};

        constexpr int LHS = 1;
        constexpr int RHS = 2;
        constexpr int opcode_field = 0;
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
        OutProofStep3DStdStrVec[0].insert(
            OutProofStep3DStdStrVec[0].begin(),
            {
                "root",
                theorem_name,
                "0"
            });

        /*
            // internal representation //
            std::vector<
            std::vector<
            std::vector<std::string>>> OutProofStep3DStdStrVec =
            {
                // {{opcode},{lhs},{rhs}} //
                {{"root","Theorem_","0"},{"1","+","1","+","1","+","1"},{"4"}}
            };
        */

        std::priority_queue<PROOF_STEP> Tasks_Thread;

        Tasks_Thread.push(OutProofStep3DStdStrVec);

        /*
        // internal representation //
        std::priority_queue<
        std::vector<
        std::vector<std::string>>> Tasks_Thread;

        Tasks_Thread.push(
            {
                // {{opcode},{lhs},{rhs}} //
                {{"root","Theorem_","0"},{"1","+","1","+","1","+","1"},{"4"}}
            });
        */

        // *** Core Proof Engine (Loop) *** //
        while (!Tasks_Thread.empty() && !QED)
        {
            PROOF_STEP TempProofStep3DStdStrVec{ Tasks_Thread.top() };

            Tasks_Thread.pop();

            const
                std::vector<
                std::vector<
                std::string>>&Theorem{ TempProofStep3DStdStrVec.back() };

            if (Theorem[LHS] == Theorem[RHS])
            {
                __stdlog__({ "Tentative Proof found" });
                QED = true;
            } else {
                // Add new rewrites to the task queue //
                const std::size_t& I = InProofLibrary3DStdStrVec.size();
                for (std::size_t i = 1; i < I; ++i)
                {
                    std::vector<
                        std::vector<
                        std::string>>

                        Theorem_0000 = Theorem,
                        Theorem_0001 = Theorem,
                        Theorem_0002 = Theorem,
                        Theorem_0003 = Theorem,
                        Theorem_0004 = Theorem;

                    Theorem_0000[LHS].clear();
                    Theorem_0001[LHS].clear();

                    Theorem_0002[RHS].clear();
                    Theorem_0003[RHS].clear();

                    bool lhs_reduce_flag{};
                    bool lhs_expand_flag{};
                    bool rhs_reduce_flag{};
                    bool rhs_expand_flag{};

                    const
                        std::vector<
                        std::vector<std::string>>&

                        Axiom = InProofLibrary3DStdStrVec[i];

                    // basic rewrites //

                    // lhs_reduction //
                    __stdlog__({ "lhs_reduce:" });
                    if (lhs_reduce_flag = SubnetFound(Theorem[LHS], Axiom[LHS], Axiom[RHS], Theorem_0000[LHS]))
                    {
                        Theorem_0000[opcode_field][opcode] = OpcodeStruct.lhs_reduce;
                        Theorem_0000[opcode_field][axiom_label] = axiom_name;
                        Theorem_0000[opcode_field][guid_UInt64] = std::to_string(i);

                        PROOF_STEP ProofStep = TempProofStep3DStdStrVec;

                        ProofStep.emplace_back(Theorem_0000);

                        Tasks_Thread.push(ProofStep);
                    }

                    // lhs_expansion //
                    __stdlog__({ "lhs_expand:" });
                    if (lhs_expand_flag = SubnetFound(Theorem[LHS], Axiom[RHS], Axiom[LHS], Theorem_0001[LHS]))
                    {
                        Theorem_0001[opcode_field][opcode] = OpcodeStruct.lhs_expand;
                        Theorem_0001[opcode_field][axiom_label] = axiom_name;
                        Theorem_0001[opcode_field][guid_UInt64] = std::to_string(i);

                        PROOF_STEP ProofStep = TempProofStep3DStdStrVec;

                        ProofStep.emplace_back(Theorem_0001);

                        Tasks_Thread.push(ProofStep);
                    }

                    // rhs_reduction //
                    __stdlog__({ "rhs_reduce:" });
                    if (rhs_expand_flag = SubnetFound(Theorem[RHS], Axiom[LHS], Axiom[RHS], Theorem_0002[RHS]))
                    {
                        Theorem_0002[opcode_field][opcode] = OpcodeStruct.rhs_reduce;
                        Theorem_0002[opcode_field][axiom_label] = axiom_name;
                        Theorem_0002[opcode_field][guid_UInt64] = std::to_string(i);

                        PROOF_STEP ProofStep = TempProofStep3DStdStrVec;

                        ProofStep.emplace_back(Theorem_0002);

                        Tasks_Thread.push(ProofStep);
                    }

                    // rhs_expansion //
                    __stdlog__({ "rhs_expand:" });
                    if (rhs_reduce_flag = SubnetFound(Theorem[RHS], Axiom[RHS], Axiom[LHS], Theorem_0003[RHS]))
                    {
                        Theorem_0003[opcode_field][opcode] = OpcodeStruct.rhs_expand;
                        Theorem_0003[opcode_field][axiom_label] = axiom_name;
                        Theorem_0003[opcode_field][guid_UInt64] = std::to_string(i);

                        PROOF_STEP ProofStep = TempProofStep3DStdStrVec;

                        ProofStep.emplace_back(Theorem_0003);

                        Tasks_Thread.push(ProofStep);
                    }

                    // advanced rewrites //

                    __stdlog__({ "advanced: lhs_reduce+rhs_reduce:" });
                    if (lhs_reduce_flag && rhs_reduce_flag) {
                        Theorem_0004[opcode_field][opcode] = OpcodeStruct.lhs_expand + " + " + OpcodeStruct.rhs_expand + " via ";
                        Theorem_0004[opcode_field][axiom_label] = axiom_name;
                        Theorem_0004[opcode_field][guid_UInt64] = std::to_string(i);
                        Theorem_0004[LHS] = Theorem_0000[LHS];
                        Theorem_0004[RHS] = Theorem_0003[RHS];

                        PROOF_STEP ProofStep = TempProofStep3DStdStrVec;

                        ProofStep.emplace_back(Theorem_0004);

                        Tasks_Thread.push(ProofStep);
                    }

                    __stdlog__({ "advanced: lhs_reduce+rhs_expand:" });
                    if (lhs_reduce_flag && rhs_expand_flag) {
                        Theorem_0004[opcode_field][opcode] = OpcodeStruct.lhs_expand + " + " + OpcodeStruct.rhs_expand + " via ";
                        Theorem_0004[opcode_field][axiom_label] = axiom_name;
                        Theorem_0004[opcode_field][guid_UInt64] = std::to_string(i);
                        Theorem_0004[LHS] = Theorem_0000[LHS];
                        Theorem_0004[RHS] = Theorem_0002[RHS];

                        PROOF_STEP ProofStep = TempProofStep3DStdStrVec;

                        ProofStep.emplace_back(Theorem_0004);

                        Tasks_Thread.push(ProofStep);
                    }

                    __stdlog__({ "advanced: lhs_expand+rhs_reduce:" });
                    if (lhs_expand_flag && rhs_reduce_flag) {
                        Theorem_0004[opcode_field][opcode] = OpcodeStruct.lhs_expand + " + " + OpcodeStruct.rhs_expand + " via ";
                        Theorem_0004[opcode_field][axiom_label] = axiom_name;
                        Theorem_0004[opcode_field][guid_UInt64] = std::to_string(i);
                        Theorem_0004[LHS] = Theorem_0001[LHS];
                        Theorem_0004[RHS] = Theorem_0003[RHS];

                        PROOF_STEP ProofStep = TempProofStep3DStdStrVec;

                        ProofStep.emplace_back(Theorem_0004);

                        Tasks_Thread.push(ProofStep);
                    }

                    __stdlog__({ "advanced: lhs_expand+rhs_expand:" });
                    if (lhs_expand_flag && rhs_expand_flag) {
                        Theorem_0004[opcode_field][opcode] = OpcodeStruct.lhs_expand + " + " + OpcodeStruct.rhs_expand + " via ";
                        Theorem_0004[opcode_field][axiom_label] = axiom_name;
                        Theorem_0004[opcode_field][guid_UInt64] = std::to_string(i);
                        Theorem_0004[LHS] = Theorem_0001[LHS];
                        Theorem_0004[RHS] = Theorem_0002[RHS];

                        PROOF_STEP ProofStep = TempProofStep3DStdStrVec;

                        ProofStep.emplace_back(Theorem_0004);

                        Tasks_Thread.push(ProofStep);
                    }
                } // end for (...Axiom : InAxiomsStdStrVec)
            } // end test (...Theorem[LHS] == Theorem[RHS])
            __stdlog__({ "Next Round..." });
        } // end for (...!Tasks_Thread.empty() && !QED))
        if (!QED)
        {
            __stdlog__({ "No Proof Found." });
        }
        __stdtraceout__("Prove");
    };

    const auto start_time_chrono = std::chrono::high_resolution_clock::now();

    Prove();

    std::cout << std::endl;
    const auto end_time_chrono = std::chrono::high_resolution_clock::now();
    const auto duration_chrono = std::chrono::duration_cast<std::chrono::nanoseconds>( end_time_chrono - start_time_chrono ).count();
    std::cout << "Total Duration (nanoseconds): " << duration_chrono << std::endl;

    __stdtraceout__("Main");
    //std::string Hold_for_user_input{};
    //std::cin >> Hold_for_user_input;

    return EXIT_SUCCESS;
}
