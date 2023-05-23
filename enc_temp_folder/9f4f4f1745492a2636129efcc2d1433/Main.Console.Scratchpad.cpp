#include <iostream>
#include <string>
#include <chrono>
#include <Euclid.h>
//#include <Euclid.TestCase.246.h>
//#include <Euclid.16.Boost.Support.No.Strings.h>

int main()
{
	using EuclidProverClass =

		Euclid_Prover::EuclidProver<
		Euclid_Prover::BracketType::CurlyBraces>;

	EuclidProverClass Euclid;

	Euclid.Axioms
	(
		{
			// Axiom_00
			{
				{ "1", "+", "1" },  // lhs
				{ "2" } // rhs
			},

			// Axiom_01
		   {
				{ "2", "+", "2" }, // lhs
				{ "4" } // rhs
			}
		}
	);

	Euclid.Prove
	(
		{
			{ "1", "+", "1", "+", "1", "+", "1" }, // lhs
			{ "4" } // rhs
		}
	);

	const auto start_time_chrono = std::chrono::high_resolution_clock::now();

	std::cout << "Working..." << std::endl;

	while (!Euclid.StatusReady())
	{
		std::this_thread::yield(); // std::this_thread::sleep_for(std::chrono::seconds(1));
	}

	if (Euclid.ProofFoundFlag)
	{
		std::cout << "Proof Found. (QED)" << std::endl;
		Euclid.PrintPath(Euclid.ProofStep3DStdStrVec);
		Euclid.PrintPath(Euclid.AxiomCommitLogStdStrVecRef);
	} else if (Euclid.ProofStep3DStdStrVec.size()) {
		std::cout << "Partial Proof Found." << std::endl;
		Euclid.PrintPath(Euclid.ProofStep3DStdStrVec);
		Euclid.PrintPath(Euclid.AxiomCommitLogStdStrVecRef);
	} else {
		std::cout << "No Proof Found." << std::endl;
	}

    std::cout << std::endl;
    const auto end_time_chrono = std::chrono::high_resolution_clock::now();
    const auto duration_chrono = std::chrono::duration_cast<std::chrono::nanoseconds>( end_time_chrono - start_time_chrono ).count();
    std::cout << "Total Duration (nanoseconds): " << duration_chrono << std::endl;

    std::string Hold_for_user_input{};
    std::cin >> Hold_for_user_input;

    return EXIT_SUCCESS;
}
